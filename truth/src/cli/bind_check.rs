//! `truth bind-check [--result ID]... [--affected --base REV [--head REV]]
//! [--lean-json FILE] [--print-lean-input]`: Python `corpus.py bind-check`.
//!
//! Validates first, selects the results (all, `--result` IDs or the results
//! `scripts/affected_results.py` selects for a diff), runs the
//! `scripts/BindTypes.lean` exporter (or reads its saved output) and binds
//! every argument record to its theorem's Lean type. The full run also
//! reports stale pins and, when Lean runs, verifies the registered finite
//! models. Stdout is Python's, byte for byte, in both modes. After running
//! Lean it also records the described types in the elaborated-type cache
//! that `context` reads ([`bind_types`]).

use super::{
    Accepts, Args, Command, Failure, Output, corpus_error, load, raw, read_json, resolve_in,
};
use std::{
    collections::BTreeSet,
    path::Path,
    process::{Command as Process, Stdio},
};
use truth::{
    bind_check::{self, Contracts},
    bind_types,
};

pub const COMMAND: Command = Command {
    name: "bind-check",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        revisions: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    super::validate_first(&args.root)?;
    let (corpus, aliases, _) = load(args)?;
    let known: BTreeSet<String> = corpus
        .records_by_id("results")
        .map(|(id, _)| id.to_owned())
        .collect();
    let scope = scope(args, &aliases, &known)?;
    if let Some(scope) = &scope {
        if scope.is_empty() {
            return Err(raw(
                0,
                "bind-check: no result selected; nothing to check\n".into(),
            ));
        }
        eprintln!(
            "bind-check limited to {} result(s): {}",
            scope.len(),
            scope.iter().cloned().collect::<Vec<_>>().join(", ")
        );
    }
    let contracts = Contracts::load(&args.root).map_err(corpus_error)?;
    let mut requests = bind_check::result_requests(&corpus, scope.as_ref());
    requests.extend(bind_check::schema_requests(&corpus, scope.as_ref()).map_err(corpus_error)?);
    if args.bind.print_input {
        let input = bind_check::tool_input(&corpus, &contracts, &requests);
        return Err(raw(0, input + "\n"));
    }
    let described = match &args.bind.lean_json {
        Some(path) => match read_json(path)? {
            serde_json::Value::Array(items) => items,
            _ => {
                return Err(corpus_error(format!(
                    "{path}: a saved {} output must be a JSON array",
                    bind_check::BIND_TOOL
                )));
            }
        },
        None => {
            let input = bind_check::tool_input(&corpus, &contracts, &requests);
            let described = bind_check::run_tool(&args.root, &input).map_err(corpus_error)?;
            // The elaborated types `context` shows (#960); a saved
            // `--lean-json` output has no provenance and is never cached.
            if let Err(error) = bind_types::write(&args.root, &corpus, &described) {
                eprintln!("bind-check: elaborated-type cache not written: {error}");
            }
            described
        }
    };
    let mut report = bind_check::report(
        &args.root,
        &corpus,
        &contracts,
        &described,
        &requests,
        scope.as_ref(),
    )
    .map_err(corpus_error)?;
    // Registered model checks are global; a scoped run leaves them to the full gate.
    if args.bind.lean_json.is_none() && scope.is_none() {
        report["models"] = bind_check::verify_models(&args.root, &corpus).map_err(corpus_error)?;
    }
    let code = u8::from(bind_check::failed(&report));
    if args.machine {
        let text = serde_json::to_string_pretty(&report).unwrap_or_default();
        Err(raw(code, text + "\n"))
    } else {
        let (text, _) = bind_check::format(&report);
        Err(raw(code, aliases.humanize(&text)))
    }
}

/// Python `bind_check_scope`: all results (`None`), the `--result` IDs, or
/// the results `affected_results.select` picks for the `--affected` diff.
fn scope(
    args: &Args,
    aliases: &truth::identity::Aliases,
    known: &BTreeSet<String>,
) -> Result<Option<BTreeSet<String>>, Failure> {
    let mut selected: Option<BTreeSet<String>> = None;
    if !args.bind.results.is_empty() {
        let requested = args
            .bind
            .results
            .iter()
            .map(|token| resolve_in(aliases, token, &["results"]))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let unknown: Vec<&String> = requested.difference(known).collect();
        if !unknown.is_empty() {
            let unknown: Vec<&str> = unknown.into_iter().map(String::as_str).collect();
            return Err(corpus_error(format!(
                "bind-check: unknown result id(s): {}",
                unknown.join(", ")
            )));
        }
        selected = Some(requested);
    }
    let (base, head) = (&args.frontier.base, &args.frontier.head);
    if args.bind.affected {
        let Some(base) = base else {
            return Err(corpus_error("bind-check --affected needs --base".into()));
        };
        let changed = changed_paths(&args.root, base, head.as_deref())?;
        let (mode, ids) = affected(&args.root, &changed)?;
        if mode == "full" {
            // The full fallback keeps the full run's stale-pin and model checks,
            // even when --result also names results.
            eprintln!("bind-check --affected: the change selects every result");
            return Ok(None);
        }
        let mut scope = selected.unwrap_or_default();
        scope.extend(ids);
        selected = Some(scope);
    } else if base.is_some() || head.is_some() {
        return Err(corpus_error(
            "bind-check: --base and --head need --affected".into(),
        ));
    }
    Ok(selected)
}

/// Python `changed_paths`: paths changed from `base` to `head`, or to the
/// working tree (tracked edits plus untracked, non-ignored files).
fn changed_paths(root: &Path, base: &str, head: Option<&str>) -> Result<Vec<String>, Failure> {
    let git = |arguments: &[&str]| -> Result<Vec<String>, Failure> {
        let output = Process::new("git")
            .args(arguments)
            .current_dir(root)
            .stdin(Stdio::null())
            .output()
            .map_err(|error| {
                corpus_error(format!("cannot resolve the diff against {base}: {error}"))
            })?;
        if !output.status.success() {
            return Err(corpus_error(format!(
                "cannot resolve the diff against {base}: git {} failed: {}",
                arguments.join(" "),
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
        Ok(String::from_utf8_lossy(&output.stdout)
            .split('\0')
            .filter(|path| !path.is_empty())
            .map(str::to_owned)
            .collect())
    };
    if let Some(head) = head {
        return git(&[
            "diff",
            "--name-only",
            "-z",
            "--no-renames",
            base,
            head,
            "--",
        ]);
    }
    let mut paths: BTreeSet<String> =
        git(&["diff", "--name-only", "-z", "--no-renames", base, "--"])?
            .into_iter()
            .collect();
    paths.extend(git(&["ls-files", "-z", "--others", "--exclude-standard"])?);
    Ok(paths.into_iter().collect())
}

/// `affected_results.select(root, changed)`, which stays Python: the mode
/// (`full` or `subset`) and the selected result IDs.
fn affected(root: &Path, changed: &[String]) -> Result<(String, Vec<String>), Failure> {
    const SELECT: &str = "import json, sys\n\
        from pathlib import Path\n\
        sys.path.insert(0, sys.argv[1])\n\
        import affected_results\n\
        mode, ids = affected_results.select(Path(sys.argv[2]), json.load(sys.stdin))\n\
        print(json.dumps([mode, ids]))\n";
    let root = std::fs::canonicalize(root)
        .map_err(|error| corpus_error(format!("cannot resolve {}: {error}", root.display())))?;
    let scripts = root.join("scripts");
    let mut child = Process::new("python3")
        .arg("-c")
        .arg(SELECT)
        .arg(&scripts)
        .arg(&root)
        .current_dir(&root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|error| {
            corpus_error(format!("cannot run scripts/affected_results.py: {error}"))
        })?;
    if let Some(mut stdin) = child.stdin.take() {
        use std::io::Write;
        let input = serde_json::to_vec(changed).unwrap_or_default();
        stdin.write_all(&input).map_err(|error| {
            corpus_error(format!("cannot run scripts/affected_results.py: {error}"))
        })?;
    }
    let output = child.wait_with_output().map_err(|error| {
        corpus_error(format!("cannot run scripts/affected_results.py: {error}"))
    })?;
    if !output.status.success() {
        return Err(corpus_error(
            "scripts/affected_results.py could not select the affected results".into(),
        ));
    }
    serde_json::from_slice::<(String, Vec<String>)>(&output.stdout).map_err(|error| {
        corpus_error(format!(
            "scripts/affected_results.py printed invalid output: {error}"
        ))
    })
}
