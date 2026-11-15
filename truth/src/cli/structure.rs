//! `truth structure STATEMENT [--unfold DECLARATION]...` and
//! `truth structure-report [--output FILE] [--build-input | --check-input]`:
//! Python `corpus.py structure` and `structure-report`.
//!
//! Both build the project modules with Lake and run the
//! `scripts/PropositionStructure.lean` exporter through `scripts/worker_env.py`,
//! as Python does; `--extractor-json FILE` replays a saved exporter output
//! instead (no Lean). `structure` prints the statement's report as Python's
//! indented JSON (humanized without `--json`); `structure-report` writes the
//! first-slice explorer artifact byte for byte as Python writes it, and
//! `--check-input` validates an artifact's recorded inputs without Lean.

use super::{Accepts, Args, Command, Failure, Output, corpus_error, load, raw, usage};
use serde_json::{Map, Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};
use truth::{
    Corpus, frontier, pyfmt,
    pyjson::Ordered,
    structure::{self, Extractor, Records, os_error},
};

pub const STRUCTURE: Command = Command {
    name: "structure",
    run: |args, operands| on_large_stack(args, operands, run_structure),
};

pub const REPORT: Command = Command {
    name: "structure-report",
    run: |args, operands| on_large_stack(args, operands, run_report),
};

/// Runs `command` on a thread with [`structure::STACK_SIZE`] of stack:
/// exporter trees are as deep as Lean's expressions and every pass over
/// them (parse, clone, print, drop) recurses.
pub(super) fn on_large_stack(
    args: &Args,
    operands: &[&str],
    command: fn(&Args, &[&str]) -> Output,
) -> Output {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(structure::STACK_SIZE)
            .spawn_scoped(scope, || command(args, operands))
            .map_err(|error| corpus_error(error.to_string()))?
            .join()
            .unwrap_or_else(|_| Err(corpus_error("structure command panicked".into())))
    })
}

/// The checkout as Python's resolved `ROOT`, so messages and the written
/// path print as Python prints them.
pub(super) fn checkout(args: &Args) -> Result<PathBuf, Failure> {
    fs::canonicalize(&args.root).map_err(|error| corpus_error(os_error(&error, &args.root)))
}

/// The frontier's `closed_statements` (Python `frontier_report` at the
/// default root).
fn closed(root: &Path, corpus: &Corpus, frontier_root: &str) -> Map<String, Value> {
    match frontier::current_frontier(root, corpus, frontier_root, false, false)
        .get_mut("closed_statements")
        .map(Value::take)
    {
        Some(Value::Object(map)) => map,
        _ => Map::new(),
    }
}

fn saved_extractor(args: &Args) -> Result<Option<String>, Failure> {
    args.structure
        .extractor_json
        .as_deref()
        .map(|path| {
            fs::read_to_string(path)
                .map_err(|error| corpus_error(os_error(&error, Path::new(path))))
        })
        .transpose()
}

fn extractor(saved: &Option<String>) -> Extractor<'_> {
    match saved {
        Some(text) => Extractor::Saved(text),
        None => Extractor::Lean,
    }
}

fn run_structure(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 1, false, Accepts::default())?;
    let options = &args.structure;
    if options.output.is_some() || options.build_input || options.check_input {
        return Err(usage(
            "--output, --build-input and --check-input apply only to structure-report",
        ));
    }
    let root = checkout(args)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let token = operands[0];
    let statement = match aliases.resolve(token, Some(&["statements"])) {
        Ok(id) => id,
        Err(truth::identity::Unresolved::Unknown) => token.to_owned(),
        Err(truth::identity::Unresolved::Ambiguous(candidates)) => {
            return Err(corpus_error(format!(
                "{} names several records: {}; pass a uuid",
                pyfmt::repr_str(token),
                aliases.describe(&candidates)
            )));
        }
    };
    let records = Records::load(&root).map_err(corpus_error)?;
    let closed = closed(&root, &corpus, &frontier_root);
    let saved = saved_extractor(args)?;
    let report = structure::build_reports(
        &root,
        &records,
        &[statement],
        &options.unfold,
        &closed,
        &extractor(&saved),
    )
    .map_err(corpus_error)?;
    let first = match report.get("reports") {
        Some(Ordered::Array(reports)) => reports.first().cloned().unwrap_or(Ordered::Null),
        _ => Ordered::Null,
    };
    let text = first.dumps(Some(2));
    let text = if args.machine {
        text
    } else {
        aliases.humanize(&text)
    };
    Err(raw(0, text + "\n"))
}

fn run_report(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    let options = &args.structure;
    if !options.unfold.is_empty() {
        return Err(usage("--unfold applies only to structure"));
    }
    let root = checkout(args)?;
    let output = root.join(
        options
            .output
            .as_deref()
            .unwrap_or(structure::DEFAULT_OUTPUT),
    );
    let shown = output.display().to_string();
    if options.check_input {
        let text =
            fs::read_to_string(&output).map_err(|error| corpus_error(os_error(&error, &output)))?;
        let artifact = structure::parse(&text).map_err(corpus_error)?;
        structure::check_artifact(&root, &artifact).map_err(corpus_error)?;
        return Ok((
            json!({"schema_version": 1, "output": shown, "inputs_match": true}),
            Some("structure artifact inputs match".into()),
        ));
    }
    let (corpus, _, frontier_root) = load(args)?;
    let records = Records::load(&root).map_err(corpus_error)?;
    let closed = closed(&root, &corpus, &frontier_root);
    let selected = structure::first_slice();
    let mut unfold = records.statement_declarations(&selected);
    unfold.push(structure::REPORT_UNFOLD.to_owned());
    let saved = saved_extractor(args)?;
    let report = structure::build_reports(
        &root,
        &records,
        &selected,
        &unfold,
        &closed,
        &extractor(&saved),
    )
    .map_err(corpus_error)?;
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent).map_err(|error| corpus_error(os_error(&error, parent)))?;
    }
    fs::write(&output, report.dumps(None) + "\n")
        .map_err(|error| corpus_error(os_error(&error, &output)))?;
    Ok((
        json!({"schema_version": 1, "output": shown, "written": true}),
        Some(format!("wrote {shown}")),
    ))
}
