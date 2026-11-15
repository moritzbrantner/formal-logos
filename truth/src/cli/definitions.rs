//! `truth definitions …`: the formal status of definition records (#1652 L3,
//! `truth/src/definition_status.rs`, docs/corpus-model.md "Formal status of
//! definitions").
//!
//! - `status [--limit N]` — counts by status and Lean kind, the prose
//!   backlog and the findings, from the committed cache (no Lean);
//! - `refresh [--write] [--lean-json FILE] [--print-lean-input]` — run
//!   `scripts/DefinitionStatus.lean` (after `lake build`) or read its saved
//!   output; `--write` rewrites the cache, otherwise it is compared: exit 1
//!   when a fresh committed entry disagrees with Lean, or (strict) when an
//!   entry is stale;
//! - `allowlist [--write]` — the shrink-only prose allowlist;
//! - `ratchet --base REV` — fail when the allowlist grew since REV.

use super::{Accepts, Args, Command, Output, usage};
use serde_json::{Value, json};
use std::{fs, process};
use truth::definition_status::{self as status, State};

pub const COMMAND: Command = Command {
    name: "definitions",
    run,
};

fn error(message: impl Into<String>) -> super::Failure {
    (
        1,
        json!({"code": "definitions_error", "message": message.into()}),
    )
}

fn corpus(args: &Args) -> Result<truth::Corpus, super::Failure> {
    truth::Corpus::load(&args.root).map_err(|e| error(format!("{}: {}", e.path, e.message)))
}

fn run(args: &Args, operands: &[&str]) -> Output {
    let Some((sub, rest)) = operands.split_first() else {
        return Err(usage(
            "definitions requires status, refresh, allowlist or ratchet",
        ));
    };
    args.check_options(Accepts {
        revisions: *sub == "ratchet",
        ..Accepts::default()
    })?;
    if args.frontier.head.is_some() {
        return Err(usage("definitions ratchet takes --base only"));
    }
    if args.write && !matches!(*sub, "refresh" | "allowlist") {
        return Err(usage(
            "--write applies only to definitions refresh and definitions allowlist",
        ));
    }
    if args.bind.flags && (*sub != "refresh" || args.bind.affected || !args.bind.results.is_empty())
    {
        return Err(usage(
            "definitions refresh takes --lean-json and --print-lean-input; the other bind-check options do not apply",
        ));
    }
    if args.research.flags
        && (*sub != "status"
            || args.research.all
            || args.research.related.is_some()
            || args.research.frontier.is_some())
    {
        return Err(usage("--limit applies only to definitions status"));
    }
    match (*sub, rest) {
        ("status", []) => status_command(args),
        ("refresh", []) => refresh(args),
        ("allowlist", []) => allowlist(args),
        ("ratchet", []) => ratchet(args),
        _ => Err(usage(
            "usage: truth definitions (status [--limit N] | refresh [--write] [--lean-json FILE] [--print-lean-input] | allowlist [--write] | ratchet --base REV)",
        )),
    }
}

fn status_command(args: &Args) -> Output {
    let limit = match args.research.limit {
        None => 25,
        Some(n) if n > 0 => n as usize,
        Some(_) => return Err(usage("--limit requires a positive integer")),
    };
    let corpus = corpus(args)?;
    let loaded = status::load(&args.root, &corpus).map_err(error)?;
    let report = status::report(
        &loaded.definitions,
        &loaded.allowlist,
        loaded.strict,
        loaded.cache.is_some(),
    );
    let backlog: Vec<Value> = loaded
        .definitions
        .iter()
        .filter(|d| d.gap.is_none())
        .filter_map(|d| match &d.state {
            State::Computed {
                status,
                reason,
                lean,
            } if status.needs_prose() => Some(json!({
                "id": d.id, "label": d.label, "path": d.path,
                "lean_declaration": d.declaration, "status": status.name(),
                "kind": lean.get("kind"), "reason": reason,
            })),
            _ => None,
        })
        .collect();
    let mut lines = vec![report.summary()];
    lines.push(format!(
        "by Lean kind: {}",
        report
            .by_kind
            .iter()
            .map(|(kind, n)| format!("{kind} {n}"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    lines.push(format!(
        "without formal_gap prose ({} of {}):",
        backlog.len().min(limit),
        backlog.len()
    ));
    for item in backlog.iter().take(limit) {
        lines.push(format!(
            "  {} {} [{}] {} — {}",
            item["status"].as_str().unwrap_or_default(),
            item["kind"].as_str().unwrap_or_default(),
            &item["id"].as_str().unwrap_or_default()
                [..8.min(item["id"].as_str().unwrap_or_default().len())],
            item["lean_declaration"].as_str().unwrap_or_default(),
            item["label"].as_str().unwrap_or_default()
        ));
    }
    for finding in &report.findings {
        lines.push(format!(
            "{}: definitions: {finding}",
            if report.strict { "error" } else { "warning" }
        ));
    }
    Ok((
        json!({
            "schema_version": 1,
            "definitions": report.definitions,
            "by_status": report.by_status,
            "by_kind": report.by_kind,
            "with_prose": report.with_prose,
            "allowlisted_backlog": report.backlog,
            "removable_allowlist_entries": report.removable,
            "strict": report.strict,
            "cache": loaded.cache.is_some(),
            "without_prose": backlog,
            "findings": report.findings,
            "summary": report.summary(),
        }),
        Some(lines.join("\n")),
    ))
}

fn refresh(args: &Args) -> Output {
    let corpus = corpus(args)?;
    let input = status::tool_input(&corpus);
    if args.bind.print_input {
        return Ok((
            serde_json::from_str(&input).unwrap_or(Value::Null),
            Some(input),
        ));
    }
    let described: Vec<Value> = match &args.bind.lean_json {
        Some(path) => {
            let source = fs::read_to_string(path).map_err(|e| error(format!("{path}: {e}")))?;
            match serde_json::from_str(&source) {
                Ok(Value::Array(items)) => items,
                _ => return Err(error(format!("{path}: must hold a JSON array"))),
            }
        }
        None => status::run_tool(&args.root, &input).map_err(error)?,
    };
    let computed = status::build_cache(&args.root, &described).map_err(error)?;
    let committed = status::read_cache(&args.root).map_err(error)?;
    let comparison = status::compare(committed.as_ref(), &computed);
    let strict = status::read_strict(&args.root).map_err(error)?;
    let rendered = status::render_cache(&computed);
    let changed = committed.as_ref().map(status::render_cache) != Some(rendered.clone());
    if args.write && changed {
        fs::write(args.root.join(status::CACHE), &rendered).map_err(|e| error(e.to_string()))?;
    }
    let value = json!({
        "schema_version": 1,
        "declarations": computed.entries.len(),
        "wrong": comparison.wrong,
        "stale": comparison.stale,
        "extra": comparison.extra,
        "changed": changed,
        "written": args.write && changed,
    });
    let mut text = format!(
        "{}: {} declarations from {}; {}",
        status::CACHE,
        computed.entries.len(),
        status::TOOL,
        match (changed, args.write) {
            (false, _) => "unchanged".to_owned(),
            (true, true) => "written".to_owned(),
            (true, false) => format!(
                "{} stale or missing, {} no longer named, {} disagreeing with Lean (`truth definitions refresh --write`)",
                comparison.stale.len(),
                comparison.extra.len(),
                comparison.wrong.len()
            ),
        }
    );
    for declaration in comparison
        .wrong
        .iter()
        .take(if args.write { 0 } else { 20 })
    {
        text.push_str(&format!(
            "\n  disagrees with Lean although its inputs are unchanged: {declaration}"
        ));
    }
    for declaration in comparison
        .stale
        .iter()
        .take(if args.write { 0 } else { 20 })
    {
        text.push_str(&format!("\n  stale or missing: {declaration}"));
    }
    let failed = !args.write && (!comparison.wrong.is_empty() || (strict && changed));
    if failed {
        return Err((
            1,
            json!({"code": "definitions_stale", "message": text, "report": value}),
        ));
    }
    Ok((value, Some(text)))
}

fn allowlist(args: &Args) -> Output {
    let corpus = corpus(args)?;
    let loaded = status::load(&args.root, &corpus).map_err(error)?;
    let existing = status::read_allowlist(&args.root).map_err(error)?;
    let needed = status::needed_allowlist(&loaded.definitions, existing.as_ref());
    let changed = existing.as_ref() != Some(&needed);
    if args.write && changed {
        fs::write(
            args.root.join(status::ALLOWLIST),
            status::render_allowlist(&needed),
        )
        .map_err(|e| error(e.to_string()))?;
    }
    let text = format!(
        "{}: {} definitions{}{}",
        status::ALLOWLIST,
        needed.len(),
        if existing.is_none() {
            " (seeded from the current corpus)"
        } else {
            ""
        },
        match (changed, args.write) {
            (false, _) => "; unchanged",
            (true, true) => "; written",
            (true, false) => "; would change (--write to apply)",
        }
    );
    Ok((
        json!({"schema_version": 1, "definitions": needed.len(), "changed": changed, "written": args.write && changed}),
        Some(text),
    ))
}

fn ratchet(args: &Args) -> Output {
    let Some(base) = args.frontier.base.as_deref() else {
        return Err(usage("definitions ratchet requires --base REV"));
    };
    let head = status::read_allowlist(&args.root)
        .map_err(error)?
        .unwrap_or_default();
    let shown = process::Command::new("git")
        .arg("-C")
        .arg(&args.root)
        .args(["show", &format!("{base}:{}", status::ALLOWLIST)])
        .output()
        .map_err(|e| error(format!("git show: {e}")))?;
    if !shown.status.success() {
        return Ok((
            json!({"schema_version": 1, "ok": true, "grown": []}),
            Some(format!(
                "definitions ratchet: {} is new at {base}; nothing to compare",
                status::ALLOWLIST
            )),
        ));
    }
    let base_list =
        status::parse_allowlist(&String::from_utf8_lossy(&shown.stdout)).map_err(error)?;
    let grown = status::ratchet(&base_list, &head);
    if grown.is_empty() {
        let removed = base_list.len().saturating_sub(head.len());
        return Ok((
            json!({"schema_version": 1, "ok": true, "grown": []}),
            Some(format!(
                "definitions ratchet: ok ({removed} definitions fewer than {base})"
            )),
        ));
    }
    let mut message = format!(
        "{} may only shrink (#1652): give the definition a formal_gap prose meaning instead of allowlisting it",
        status::ALLOWLIST
    );
    for line in &grown {
        message.push_str("\n  ");
        message.push_str(line);
    }
    Err((
        1,
        json!({"code": "definitions_ratchet", "message": message, "grown": grown}),
    ))
}
