//! `truth unused-premises [--strict] [--exemptions FILE] [--frontier-root
//! STATEMENT] [--bind-json FILE] [--usage-json FILE]`: Python `corpus.py
//! unused-premises` (#571).
//!
//! Validates first, binds every result with the `scripts/BindTypes.lean`
//! exporter (or reads a saved `bind-check --json` report), runs
//! `scripts/UnusedPremises.lean` on the same input (or reads its saved
//! output), and reports each bound premise whose hypothesis the proof term
//! never uses. Python's `--root STATEMENT` is `--frontier-root` here. Stdout
//! is Python's byte for byte; `--strict` exits 1 on an unexempted finding or
//! a stale exemption.

use super::{Accepts, Args, Command, Failure, Output, corpus_error, load, raw};
use serde_json::Value;
use std::{collections::HashSet, path::Path};
use truth::{
    bind_check::{self, Contracts},
    frontier, unused_premises,
};

pub const COMMAND: Command = Command {
    name: "unused-premises",
    run,
};

/// A saved JSON input, read as Python's `json.loads(Path(…).read_text())`.
fn saved(path: &str) -> Result<Value, Failure> {
    let bytes = std::fs::read(path)
        .map_err(|error| corpus_error(format!("cannot read {path}: {error}")))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| corpus_error(format!("{path}: invalid JSON: {error}")))
}

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let proof = &args.proof;
    proof.only(
        "unused-premises",
        &["--strict", "--exemptions", "--bind-json", "--usage-json"],
    )?;
    super::validate_first(&args.root)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let contracts = Contracts::load(&args.root).map_err(corpus_error)?;
    let requests = bind_check::result_requests(&corpus, None);
    let input = bind_check::tool_input_with(&corpus, &contracts, &requests, false);
    let bind_entries = match &proof.bind_json {
        Some(path) => match saved(path)?.get("results") {
            Some(Value::Array(entries)) => entries.clone(),
            _ => {
                return Err(corpus_error(format!(
                    "{path}: a saved `bind-check --json` report needs a `results` list"
                )));
            }
        },
        None => {
            let described = bind_check::run_tool(&args.root, &input).map_err(corpus_error)?;
            bind_check::bind_entries(&corpus, &contracts, &described, &requests)
        }
    };
    let usage = match &proof.usage_json {
        Some(path) => match saved(path)? {
            Value::Array(items) => items,
            _ => {
                return Err(corpus_error(format!(
                    "{path}: a saved {} output must be a JSON array",
                    unused_premises::UNUSED_TOOL
                )));
            }
        },
        None => bind_check::run_exporter(
            &args.root,
            unused_premises::UNUSED_TOOL,
            &input,
            "unused-premises",
        )
        .map_err(corpus_error)?,
    };
    let report = frontier::current_frontier(&args.root, &corpus, &frontier_root, false, false);
    let root_open: HashSet<String> = report["items"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|item| !item["path_to_root"].is_null())
        .filter_map(|item| item["statement_id"].as_str().map(str::to_owned))
        .collect();
    let report = unused_premises::findings(&bind_entries, &usage, &root_open);
    let exemptions = match &proof.exemptions {
        Some(path) => Path::new(path).to_owned(),
        None => args.root.join(unused_premises::EXEMPTIONS),
    };
    let exemptions = unused_premises::load_exemptions(&exemptions).map_err(corpus_error)?;
    let report = unused_premises::apply_exemptions(report, &exemptions);
    let code = u8::from(proof.strict && unused_premises::gate_fails(&report));
    if args.machine {
        let text = serde_json::to_string_pretty(&report).unwrap_or_default();
        Err(raw(code, text + "\n"))
    } else {
        Err(raw(
            code,
            aliases.humanize(&unused_premises::format(&report)),
        ))
    }
}
