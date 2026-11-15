//! `truth lean-reuse --review [--usage-json FILE]`: Python `corpus.py
//! lean-reuse` (#959), a read-only review of result theorems referenced by
//! proof terms against Solution imports and the argument graph.
//!
//! Runs `scripts/LeanReuse.lean` on every result theorem (or reads its
//! saved output). Text is Python's byte for byte; `--json` prints Python's
//! report plus `input_identity`. Advisory: no records change.

use super::{Accepts, Args, Command, Failure, Output, corpus_error, load, with_identity};
use serde_json::Value;
use truth::{Corpus, bind_check, lean_reuse};

pub const COMMAND: Command = Command {
    name: "lean-reuse",
    run,
};

/// The exporter rows: from `saved` (Python `read_lean_reuse_json`) or by
/// running `scripts/LeanReuse.lean` on the theorems `inspect` names (all
/// when `None`).
pub fn exporter_rows(
    root: &std::path::Path,
    corpus: &Corpus,
    saved: Option<&str>,
    inspect: Option<&[String]>,
) -> Result<Vec<Value>, Failure> {
    let value = match saved {
        Some(path) => {
            let bytes = std::fs::read(path).map_err(|error| {
                corpus_error(format!("cannot read Lean reuse output {path}: {error}"))
            })?;
            serde_json::from_slice(&bytes).map_err(|error| {
                corpus_error(format!("cannot read Lean reuse output {path}: {error}"))
            })?
        }
        None => {
            let input = lean_reuse::tool_input(corpus, inspect);
            Value::Array(
                bind_check::run_exporter(root, lean_reuse::TOOL, &input, lean_reuse::COMMAND)
                    .map_err(corpus_error)?,
            )
        }
    };
    lean_reuse::rows(value).map_err(corpus_error)
}

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    args.proof
        .only("lean-reuse", &["--review", "--usage-json"])?;
    if !args.proof.review {
        return Err(corpus_error(
            "lean-reuse is review-only; pass --review".into(),
        ));
    }
    let (corpus, aliases, _) = load(args)?;
    let rows = exporter_rows(&args.root, &corpus, args.proof.usage_json.as_deref(), None)?;
    let expected: Vec<String> = corpus
        .records("results")
        .iter()
        .filter_map(|record| record.get("theorem").and_then(Value::as_str))
        .map(str::to_owned)
        .collect();
    let uses = lean_reuse::usage_map(&rows, &expected).map_err(corpus_error)?;
    let report = lean_reuse::review(&args.root, &corpus, &uses);
    let text = aliases.humanize(&lean_reuse::format_review(&report));
    Ok((
        with_identity(&report, &corpus),
        Some(text.strip_suffix('\n').unwrap_or(&text).to_owned()),
    ))
}
