//! `truth check`: the full corpus validation (Python `corpus.py check`).

use super::{Args, Command, Output, usage};
use serde_json::json;

pub const COMMAND: Command = Command { name: "check", run };

/// Python's `corpus ok: …` line and warnings, or its first error.
fn run(args: &Args, operands: &[&str]) -> Output {
    if !operands.is_empty() {
        return Err(args.shape_error());
    }
    if args.bridge_flags
        || args.research.flags
        || args.queue
        || args.senses
        || args.group_by.is_some()
        || args.frontier_root_set()
        || args.issues.own()
        || args.issues.issues_from.is_some()
    {
        return Err(usage("check takes no options besides --root and --json"));
    }
    match truth::check::check(&args.root) {
        Ok(outcome) => {
            let summary = outcome.summary();
            let text: Vec<String> = outcome
                .warnings
                .iter()
                .map(|warning| format!("warning: {warning}"))
                .collect();
            Ok((
                json!({
                    "schema_version": 1,
                    "ok": true,
                    "counts": outcome.counts.iter().map(|(k, v)| (k.to_string(), json!(v))).collect::<serde_json::Map<_, _>>(),
                    "warnings": outcome.warnings,
                    "summary": summary,
                }),
                // `main` prints the part between the NULs to stderr.
                Some(format!("\u{0}{}\u{0}{summary}", text.join("\n"))),
            ))
        }
        Err(message) => Err((1, json!({"code": "corpus_error", "message": message}))),
    }
}
