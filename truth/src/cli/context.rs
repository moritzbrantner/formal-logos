//! `truth context TARGET`: Python `corpus.py context`, the bounded pack for
//! an argument or result. `--proof-use` runs `scripts/LeanReuse.lean` on
//! the argument's result theorems (`--proof-use-json FILE` reads a saved
//! output) and classifies their proof-term references, review only.

use super::{
    Args, Command, Output, corpus_error, invalid_target, lean_reuse, load, research, unknown,
    with_identity,
};
use serde_json::Value;
use truth::{context, lean_reuse as reuse, related};

pub const COMMAND: Command = Command {
    name: "context",
    run,
};

/// JSON as the Python command prints it (plus `input_identity`) and
/// byte-identical text.
fn run(args: &Args, operands: &[&str]) -> Output {
    let target = research::operand(args, "context", operands, true)?;
    args.proof
        .only("context", &["--proof-use", "--proof-use-json"])?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let kinds = &["arguments", "results", "statements"];
    let target = research::resolve_target(&aliases, target, kinds)?.unwrap_or_default();
    let argument = context::resolve_target(&corpus, &target).map_err(|error| match error {
        context::TargetError::Unknown(message) => unknown(&message),
        context::TargetError::Ambiguous(message) => invalid_target(&message),
    })?;
    let view = research::frontier_view(args, &corpus, &frontier_root)?;
    let count = args.research.related.unwrap_or(context::DEFAULT_RELATED);
    let mut matches = Vec::new();
    if count != 0 {
        let conclusion = corpus
            .get("arguments", &argument)
            .and_then(|record| record.fields.get("conclusion_statement_id"))
            .and_then(Value::as_str)
            .unwrap_or_default();
        match related::related(&corpus, conclusion, count) {
            Ok(report) => matches = report.matches,
            Err(error) => eprintln!("context: related ranking unavailable: {}", error.message()),
        }
    }
    let proof = &args.proof;
    let proof_uses = if proof.proof_use || proof.proof_use_json.is_some() {
        let expected: Vec<String> = corpus
            .records("results")
            .iter()
            .filter(|result| {
                result.get("argument_id").and_then(Value::as_str) == Some(argument.as_str())
            })
            .filter_map(|result| result.get("theorem").and_then(Value::as_str))
            .map(str::to_owned)
            .collect();
        let rows = lean_reuse::exporter_rows(
            &args.root,
            &corpus,
            proof.proof_use_json.as_deref(),
            Some(&expected),
        )?;
        Some(reuse::usage_map(&rows, &expected).map_err(corpus_error)?)
    } else {
        None
    };
    let pack = context::context_pack(
        &args.root,
        &corpus,
        &view,
        &argument,
        &matches,
        proof_uses.as_ref(),
    );
    let limit = args.research.limit.unwrap_or(context::DEFAULT_LIMIT);
    let text = context::format_context(&pack, limit);
    Ok((with_identity(&pack, &corpus), Some(aliases.humanize(&text))))
}
