//! `truth context TARGET`: Python `corpus.py context`, the bounded pack for
//! an argument or result.

use super::{Args, Command, Output, invalid_target, load, research, unknown, with_identity};
use serde_json::Value;
use truth::{context, related};

pub const COMMAND: Command = Command {
    name: "context",
    run,
};

/// JSON as the Python command prints it (plus `input_identity`) and
/// byte-identical text.
fn run(args: &Args, operands: &[&str]) -> Output {
    let target = research::operand(args, "context", operands, true)?;
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
    let pack = context::context_pack(&args.root, &corpus, &view, &argument, &matches);
    let limit = args.research.limit.unwrap_or(context::DEFAULT_LIMIT);
    let text = context::format_context(&pack, limit);
    Ok((with_identity(&pack, &corpus), Some(aliases.humanize(&text))))
}
