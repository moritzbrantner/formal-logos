//! `truth related STATEMENT [--limit N]`: Python `corpus.py related`.

use super::{
    Args, Command, HELP, Output, invalid_target, load, research, unknown, usage, with_identity,
};
use truth::related;

pub const COMMAND: Command = Command {
    name: "related",
    run,
};

/// JSON as the Python command prints it (plus `input_identity`) and
/// byte-identical text.
fn run(args: &Args, operands: &[&str]) -> Output {
    let applies = args.research.frontier.is_none()
        && args.research.related.is_none()
        && !args.frontier_root_set();
    let target = research::operand(args, "related", operands, applies)?;
    let (corpus, aliases, _) = load(args)?;
    let target = research::resolve_target(&aliases, target, &["statements"])?;
    let target = target.ok_or_else(|| usage(HELP))?;
    let limit = args.research.limit.unwrap_or(related::DEFAULT_LIMIT);
    let report = related::related(&corpus, &target, limit).map_err(|error| match error {
        related::LookupError::Unknown(message) => unknown(&message),
        related::LookupError::Invalid(message) => invalid_target(&message),
    })?;
    let text = related::format_related(&report);
    Ok((
        with_identity(&report, &corpus),
        Some(aliases.humanize(&text)),
    ))
}
