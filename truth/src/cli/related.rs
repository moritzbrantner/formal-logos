//! `truth related STATEMENT [--limit N]`: Python `corpus.py related`.

use super::{
    Args, Command, HELP, Output, invalid_target, load, research, unknown, usage, with_identity,
    with_note_mentions,
};
use truth::related;

pub const COMMAND: Command = Command {
    name: "related",
    run,
};

/// JSON as the Python command prints it (plus `input_identity` and, #952,
/// `note_mentions`) and
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
    let mut text = related::format_related(&report);
    let mut value = with_identity(&report, &corpus);
    let shown = usize::try_from(limit).unwrap_or(usize::MAX).max(1);
    with_note_mentions(args, &corpus, &[&target], &mut value, &mut text, shown)?;
    Ok((value, Some(aliases.humanize(&text))))
}
