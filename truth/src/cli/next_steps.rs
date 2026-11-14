//! `truth next-steps [--frontier-root STATEMENT]`: Python `corpus.py
//! next-steps`, the frontier's `next_steps` projection.

use super::{Accepts, Args, Command, Output, load, validate_first};
use serde_json::json;
use truth::{frontier, navigation};

pub const COMMAND: Command = Command {
    name: "next-steps",
    run,
};

/// Validates first, as Python's `current_frontier` does, then computes the
/// frontier with its next-work projection. `--json` is the projection (Python
/// `next-steps --json`) plus `input_identity`; text is `format_next_steps`,
/// uuids humanized. Python's `--root STATEMENT` is `--frontier-root` here.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    validate_first(&args.root)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let report = frontier::current_frontier(&args.root, &corpus, &frontier_root, false, true);
    let mut steps = report["next_steps"].clone();
    let text = if args.machine {
        String::new()
    } else {
        aliases.humanize(&navigation::format_next_steps(&steps))
    };
    steps["input_identity"] = json!(corpus.input_identity());
    Ok((steps, Some(text)))
}
