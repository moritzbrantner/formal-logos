//! `truth workers [--authored-only-by MODEL] [--open] [--frontier-root STATEMENT]`
//! (owner direction, 2026-11-26): for each statement with attempts, the latest
//! attempt's outcome and the models that authored attempts on it
//! (`truth::workers`), so unfinished work by one model can be revisited with
//! another. It writes nothing and establishes nothing.

use super::{Accepts, Args, Command, Output, load, research};
use serde_json::json;
use truth::workers;

pub const COMMAND: Command = Command {
    name: "workers",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(
        operands,
        0,
        false,
        Accepts {
            frontier_root: true,
            ..Accepts::default()
        },
    )?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let view = research::frontier_view(args, &corpus, &frontier_root)?;
    let filter = workers::Filter {
        authored_only_by: args.workers.authored_only_by.clone(),
        open: args.workers.open,
    };
    let mut report = workers::report(
        &corpus,
        &view.closed_statements,
        &view.reaching_root_statements,
        &filter,
    );
    report["frontier_root"] = json!(frontier_root);
    report["input_identity"] = json!(corpus.input_identity());
    let text = aliases.humanize(&workers::format(&report));
    Ok((report, Some(text)))
}
