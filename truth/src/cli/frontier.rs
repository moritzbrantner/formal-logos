//! `truth frontier [--reaching-root] [--routes]`: Python `corpus.py frontier`.

use super::{Accepts, Args, Command, Output, load};
use serde_json::json;
use truth::frontier;

pub const COMMAND: Command = Command {
    name: "frontier",
    run,
};

/// JSON as `scripts/corpus.py frontier --json` prints it (plus
/// `input_identity`; `next_steps` only without `--routes`, as in Python), and
/// the same text as the Python command. Only the requested form is computed.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        frontier: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let options = &args.frontier;
    let machine = args.machine;
    let next_steps = machine && !options.routes;
    let report = frontier::current_frontier(
        &args.root,
        &corpus,
        &frontier_root,
        options.reaching_root,
        next_steps,
    );
    let identity = json!(corpus.input_identity());
    let (output, text) = if options.routes {
        let mut routes = report["routes"].clone();
        let text = if machine {
            String::new()
        } else {
            frontier::format_routes(&routes)
        };
        routes["input_identity"] = identity;
        (routes, text)
    } else {
        let text = if machine {
            String::new()
        } else {
            frontier::format_frontier(&report)
        };
        let mut report = report;
        report["input_identity"] = identity;
        (report, text)
    };
    Ok((output, Some(aliases.humanize(&text))))
}
