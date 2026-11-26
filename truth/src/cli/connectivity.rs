//! `truth connectivity [--frontier-root STATEMENT] [--list-isolated N]`: how
//! the statements connect to the frontier root (a diagnostic for the
//! cohesive-graph goal; counts are not a progress score).

use super::{Accepts, Args, Command, Output, load};
use serde_json::json;
use truth::connectivity;

pub const COMMAND: Command = Command {
    name: "connectivity",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let mut output = connectivity::report(&corpus, &frontier_root, args.list_isolated.unwrap_or(0));
    output["schema_version"] = json!(1);
    output["input_identity"] = json!(corpus.input_identity());
    let text = connectivity::format(&output);
    Ok((output, Some(aliases.humanize(&text))))
}
