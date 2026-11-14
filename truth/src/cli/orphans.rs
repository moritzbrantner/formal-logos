//! `truth orphans [--by module|family] [--senses]`: verified work that does
//! not reach the frontier root.

use super::{Accepts, Args, Command, Output, load};
use serde_json::json;
use truth::orphans;

pub const COMMAND: Command = Command {
    name: "orphans",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        orphans: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let (mut output, text) = if args.senses {
        let report = orphans::sense_report(&args.root, &corpus, &frontier_root);
        let text = orphans::format_senses(&report);
        (report, text)
    } else {
        let by = args.group_by.unwrap_or(orphans::GroupBy::Module);
        let report = orphans::report(&args.root, &corpus, &frontier_root, by);
        let text = orphans::format(&report);
        (report, text)
    };
    output["schema_version"] = json!(1);
    output["input_identity"] = json!(corpus.input_identity());
    Ok((output, Some(aliases.humanize(&text))))
}
