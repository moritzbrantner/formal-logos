//! `truth bottlenecks [--stage N]... [--min-arguments N] [--min-routes N]
//! [--limit N] [--authored-only-by MODEL] [--frontier-root STATEMENT]` (owner
//! direction, 2026-11-26): the open premises reaching the root where several
//! arguments or routes stop (`truth::bottlenecks`), for choosing which
//! premises get a focused negation-side review. It writes nothing and
//! establishes nothing.

use super::{Accepts, Args, Command, Output, load, usage};
use serde_json::json;
use truth::{bottlenecks, frontier, workers};

pub const COMMAND: Command = Command {
    name: "bottlenecks",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    if !operands.is_empty()
        || args.bridge_flags
        || args.research.all
        || args.research.related.is_some()
        || args.research.frontier.is_some()
    {
        return Err(usage(
            "bottlenecks takes only --stage N, --min-arguments N, --min-routes N, --limit N, \
             --authored-only-by MODEL and --frontier-root STATEMENT",
        ));
    }
    args.check_options(Accepts {
        frontier_root: true,
        ..Accepts::default()
    })?;
    let limit = match args.research.limit {
        None => None,
        Some(limit) if limit > 0 => Some(limit as usize),
        Some(_) => return Err(usage("--limit must be a positive integer")),
    };
    let (corpus, aliases, frontier_root) = load(args)?;
    let report = frontier::current_frontier(&args.root, &corpus, &frontier_root, true, false);
    if report["root_known"] != true {
        return Err(usage(format!("unknown root statement: {frontier_root}")));
    }
    let defaults = bottlenecks::Filter::default();
    let filter = bottlenecks::Filter {
        stages: args.bottlenecks.stages.iter().copied().collect(),
        min_arguments: args
            .bottlenecks
            .min_arguments
            .unwrap_or(defaults.min_arguments),
        min_routes: args.bottlenecks.min_routes.unwrap_or(defaults.min_routes),
        authored_only_by: args.workers.authored_only_by.clone(),
        limit,
    };
    let label = |id: &str| aliases.label(id).map(str::to_owned);
    let mut output = bottlenecks::report(&report, &label, &workers::authors(&corpus), &filter);
    output["input_identity"] = json!(corpus.input_identity());
    let text = aliases.humanize(&bottlenecks::format(&output));
    Ok((output, Some(text)))
}
