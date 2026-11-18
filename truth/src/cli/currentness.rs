//! `truth currentness [--frontier-root STATEMENT] [--limit N]` (#1751): the
//! read-only currentness view of the open premises reaching a root
//! (`truth::currentness`). It writes nothing and establishes nothing.

use super::{Args, Command, Output, corpus_error, load, usage};
use serde_json::json;
use std::collections::BTreeSet;
use truth::{currentness, frontier, lifecycle, senses};

pub const COMMAND: Command = Command {
    name: "currentness",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    if !operands.is_empty()
        || args.bridge_flags
        || args.configuration.flags
        || args.queue
        || args.frontier_flags()
        || args.senses
        || args.group_by.is_some()
        || args.issues.own()
        || args.issues.issues_from.is_some()
        || args.research.all
        || args.research.related.is_some()
        || args.research.frontier.is_some()
        || args.write
    {
        return Err(usage(
            "currentness takes only --frontier-root STATEMENT and --limit N",
        ));
    }
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
    let allowlist = senses::read_allowlist(&args.root).map_err(corpus_error)?;
    let ids: BTreeSet<String> = report["items"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item["statement_id"].as_str().map(str::to_owned))
        .collect();
    let impacts = lifecycle::impacts(&args.root, &corpus, &ids).map_err(corpus_error)?;
    let mut output = currentness::report(&report, &corpus, &allowlist, &impacts, limit);
    output["input_identity"] = json!(corpus.input_identity());
    let text = aliases.humanize(&currentness::format(&output));
    Ok((output, Some(text)))
}
