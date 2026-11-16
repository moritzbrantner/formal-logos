//! `truth frontier-diff --base REV [--head REV]`: Python `frontier_delta`.

use super::{Accepts, Args, Command, Output, load, usage};
use serde_json::json;
use truth::frontier;

pub const COMMAND: Command = Command {
    name: "frontier-diff",
    run,
};

/// Python `frontier_delta` between the base revision and the head revision
/// or working tree. A revision is read from its `git archive` extract and
/// judged by this binary's rules (`frontier::base_tree`), so both sides use
/// one rule set and `engines` is always `rust`.
fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        revisions: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let Some(base_revision) = args.frontier.base.as_deref() else {
        return Err(usage("frontier-diff requires --base REV"));
    };
    let (corpus, aliases, frontier_root) = load(args)?;
    let root = &args.root;
    let head_revision = args.frontier.head.as_deref();
    let failed = |message: String| (1, json!({"code": "revision_error", "message": message}));
    let base = frontier::revision_frontier(root, base_revision, &frontier_root).map_err(failed)?;
    let head = match head_revision {
        Some(revision) => {
            frontier::revision_frontier(root, revision, &frontier_root).map_err(failed)?
        }
        None => frontier::current_frontier(root, &corpus, &frontier_root, true, false),
    };
    let mut delta = frontier::frontier_delta(&base, &head);
    delta["base"] = json!(base_revision);
    delta["head"] = json!(head_revision.unwrap_or("working tree"));
    let text = frontier::format_frontier_delta(&delta);
    delta["engines"] = json!({"base": "rust", "head": "rust"});
    delta["input_identity"] = json!(corpus.input_identity());
    Ok((delta, Some(aliases.humanize(&text))))
}
