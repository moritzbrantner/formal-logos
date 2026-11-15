//! `truth bridge-experiments RESULT --profile-module MODULE [--limit N]`:
//! Python `corpus.py bridge-experiments` (#953, #954 B6), the read-only,
//! profile-scoped cross-argument experiment discovery. Python's
//! `--root STATEMENT` is `--frontier-root` here.

use super::{Accepts, Args, Command, Output, corpus_error, load, resolve_in, usage, with_identity};
use truth::{bridge_experiments, dossier, frontier};

pub const COMMAND: Command = Command {
    name: "bridge-experiments",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let research = &args.research;
    if research.all || research.related.is_some() || research.frontier.is_some() {
        return Err(usage(
            "--all, --related and --frontier-json do not apply to bridge-experiments",
        ));
    }
    let [anchor] = operands else {
        return Err(usage(
            "usage: truth bridge-experiments RESULT --profile-module MODULE [--limit N] [--frontier-root STATEMENT]",
        ));
    };
    if args.bridge_flags {
        return Err(args.shape_error());
    }
    args.check_options(Accepts {
        frontier_root: true,
        ..Accepts::default()
    })?;
    let profile = args
        .profile_module
        .as_deref()
        .ok_or_else(|| usage("bridge-experiments requires --profile-module MODULE"))?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let anchor = resolve_in(&aliases, anchor, &["results"])?;
    let report = frontier::current_frontier(&args.root, &corpus, &frontier_root, false, false);
    let view = dossier::FrontierView::from_report(&report).map_err(corpus_error)?;
    if !view.root_known {
        return Err(corpus_error(format!(
            "unknown root statement: {frontier_root}"
        )));
    }
    let report = bridge_experiments::experiment_report(
        &args.root,
        &corpus,
        &view,
        &anchor,
        profile,
        research.limit.unwrap_or(5),
    )
    .map_err(corpus_error)?;
    let text = aliases.humanize(&bridge_experiments::format_experiments(&report));
    Ok((with_identity(&report, &corpus), Some(text)))
}
