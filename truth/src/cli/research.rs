//! What the research navigation commands `related`, `dossier` and `context`
//! share: their option checks, target resolution and the frontier view.

use super::{Args, Failure, HELP, input_error, read_json, usage};
use truth::{Corpus, dossier, frontier, identity::Aliases, thickness};

/// The operand of `command` (`None` only for `dossier --all`) after the
/// checks the three commands share; `applies` is false when a research
/// option outside the command's own was given.
pub fn operand<'a>(
    args: &Args,
    command: &str,
    operands: &[&'a str],
    applies: bool,
) -> Result<Option<&'a str>, Failure> {
    if args.bridge_flags {
        return Err(args.shape_error());
    }
    let target = match operands {
        [] if command == "dossier" && args.research.all => None,
        [id] if !id.is_empty() && !args.research.all => Some(*id),
        _ => return Err(usage(HELP)),
    };
    if !applies
        || args.configuration.flags
        || args.queue
        || args.frontier_flags()
        || args.senses
        || args.group_by.is_some()
    {
        return Err(usage(format!("an option does not apply to {command}")));
    }
    Ok(target)
}

/// The command-line target as the uuid it names, trying `kinds` in order;
/// an unknown token stays as given so the command reports it.
pub fn resolve_target(
    aliases: &Aliases,
    target: Option<&str>,
    kinds: &[&str],
) -> Result<Option<String>, Failure> {
    target
        .map(|token| super::resolve_in(aliases, token, kinds))
        .transpose()
}

/// The frontier view `dossier` and `context` read: from `--frontier-json
/// FILE` (a `corpus.py frontier --json` report) when given, otherwise
/// computed in-process by the Rust frontier on this checkout.
pub fn frontier_view(
    args: &Args,
    corpus: &Corpus,
    frontier_root: &str,
) -> Result<dossier::FrontierView, Failure> {
    let (view, source) = match args.research.frontier.as_deref() {
        Some(path) => {
            let view = dossier::FrontierView::from_report(&read_json(path)?)
                .map_err(|error| input_error(path, error))?;
            if frontier_root != thickness::DEFAULT_ROOT
                && view.root.as_deref() != Some(frontier_root)
            {
                return Err(usage(format!(
                    "--frontier-root {frontier_root} differs from the report root {}",
                    view.root.as_deref().unwrap_or("None")
                )));
            }
            (view, path)
        }
        None => {
            let report =
                frontier::current_frontier(&args.root, corpus, frontier_root, false, false);
            let view = dossier::FrontierView::from_report(&report)
                .map_err(|error| input_error("corpus", error))?;
            (view, "corpus")
        }
    };
    if !view.root_known {
        return Err(input_error(
            source,
            format!(
                "unknown root statement: {}",
                view.root.as_deref().unwrap_or("None")
            ),
        ));
    }
    Ok(view)
}
