//! `truth type-lints [--base REV]`: advisory metadata lints over the
//! elaborated types `truth bind-check` cached ([`truth::type_lints`]). With
//! `--base`, only relations and statements new or changed since that
//! revision are judged, together with the `tests` relations whose subject
//! result `bind-check --affected` would select for the same diff (its record,
//! Comparator config or Lean inputs changed). It always exits 0: every
//! finding is a warning.

use super::{Accepts, Args, Command, Output, bind_check, corpus_error, load};
use serde_json::json;
use truth::{Corpus, type_lints};

pub const COMMAND: Command = Command {
    name: "type-lints",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        base: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let (corpus, aliases, _) = load(args)?;
    // An unreadable cache leaves every result unchecked (with a note); the
    // command still exits 0.
    let described = type_lints::Described::load(&args.root, &corpus);
    let mut output = match args.frontier.base.as_deref() {
        Some(revision) => {
            let tree = truth::frontier::base_tree(&args.root, revision).map_err(corpus_error)?;
            let base = Corpus::load(tree.path()).map_err(|error| {
                corpus_error(format!(
                    "corpus at {revision} failed: {}: {}",
                    error.path, error.message
                ))
            })?;
            // The results whose certificate may have changed, selected as
            // `bind-check --affected` selects them. If the selection cannot
            // run, every result counts as changed (judging more, never less).
            let affected_results = bind_check::changed_paths(&args.root, revision, None)
                .and_then(|changed| bind_check::affected(&args.root, &changed));
            let affected_results = match affected_results {
                Ok((mode, ids)) => (mode != "full").then(|| ids.into_iter().collect()),
                Err((_, error)) => {
                    eprintln!(
                        "type-lints: cannot select the affected results ({error}); judging the \
                         tests of every result"
                    );
                    None
                }
            };
            let mut output = type_lints::report(
                &corpus,
                &described,
                &type_lints::Scope::Since {
                    base: &base,
                    affected_results,
                },
            );
            output["base"] = json!(revision);
            output
        }
        None => type_lints::report(&corpus, &described, &type_lints::Scope::All),
    };
    output["schema_version"] = json!(1);
    let text = aliases.humanize(&type_lints::format(&output));
    Ok((output, Some(text)))
}
