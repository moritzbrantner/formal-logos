//! `truth issues --from FILE [--for ID]`: Python `corpus.py issues`, the
//! read-only reconciliation of issue acceptance blocks (#949) against this
//! checkout. It reads one offline `gh issue list --json
//! number,title,body,url,comments` snapshot and never calls GitHub.

use super::{Accepts, Args, Command, Failure, Output, load, resolve_in, usage, with_identity};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use truth::{Corpus, frontier, issues, thickness};

pub const COMMAND: Command = Command {
    name: "issues",
    run,
};

/// A snapshot or acceptance error, reported as Python's `CorpusError`.
pub fn corpus_error(message: String) -> Failure {
    (2, json!({"code": "corpus_error", "message": message}))
}

/// The snapshot at `path` reconciled against `corpus` with `closed`, the
/// frontier closure map.
pub fn report(
    args: &Args,
    issues_snapshot: Vec<serde_json::Map<String, Value>>,
    corpus: &Corpus,
    closed: &BTreeMap<String, String>,
) -> Result<issues::Report, Failure> {
    issues::analyze(&issues_snapshot, corpus, closed, Some(&args.root)).map_err(corpus_error)
}

/// JSON as the Python command prints it (plus `input_identity`) and
/// byte-identical text.
fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(
        operands,
        0,
        false,
        Accepts {
            issues: true,
            ..Accepts::default()
        },
    )?;
    let path = args
        .issues
        .from
        .as_deref()
        .filter(|path| !path.is_empty())
        .ok_or_else(|| {
            usage(
                "issues requires --from FILE, an offline snapshot written by `gh issue list --state open \
                 --limit 1000 --json number,title,body,url,comments`; truth never calls GitHub",
            )
        })?;
    let snapshot = issues::read_snapshot(path).map_err(corpus_error)?;
    let (corpus, aliases, _) = load(args)?;
    let selected = match args.issues.for_id.as_deref().filter(|id| !id.is_empty()) {
        Some(token) => Some(resolve_in(
            &aliases,
            token,
            &[
                "results",
                "statements",
                "configurations",
                "attempts",
                "arguments",
            ],
        )?),
        None => None,
    };
    let frontier =
        frontier::current_frontier(&args.root, &corpus, thickness::DEFAULT_ROOT, false, false);
    let closed: BTreeMap<String, String> = frontier["closed_statements"]
        .as_object()
        .into_iter()
        .flatten()
        .map(|(id, reason)| (id.clone(), reason.as_str().unwrap_or_default().to_owned()))
        .collect();
    let mut report = report(args, snapshot, &corpus, &closed)?;
    if let Some(id) = selected {
        report.select(&id);
    }
    let text = issues::format_report(&report);
    Ok((
        with_identity(&report, &corpus),
        Some(aliases.humanize(&text)),
    ))
}
