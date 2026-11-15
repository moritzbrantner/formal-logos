//! `truth dossier (STATEMENT | --all)`: Python `corpus.py dossier`.

use super::{
    Args, Command, HELP, Output, issues, load, research, unknown, usage, with_identity,
    with_note_mentions,
};
use serde_json::{Value, json};
use truth::dossier;

pub const COMMAND: Command = Command {
    name: "dossier",
    run,
};

/// JSON as the Python command prints it, plus `input_identity` and (#952)
/// `note_mentions`, and Python's text plus a final notes block; `--all` is
/// machine output printed exactly as Python's.
fn run(args: &Args, operands: &[&str]) -> Output {
    let applies = args.research.related.is_none();
    let target = research::operand(args, "dossier", operands, applies)?;
    let (corpus, aliases, frontier_root) = load(args)?;
    let target = research::resolve_target(&aliases, target, &["statements"])?;
    let index = dossier::DossierIndex::new(&corpus);
    if let Some(id) = target.as_deref()
        && corpus.get("statements", id).is_none()
    {
        return Err(unknown(&format!("unknown statement: {id}")));
    }
    let view = research::frontier_view(args, &corpus, &frontier_root)?;
    let targets = match args
        .issues
        .issues_from
        .as_deref()
        .filter(|path| !path.is_empty())
    {
        Some(path) => {
            let snapshot = truth::issues::read_snapshot(path).map_err(issues::corpus_error)?;
            Some(issues::report(
                args,
                snapshot,
                &corpus,
                &view.closed_statements,
            )?)
        }
        None => None,
    };
    let statuses = targets.as_ref().map(truth::issues::Report::statuses);
    let with_targets = |mut found: dossier::Dossier| {
        if let (Some(report), Some(statuses)) = (&targets, &statuses) {
            let id = found
                .statement
                .get("id")
                .and_then(Value::as_str)
                .unwrap_or_default();
            found.targeting_issues = Some(
                report
                    .issues_for_id(id)
                    .into_iter()
                    .map(|number| dossier::IssueTarget {
                        number,
                        status: statuses[&number],
                    })
                    .collect(),
            );
        }
        found
    };
    if args.research.all {
        let all: serde_json::Map<String, Value> = index
            .statement_ids()
            .into_iter()
            .filter_map(|id| {
                index
                    .dossier(id, &view)
                    .map(|d| (id.to_owned(), json!(with_targets(d))))
            })
            .collect();
        let text = Value::Object(all.clone()).to_string();
        return Ok((Value::Object(all), Some(text)));
    }
    let id = target.ok_or_else(|| usage(HELP))?;
    let found = index
        .dossier(&id, &view)
        .map(with_targets)
        .ok_or_else(|| unknown(&format!("unknown statement: {id}")))?;
    let limit = args
        .research
        .limit
        .unwrap_or(dossier::DEFAULT_LIMIT)
        .try_into()
        .ok()
        .filter(|limit: &usize| *limit > 0);
    let mut text = dossier::format_dossier(&found, &index, limit);
    let mut value = with_identity(&found, &corpus);
    let shown = limit.unwrap_or(usize::MAX);
    with_note_mentions(args, &corpus, &[&id], &mut value, &mut text, shown)?;
    Ok((value, Some(aliases.humanize(&text))))
}
