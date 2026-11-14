//! `truth dossier (STATEMENT | --all)`: Python `corpus.py dossier`.

use super::{Args, Command, HELP, Output, load, research, unknown, usage, with_identity};
use serde_json::{Value, json};
use truth::dossier;

pub const COMMAND: Command = Command {
    name: "dossier",
    run,
};

/// JSON as the Python command prints it (plus `input_identity`, except
/// `--all`, which is machine output printed as is) and byte-identical text.
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
    if args.research.all {
        let all: serde_json::Map<String, Value> = index
            .statement_ids()
            .into_iter()
            .filter_map(|id| index.dossier(id, &view).map(|d| (id.to_owned(), json!(d))))
            .collect();
        let text = Value::Object(all.clone()).to_string();
        return Ok((Value::Object(all), Some(text)));
    }
    let id = target.ok_or_else(|| usage(HELP))?;
    let found = index
        .dossier(&id, &view)
        .ok_or_else(|| unknown(&format!("unknown statement: {id}")))?;
    let limit = args
        .research
        .limit
        .unwrap_or(dossier::DEFAULT_LIMIT)
        .try_into()
        .ok()
        .filter(|limit: &usize| *limit > 0);
    let text = dossier::format_dossier(&found, &index, limit);
    Ok((
        with_identity(&found, &corpus),
        Some(aliases.humanize(&text)),
    ))
}
