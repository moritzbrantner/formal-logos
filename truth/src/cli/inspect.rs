//! `truth inspect ID`: every record an ID, legacy id or label names.

use super::{Accepts, Args, Command, HELP, Output, load, resolve, usage};
use serde_json::json;

pub const COMMAND: Command = Command {
    name: "inspect",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    args.reject_research()?;
    let token = match operands {
        [id] if !id.is_empty() && !args.bridge_flags => *id,
        _ => return Err(usage(HELP)),
    };
    args.check_options(Accepts::default())?;
    let (corpus, aliases, _) = load(args)?;
    let resolved = resolve(&aliases, token, None)?;
    let matches: Vec<_> = resolved
        .iter()
        .flat_map(|id| corpus.inspect(id))
        .map(|(kind, record)| json!({"kind":kind, "path":record.path, "record":record.fields}))
        .collect();
    let Some(id) = resolved.filter(|_| !matches.is_empty()) else {
        return Err((
            3,
            json!({"code":"unknown_id", "message":format!("unknown ID {token}"),
            "id":token, "input_identity":corpus.input_identity()}),
        ));
    };
    let mut lines = vec![format!(
        "{} ({})",
        aliases.show(&id),
        corpus.input_identity()
    )];
    for record in &matches {
        lines.push(format!(
            "{} · {}\n{:#}",
            record["kind"], record["path"], record["record"]
        ));
    }
    let output = json!({
        "schema_version": 1,
        "validation": "structural",
        "input_identity": corpus.input_identity(),
        "id": id,
        "label": aliases.label(&id),
        "matches": matches,
    });
    Ok((output, Some(aliases.humanize(&lines.join("\n")))))
}
