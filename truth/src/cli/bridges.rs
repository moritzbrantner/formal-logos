//! `truth bridges`: advisory bridge candidates for target statements.

use super::{
    Accepts, Args, Command, Output, input_error, load, read_json, resolve_statement, usage,
};
use serde_json::{Value, json};
use truth::{bridges, identity::Aliases};

pub const COMMAND: Command = Command {
    name: "bridges",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, true, Accepts::default())?;
    let (corpus, aliases, _) = load(args)?;
    let bridge = &args.bridge;
    let path = bridge
        .constants
        .as_deref()
        .ok_or_else(|| usage("bridges requires --constants FILE"))?;
    let constants =
        bridges::parse_constants(&read_json(path)?).map_err(|error| input_error(path, error))?;
    let mut targets = bridge.targets.clone();
    if let Some(queue) = bridge.queue.as_deref() {
        let ids =
            bridges::parse_queue(&read_json(queue)?).map_err(|error| input_error(queue, error))?;
        targets.extend(ids.into_iter().take(bridge.limit.unwrap_or(10)));
    }
    if targets.is_empty() {
        return Err(usage("bridges requires --queue-file FILE or --target ID"));
    }
    let targets = targets
        .iter()
        .map(|target| resolve_statement(&aliases, target))
        .collect::<Result<Vec<_>, _>>()?;
    let mut report = bridges::report(&corpus, &constants, &targets, bridge.options)
        .map_err(|message| (3, json!({"code":"unknown_id", "message":message})))?;
    for target in report["targets"].as_array_mut().into_iter().flatten() {
        let label = target["statement_id"]
            .as_str()
            .and_then(|id| aliases.label(id));
        target["label"] = json!(label);
    }
    let mut output = json!({
        "schema_version": 1,
        "validation": "structural",
        "input_identity": corpus.input_identity(),
    });
    for (key, value) in report.as_object().into_iter().flatten() {
        output[key] = value.clone();
    }
    let text = aliases.humanize(&text(&output, &aliases));
    Ok((output, Some(text)))
}

/// `bridges` text: ids as `label [uuid8]`.
fn text(output: &Value, aliases: &Aliases) -> String {
    let mut lines = vec![format!(
        "Bridge candidates ({}); advisory ranking only, not a proof",
        output["input_identity"]
    )];
    for target in output["targets"].as_array().into_iter().flatten() {
        lines.push(format!(
            "\n{}",
            aliases.show(target["statement_id"].as_str().unwrap_or_default())
        ));
        if let Some(reason) = target["skipped"].as_str() {
            lines.push(format!("  skipped: {reason}"));
        }
        for arity in ["singles", "pairs", "triples"] {
            for candidate in target[arity].as_array().into_iter().flatten() {
                let ids: Vec<_> = candidate["statement_ids"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .map(|id| aliases.show(id))
                    .collect();
                lines.push(format!(
                    "  {arity:8} {:.3}  {}",
                    candidate["score"].as_f64().unwrap_or(0.0),
                    ids.join(" + ")
                ));
            }
        }
    }
    lines.join("\n")
}
