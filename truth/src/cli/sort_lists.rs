//! `truth sort-lists`: Python `corpus.py sort-lists`, which sorts the
//! order-free lists `check` requires sorted, in place.

use super::{Accepts, Args, Command, Output};
use serde_json::json;
use truth::{Corpus, navigation};

pub const COMMAND: Command = Command {
    name: "sort-lists",
    run,
};

/// Does not validate first, as in Python. Text is one `sorted FIELD in PATH`
/// line per rewritten record (uuids humanized when the corpus loads);
/// `--json` lists them under `sorted`.
fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    let sorted = navigation::sort_lists(&args.root)
        .map_err(|message| (1, json!({"code": "invalid_input", "message": message})))?;
    let lines: Vec<String> = sorted
        .iter()
        .map(|entry| format!("sorted {} in {}", entry.field, entry.path))
        .collect();
    let text = (!lines.is_empty()).then(|| {
        let text = lines.join("\n");
        match Corpus::load(&args.root) {
            Ok(corpus) => corpus.aliases().humanize(&text),
            Err(_) => text,
        }
    });
    let output = json!({
        "schema_version": 1,
        "sorted": sorted.iter()
            .map(|entry| json!({"path": entry.path, "field": entry.field}))
            .collect::<Vec<_>>(),
    });
    Ok((output, text))
}
