//! `truth arguments` and `truth results`: Python `corpus.py arguments` and
//! `results`, the record IDs one per line in file order.

use super::{Accepts, Args, Command, Output, load, validate_first};
use serde_json::json;
use truth::navigation;

pub const ARGUMENTS: Command = Command {
    name: "arguments",
    run: |args, operands| run(args, operands, "arguments"),
};

pub const RESULTS: Command = Command {
    name: "results",
    run: |args, operands| run(args, operands, "results"),
};

/// Validates first, as Python does. Text is the bare IDs (Python does not
/// humanize ID lists); `--json` lists them under `ids`.
fn run(args: &Args, operands: &[&str], kind: &str) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    validate_first(&args.root)?;
    let (corpus, _, _) = load(args)?;
    let ids = navigation::ids(&corpus, kind);
    let text = (!ids.is_empty()).then(|| ids.join("\n"));
    let output = json!({
        "schema_version": 1,
        "input_identity": corpus.input_identity(),
        "kind": kind,
        "ids": ids,
    });
    Ok((output, text))
}
