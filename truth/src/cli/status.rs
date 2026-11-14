//! `truth status`: record counts after the structural load.

use super::{Accepts, Args, Command, Output, load};
use serde_json::json;
use std::collections::BTreeMap;

pub const COMMAND: Command = Command {
    name: "status",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    let (corpus, _, _) = load(args)?;
    let counts: BTreeMap<_, _> = corpus.counts().collect();
    let mut lines = vec![format!(
        "Corpus structure ({})",
        json!(corpus.input_identity())
    )];
    for (kind, count) in &counts {
        lines.push(format!("{kind:16} {count}"));
    }
    let output = json!({
        "schema_version": 1,
        "validation": "structural",
        "input_identity": corpus.input_identity(),
        "counts": counts,
    });
    Ok((output, Some(lines.join("\n"))))
}
