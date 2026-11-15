//! `truth next`: Python `corpus.py next`, the highest-priority source
//! candidate (least `priority`, then `id`).

use super::{Accepts, Args, Command, Output, load, validate_first};
use serde_json::json;
use truth::navigation;

pub const COMMAND: Command = Command { name: "next", run };

/// Validates first, as Python does. Text is the candidate as Python prints
/// it (`json.dumps(candidate, indent=2, ensure_ascii=False)`, keys in file
/// order, uuids humanized); `--json` is the candidate record itself. With no
/// candidates it prints `no candidates` and exits 1, as Python does.
fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    validate_first(&args.root)?;
    let (corpus, aliases, _) = load(args)?;
    match navigation::next_candidate(&args.root, &corpus) {
        Ok(Some((candidate, text))) => Ok((candidate, Some(aliases.humanize(&text)))),
        Ok(None) => Err((
            1,
            json!({"code": "no_candidates", "message": "no candidates", "stdout": true}),
        )),
        Err(message) => Err((1, json!({"code": "read_error", "message": message}))),
    }
}
