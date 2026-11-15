//! `truth attribution-check --base REV [--materialize] [--max-chars N]`:
//! Python `corpus.py attribution-check` (#989, #954 slice B5).
//!
//! The working tree is the head. The text is Python's byte for byte: the
//! report on stdout (records named `label [uuid8]`), the failed problems on stderr with exit code 1, and an
//! `attribution-check error: …` on stderr with exit code 2. `--json` prints
//! the report (`base`, `claims`, `problems`, `ok`) on stdout with the same
//! exit code. Offline unless `--materialize`, which runs `python3
//! scripts/source_evidence.py materialize PASSAGE` for each selected passage.

use super::{Accepts, Args, Command, Output, load, raw, raw_with_stderr, usage};
use serde_json::json;
use truth::attribution;

pub const COMMAND: Command = Command {
    name: "attribution-check",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        base: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    let Some(base) = args.frontier.base.as_deref() else {
        return Err(usage("attribution-check requires --base REV"));
    };
    let options = &args.attribution;
    let report = match attribution::report(&args.root, base, options.materialize) {
        Ok(report) => report,
        Err(message) if args.machine => {
            return Err((2, json!({"code": "attribution_error", "message": message})));
        }
        Err(message) => {
            return Err(raw_with_stderr(
                2,
                String::new(),
                format!("attribution-check error: {message}\n"),
            ));
        }
    };
    let code = u8::from(!report.problems.is_empty());
    if args.machine {
        let mut value = serde_json::to_value(&report).unwrap_or_default();
        value["ok"] = json!(report.problems.is_empty());
        return Err(raw(code, format!("{value}\n")));
    }
    // `corpus.py` names records in its text output as `label [uuid8]`.
    let (_, aliases, _) = load(args)?;
    let text = attribution::format(&report, options.max_chars.unwrap_or(6000));
    Err(raw_with_stderr(
        code,
        aliases.humanize(&text) + "\n",
        attribution::format_problems(&report.problems),
    ))
}
