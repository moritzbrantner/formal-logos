//! `truth connectivity [--frontier-root STATEMENT] [--list-isolated N]`: how
//! the statements connect to the frontier root (a diagnostic for the
//! cohesive-graph goal; counts are not a progress score).
//! `truth connectivity --base REV`: the gate on new disconnection since a
//! base revision; it fails (exit 1) when a new statement, or one that left
//! the root component, is outside it without a `connection_plan`.

use super::{Accepts, Args, Command, Output, load, raw, usage};
use serde_json::json;
use truth::connectivity;

pub const COMMAND: Command = Command {
    name: "connectivity",
    run,
};

fn run(args: &Args, operands: &[&str]) -> Output {
    let accepts = Accepts {
        frontier_root: true,
        base: true,
        ..Accepts::default()
    };
    args.simple(operands, 0, false, accepts)?;
    if args.frontier.base.is_some() && args.list_isolated.is_some() {
        return Err(usage("--base and --list-isolated are alternatives"));
    }
    let (corpus, aliases, frontier_root) = load(args)?;
    if let Some(base) = args.frontier.base.as_deref() {
        let mut output = connectivity::revision_gate(&args.root, &corpus, base, &frontier_root)
            .map_err(|message| (1, json!({"code": "revision_error", "message": message})))?;
        output["schema_version"] = json!(1);
        output["input_identity"] = json!(corpus.input_identity());
        let text = aliases.humanize(&connectivity::format_gate(&output));
        if output["passed"] == true {
            return Ok((output, Some(text)));
        }
        return Err(if args.machine {
            output["code"] = json!("connectivity_gate");
            output["message"] = json!(text);
            (1, output)
        } else {
            raw(1, format!("{text}\n"))
        });
    }
    let mut output = connectivity::report(&corpus, &frontier_root, args.list_isolated.unwrap_or(0));
    output["schema_version"] = json!(1);
    output["input_identity"] = json!(corpus.input_identity());
    let text = connectivity::format(&output);
    Ok((output, Some(aliases.humanize(&text))))
}
