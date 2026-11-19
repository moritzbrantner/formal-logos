//! `truth countermodel THEOREM [--omit HYP]... [--all] [--size N]
//! [--module MODULE] [--no-check]`: finite omission countermodels for a Lean
//! theorem (docs/countermodels.md), formerly `scripts/countermodel.py`.
//!
//! Lake builds the theorem's module and `scripts/Countermodel.lean` extracts
//! its first-order skeleton (both through `scripts/worker_env.py`); the
//! search and rendering are [`truth::countermodel`]. Exit code 1 when Lean
//! rejects a certificate, 2 when the theorem is unavailable or outside the
//! fragment.

use super::{Accepts, Args, Command, Failure, Output, raw, usage};
use serde_json::json;
use truth::countermodel::{self, Skeleton};

pub const COMMAND: Command = Command {
    name: "countermodel",
    run,
};

fn unavailable(message: String) -> Failure {
    (
        2,
        json!({"code": "unavailable", "message": format!("unsupported or unavailable: {message}")}),
    )
}

fn run(args: &Args, operands: &[&str]) -> Output {
    let research = &args.research;
    if research.limit.is_some() || research.related.is_some() || research.frontier.is_some() {
        return Err(usage(
            "--limit, --related and --frontier-json apply only to related, dossier and context",
        ));
    }
    let [theorem] = operands else {
        return Err(usage(super::HELP));
    };
    if args.bridge_flags {
        return Err(usage(super::HELP));
    }
    args.check_options(Accepts::default())?;
    let options = &args.countermodel;
    let skeleton = countermodel::extract(&args.root, theorem, options.module.as_deref())
        .map_err(unavailable)?;
    let omit = if options.omit.is_empty() {
        None
    } else {
        Some(
            countermodel::resolve_omit(&skeleton, &options.omit)
                .map_err(|message| (2, json!({"code": "usage", "message": message})))?,
        )
    };
    let root = args.root.clone();
    let check = move |skeleton: &Skeleton, snippet: &str| {
        countermodel::lean_check(&root, skeleton, snippet)
    };
    let checker: Option<countermodel::Checker> = (!options.no_check).then_some(&check);
    let reports = countermodel::run(
        &skeleton,
        omit.as_deref(),
        options.size.unwrap_or(2),
        research.all,
        checker,
    )
    .map_err(unavailable)?;
    let value = json!({
        "theorem": theorem,
        "module": skeleton.module,
        "reports": reports.iter().map(countermodel::Report::to_json).collect::<Vec<_>>(),
    });
    let text = reports
        .iter()
        .map(countermodel::Report::to_text)
        .collect::<Vec<_>>()
        .join("\n\n");
    if reports.iter().any(|r| r.status == "lean-rejected") {
        let stdout = if args.machine {
            format!("{value}\n")
        } else {
            format!("{text}\n")
        };
        return Err(raw(1, stdout));
    }
    Ok((value, Some(text)))
}
