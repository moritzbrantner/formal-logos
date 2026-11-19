//! `truth prove-sweep [--theorem NAME]... [--module MODULE]... [--heartbeats N]
//! [--batch N]`: the cheap proof-discovery sweep over the frozen Challenge
//! theorems (docs/prove-sweep.md, [`truth::prove_sweep`]). Advisory: it
//! writes nothing, and a failure is `unresolved`, never a refutation.

use super::{Accepts, Args, Command, Output, input_error, usage};
use serde_json::json;
use std::time::Instant;
use truth::prove_sweep::{self, Options, PORTFOLIO};

pub const COMMAND: Command = Command {
    name: "prove-sweep",
    run,
};

/// Default `maxHeartbeats` per attempt: a tenth of Lean's default.
const HEARTBEATS: usize = 20_000;
/// Default Challenges per Lean run.
const BATCH: usize = 40;

fn run(args: &Args, operands: &[&str]) -> Output {
    args.simple(operands, 0, false, Accepts::default())?;
    let started = Instant::now();
    let mut challenges =
        prove_sweep::discover(&args.root).map_err(|message| input_error("TruthCore", message))?;
    let modules = &args.modules;
    let theorems = &args.sweep.theorems;
    challenges.retain(|c| prove_sweep::selected(&c.module, modules, true));
    for challenge in &mut challenges {
        challenge
            .targets
            .retain(|t| prove_sweep::selected(&t.theorem, theorems, false));
    }
    challenges.retain(|c| !c.targets.is_empty());
    if challenges.is_empty() {
        return Err(usage("no Challenge theorem matches the filters"));
    }
    let options = Options {
        heartbeats: args.sweep.heartbeats.unwrap_or(HEARTBEATS) as u64,
        batch: args.sweep.batch.unwrap_or(BATCH),
    };
    let targets: usize = challenges.iter().map(|c| c.targets.len()).sum();
    eprintln!(
        "prove-sweep: {targets} targets in {} Challenges, {} tactics each",
        challenges.len(),
        PORTFOLIO.len()
    );
    let refs: Vec<&prove_sweep::Challenge> = challenges.iter().collect();
    let build = prove_sweep::build_imports(&args.root, &refs).err();
    if let Some(message) = &build {
        eprintln!("prove-sweep: {message}");
    }
    let outcomes = prove_sweep::sweep(&args.root, &challenges, &options, &mut |done, total| {
        eprintln!(
            "prove-sweep: run {done}/{total} ({}s)",
            started.elapsed().as_secs()
        );
    });
    let seconds = started.elapsed().as_secs();
    let mut summary = prove_sweep::summary(&outcomes);
    summary["seconds"] = json!(seconds);
    let value = json!({
        "portfolio": PORTFOLIO.iter().map(|(label, tactic)| json!({"label": label, "tactic": tactic})).collect::<Vec<_>>(),
        "heartbeats": options.heartbeats,
        "build_error": build,
        "summary": summary,
        "targets": outcomes.iter().map(prove_sweep::Outcome::to_json).collect::<Vec<_>>(),
    });
    let mut lines = Vec::new();
    for outcome in &outcomes {
        let mut line = match outcome.status {
            "closed" => format!(
                "closed by {}: {}",
                outcome.closed_by.as_deref().unwrap_or_default(),
                outcome.theorem
            ),
            "error" => format!(
                "error: {}: {}",
                outcome.theorem,
                outcome.message.as_deref().unwrap_or_default()
            ),
            status => format!("{status}: {}", outcome.theorem),
        };
        if let Some(how) = &outcome.transcription {
            line.push_str(&format!(" [likely transcription: {how}]"));
        }
        lines.push(line);
    }
    let closed_by: Vec<String> = summary["closed_by"]
        .as_object()
        .into_iter()
        .flatten()
        .filter(|(_, n)| n.as_u64() != Some(0))
        .map(|(label, n)| format!("{label} {n}"))
        .collect();
    lines.push(String::new());
    lines.push(format!(
        "{} targets: {} closed ({}), {} unresolved, {} errors; {} likely transcriptions; {seconds}s",
        summary["targets"],
        summary["closed"],
        if closed_by.is_empty() {
            "none".to_owned()
        } else {
            closed_by.join(", ")
        },
        summary["unresolved"],
        summary["error"],
        summary["likely_transcriptions"],
    ));
    lines.push(
        "Advisory: a closed goal still needs a Solution, Comparator and the usual gates; \
         unresolved is not a refutation."
            .to_owned(),
    );
    Ok((value, Some(lines.join("\n"))))
}
