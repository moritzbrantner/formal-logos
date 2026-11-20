//! `truth discover (--target STATEMENT | --targets open-root|next-tests)...
//! [--module PREFIX]... [--premise-pool closed|proved|all] [--candidates N]
//! [--limit N] [--heartbeats N] [--batch N] [--jobs N] [--zipperposition PATH]
//! [--write-spec PATH]`: Duper search for new implications between corpus
//! propositions (docs/discover.md, [`truth::discover`]). Advisory: it writes
//! no corpus record; `--write-spec` writes a spec draft and a Solution draft.

use super::{Args, Command, Output, input_error, load, resolve_statement, usage};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};
use truth::{
    discover::{self, Finding, Kind, Options, Pool, Statement},
    frontier,
};

pub const COMMAND: Command = Command {
    name: "discover",
    run,
};

/// `YYYY-MM-DD` (UTC) of the current time.
fn today() -> String {
    let days = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs() / 86_400) as i64;
    // Howard Hinnant's civil_from_days.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02}")
}

/// `specs/discover-causality.toml` -> `TruthCore.Results.Discover.DiscoverCausality`.
pub fn batch_module(spec: &Path) -> String {
    let stem = spec.file_stem().and_then(|s| s.to_str()).unwrap_or("Run");
    let camel: String = stem
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|part| !part.is_empty())
        .map(|part| {
            let mut chars = part.chars();
            chars
                .next()
                .map(|c| c.to_ascii_uppercase().to_string() + chars.as_str())
                .unwrap_or_default()
        })
        .collect();
    let camel = if camel
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic())
    {
        camel
    } else {
        format!("Run{camel}")
    };
    format!("TruthCore.Results.Discover.{camel}")
}

fn names(ids: &[String], statements: &BTreeMap<String, Statement>) -> String {
    ids.iter()
        .map(|id| {
            let label = statements.get(id).map_or(id.as_str(), |s| s.label.as_str());
            format!("{label} [{}]", &id[..id.len().min(8)])
        })
        .collect::<Vec<_>>()
        .join("; ")
}

fn run(args: &Args, operands: &[&str]) -> Output {
    if !operands.is_empty() || args.research.related.is_some() || args.research.frontier.is_some() {
        return Err(usage(super::HELP));
    }
    let bridge = &args.bridge;
    if bridge.constants.is_some() || bridge.queue.is_some() || bridge.limit.is_some() {
        return Err(usage(
            "discover takes --target and --targets open-root|next-tests",
        ));
    }
    let given = &args.discover;
    if bridge.targets.is_empty() && given.selectors.is_empty() {
        return Err(usage(
            "discover requires --target STATEMENT or --targets open-root|next-tests",
        ));
    }
    let pool = match &given.pool {
        None => Pool::Closed,
        Some(text) => {
            Pool::parse(text).ok_or_else(|| usage("--premise-pool takes closed, proved or all"))?
        }
    };
    let defaults = Options::default();
    let options = Options {
        bridges: true,
        heartbeats: args
            .sweep
            .heartbeats
            .map_or(defaults.heartbeats, |h| h as u64),
        candidates: given.candidates.unwrap_or(defaults.candidates),
        pool,
        zipperposition: given
            .zipperposition
            .clone()
            .or_else(|| std::env::var("TRUTH_ZIPPERPOSITION").ok())
            .filter(|p| !p.is_empty()),
        jobs: given.jobs.unwrap_or(defaults.jobs),
        batch: args.sweep.batch.unwrap_or(defaults.batch),
        modules: args.modules.clone(),
    };
    if let Some(path) = &options.zipperposition
        && !Path::new(path).is_file()
    {
        return Err(usage(format!("--zipperposition: no executable at {path}")));
    }
    let (corpus, aliases, frontier_root) = load(args)?;
    let report = frontier::current_frontier(&args.root, &corpus, &frontier_root, false, true);
    let mut targets = Vec::new();
    for token in &bridge.targets {
        targets.push(resolve_statement(&aliases, token)?);
    }
    for selector in &given.selectors {
        targets.extend(discover::selected_targets(&report, selector).map_err(usage)?);
    }
    let mut seen = BTreeSet::new();
    targets.retain(|id| seen.insert(id.clone()));
    eprintln!("discover: building Duper and the library");
    discover::build(&args.root).map_err(|message| input_error("lake", message))?;
    // `--limit` caps the targets after the module filter.
    let statements = discover::statements(&corpus);
    if !options.modules.is_empty() {
        targets.retain(|id| {
            statements.get(id).is_none_or(|s| {
                options
                    .modules
                    .iter()
                    .any(|m| s.declaration.starts_with(m.as_str()))
            })
        });
    }
    if let Some(limit) = args.research.limit {
        targets.truncate(usize::try_from(limit).unwrap_or(0));
    }
    let progress = |message: &str| eprintln!("discover: {message}");
    let (outcome, statements, vocabulary) =
        discover::discover(&args.root, &corpus, &report, &targets, &options, &progress)
            .map_err(|message| input_error("discover", message))?;
    let mut spec_written = None;
    if let Some(spec) = &given.write_spec {
        let chosen: Vec<&Finding> = outcome
            .findings
            .iter()
            .filter(|f| f.kind == Kind::Discovery)
            .collect();
        let path = Path::new(spec);
        let batch = batch_module(path);
        let sense_check = discover::SenseCheck::new(&corpus)
            .map_err(|message| input_error("corpus/disambiguations", message))?;
        let spec_text = discover::render_spec(&batch, &chosen, &statements, &sense_check, &today());
        let solution = path.with_extension("Solution.lean");
        let solution_text = discover::render_solution(
            &batch,
            &chosen,
            &statements,
            &vocabulary,
            options.heartbeats,
        );
        fs::write(path, spec_text)
            .and_then(|()| fs::write(&solution, solution_text))
            .map_err(|error| input_error(spec, error.to_string()))?;
        spec_written = Some(
            json!({"spec": spec, "solution": solution.display().to_string(),
                                   "results_module": batch, "arguments": chosen.len()}),
        );
    }
    let count = |kind: Kind| outcome.findings.iter().filter(|f| f.kind == kind).count();
    let mut by_filter: BTreeMap<String, usize> = BTreeMap::new();
    for finding in &outcome.findings {
        let mut seen = BTreeSet::new();
        for (filter, _) in &finding.filters {
            if seen.insert(filter) {
                *by_filter.entry(filter.clone()).or_default() += 1;
            }
        }
    }
    let proved = outcome
        .findings
        .iter()
        .filter(|f| !f.outcome["closed"].is_null() || !f.outcome["alone"].is_null())
        .count();
    let minimized = outcome
        .findings
        .iter()
        .filter(|f| {
            f.outcome["deletions"]
                .as_array()
                .is_some_and(|d| d.iter().any(|e| e["outcome"] == "dropped"))
                || f.outcome["closed"]["used"]
                    .as_array()
                    .is_some_and(|used| used.len() < f.trial.premises.len())
        })
        .count();
    let bridges = discover::rank_bridges(&outcome.findings);
    let summary = json!({
        "targets": targets.len(),
        "missing_bridges": bridges.len(),
        "skipped": outcome.skipped.len(),
        "goals": outcome.trials,
        "proved": proved,
        "minimized": minimized,
        "discoveries": count(Kind::Discovery),
        "incompatibilities": count(Kind::Incompatibility),
        "vocabulary_theorems": count(Kind::VocabularyTheorem),
        "filtered": count(Kind::Filtered),
        "filtered_by": by_filter,
        "unresolved": count(Kind::Unresolved),
        "errors": count(Kind::Error),
        "seconds": outcome.seconds,
    });
    let value = json!({
        "options": {
            "heartbeats": options.heartbeats, "candidates": options.candidates,
            "premise_pool": options.pool.name(), "zipperposition": options.zipperposition,
            "jobs": options.jobs, "batch": options.batch, "modules": options.modules,
        },
        "summary": summary,
        "skipped": outcome.skipped.iter().map(|(id, why)| json!({"statement_id": id, "reason": why})).collect::<Vec<_>>(),
        "findings": outcome.findings.iter().map(|f| discover::finding_json(f, &statements)).collect::<Vec<_>>(),
        "missing_bridges": bridges.iter().map(discover::bridge_json).collect::<Vec<_>>(),
        "spec": spec_written,
        "boundary": "Advisory search. Every reported proof was kernel-checked; a discovery is a conditional support option for review, not a corpus record, and an unresolved target is not a refutation.",
    });
    Ok((
        value.clone(),
        Some(text(&value, &outcome.findings, &bridges, &statements)),
    ))
}

fn text(
    value: &Value,
    findings: &[Finding],
    bridges: &[discover::Bridge],
    statements: &BTreeMap<String, Statement>,
) -> String {
    let mut lines = Vec::new();
    if !bridges.is_empty() {
        lines.push(format!(
            "missing bridges ({}), ranked by targets unlocked; candidate propositions, not premises:",
            bridges.len()
        ));
        for (rank, b) in bridges.iter().enumerate() {
            let targets: Vec<String> = b.targets.iter().cloned().collect();
            lines.push(format!(
                "  {}. {}  [{} -> {}]\n     unlocks {} target(s): {}",
                rank + 1,
                b.text,
                b.from,
                b.to,
                b.targets.len(),
                names(&targets, statements)
            ));
            for qualification in discover::bridge_qualifications(b) {
                lines.push(format!("     only if: {qualification}"));
            }
        }
    }
    for kind in [
        Kind::Discovery,
        Kind::Incompatibility,
        Kind::VocabularyTheorem,
    ] {
        let chosen: Vec<&Finding> = findings.iter().filter(|f| f.kind == kind).collect();
        if chosen.is_empty() {
            continue;
        }
        lines.push(format!("{} ({}):", kind.name(), chosen.len()));
        for f in chosen {
            let target = names(std::slice::from_ref(&f.trial.target), statements);
            lines.push(match kind {
                Kind::Incompatibility => {
                    format!("  jointly inconsistent: {}", names(&f.premises, statements))
                }
                Kind::VocabularyTheorem => format!("  {target} follows from its definitions alone"),
                _ => format!("  {target}\n    from {}", names(&f.premises, statements)),
            });
            for (filter, detail) in &f.filters {
                lines.push(format!("    flag {filter}: {detail}"));
            }
        }
    }
    let filtered: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.kind == Kind::Filtered)
        .collect();
    if !filtered.is_empty() {
        lines.push(format!("filtered ({}):", filtered.len()));
        for f in filtered {
            let reasons: Vec<String> = f.filters.iter().map(|(n, d)| format!("{n}: {d}")).collect();
            lines.push(format!(
                "  {} from {}\n    {}",
                names(std::slice::from_ref(&f.trial.target), statements),
                names(&f.premises, statements),
                reasons.join("; ")
            ));
        }
    }
    let s = &value["summary"];
    lines.push(String::new());
    lines.push(format!(
        "{} targets ({} skipped), {} goals: {} proved, {} minimized; {} discoveries, {} incompatibilities, \
         {} vocabulary theorems, {} filtered {}, {} unresolved, {} errors; {}s",
        s["targets"], s["skipped"], s["goals"], s["proved"], s["minimized"], s["discoveries"],
        s["incompatibilities"], s["vocabulary_theorems"], s["filtered"], s["filtered_by"],
        s["unresolved"], s["errors"], s["seconds"]
    ));
    if let Some(spec) = value["spec"].as_object() {
        lines.push(format!(
            "spec draft: {} and {} ({} arguments)",
            spec["spec"].as_str().unwrap_or_default(),
            spec["solution"].as_str().unwrap_or_default(),
            spec["arguments"]
        ));
    }
    lines.push(
        "Advisory: kernel-checked proofs of conditional implications; review before recording. \
         Unresolved is not a refutation."
            .to_owned(),
    );
    lines.join("\n")
}
