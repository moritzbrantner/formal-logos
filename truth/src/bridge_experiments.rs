//! Bounded cross-result research experiments, derived from the registered
//! corpus: Python `scripts/bridge_experiments.py` (`corpus.py
//! bridge-experiments`, #953).
//!
//! This is a discovery view, not an entailment checker or a new research
//! registry. An exact Lean Solution import witnesses *reuse*, but never
//! certifies that two results describe the same semantic interpretation.
//! Callers select one concrete profile module, inspect types and keep witness
//! identity fixed. The Lean imports and import closures are the `context`
//! pack's ([`crate::context`]).

use crate::{Corpus, context, dossier::FrontierView, pyfmt};
use serde_json::{Map, Value, json};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

type Record = Map<String, Value>;

const SCOPE_FIELDS: &[&str] = &["semantic_profile_id", "model_profile_id", "witness_id"];
const NEGATIVE_TEST: &str = "Attempt a SAME-PROFILE counterinterpretation satisfying each complete premise bundle while denying the proposed bridge. Compare a positive interpretation, the strongest rival, and an omission control. An absent proof is not a countermodel.";
const QUALIFICATION: &str = "Registered evidence and an exact Solution import only. Inspect theorem types, common interpretation and negative controls; no new entailment or philosophical closure follows.";
const PROFILE_BOUNDARY: &str = "All displayed Solution modules import this exact Lean module. Shared imports do not establish the same semantic instantiation or witness; inspect complete types before combining them. Explicit profile/witness metadata mismatches are excluded.";
const ABSENCE_WARNING: &str = "The absence of a candidate or recorded proof is NOT a refutation. Do not infer a worldview result from this discovery report.";

fn text<'a>(record: &'a Record, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn list<'a>(record: &'a Record, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

fn get(record: &Record, field: &str) -> Value {
    record.get(field).cloned().unwrap_or(Value::Null)
}

/// Python `LEAN_MODULE.fullmatch`: `TruthCore(\.[A-Za-z][A-Za-z0-9_]*)+`.
fn lean_module(module: &str) -> bool {
    let Some(rest) = module.strip_prefix("TruthCore.") else {
        return false;
    };
    rest.split('.').all(|part| {
        let mut chars = part.chars();
        chars.next().is_some_and(|c| c.is_ascii_alphabetic())
            && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
    })
}

/// Python `experiment_report`: *recorded* unresolved joins where one
/// Solution imports another, under one named profile module.
pub fn experiment_report(
    root: &Path,
    corpus: &Corpus,
    frontier: &FrontierView,
    anchor_id: &str,
    profile_module: &str,
    limit: i64,
) -> Result<Value, String> {
    let by_id = |kind| -> HashMap<&str, &Record> {
        corpus
            .records(kind)
            .into_iter()
            .map(|record| (text(record, "id"), record))
            .collect()
    };
    let results = by_id("results");
    let arguments = by_id("arguments");
    let statements = by_id("statements");
    let Some(&anchor) = results.get(anchor_id) else {
        return Err(format!("unknown result: {anchor_id}"));
    };
    let is_file = |module: &str| root.join(context::module_path(module)).is_file();
    if !lean_module(profile_module) || !is_file(profile_module) {
        return Err(format!(
            "unknown or invalid profile module: {profile_module}"
        ));
    }
    if !(1..=20).contains(&limit) {
        return Err("limit must be between 1 and 20".to_owned());
    }
    let lean = context::Lean::new(root);
    let in_profile = |result: &Record| {
        let module = text(result, "solution_module");
        !module.is_empty()
            && is_file(module)
            && (module == profile_module
                || lean
                    .closure(module)
                    .iter()
                    .any(|(name, _)| name == profile_module))
    };
    if !in_profile(anchor) {
        return Err(format!(
            "anchor result {anchor_id} does not import selected profile {profile_module}"
        ));
    }
    // Optional exact metadata is a veto, not a source of inferred identity.
    let scope_compatible = |left: &Record, right: &Record| {
        SCOPE_FIELDS.iter().all(|field| {
            !(left.contains_key(*field) || right.contains_key(*field))
                || left.get(*field) == right.get(*field)
        })
    };
    let direct_edge = |peer: &Record| -> Option<(String, String)> {
        let source = text(peer, "solution_module");
        let target = text(anchor, "solution_module");
        if source.is_empty() || target.is_empty() || source == target {
            return None;
        }
        if lean.imports(target).iter().any(|name| name == source) {
            return Some((anchor_id.to_owned(), text(peer, "id").to_owned()));
        }
        if lean.imports(source).iter().any(|name| name == target) {
            return Some((text(peer, "id").to_owned(), anchor_id.to_owned()));
        }
        None
    };
    let conclusion = |result: &Record| {
        arguments
            .get(text(result, "argument_id"))
            .map_or("", |argument| text(argument, "conclusion_statement_id"))
    };
    let proof_bundle = |result: &Record| {
        let argument = arguments
            .get(text(result, "argument_id"))
            .copied()
            .cloned()
            .unwrap_or_default();
        json!({
            "result_id": get(result, "id"), "argument_id": get(&argument, "id"),
            "theorem": get(result, "theorem"), "recorded_status": get(result, "status"),
            "premise_statement_ids": get(&argument, "premise_statement_ids"),
            "conclusion_statement_id": get(&argument, "conclusion_statement_id"),
        })
    };

    let root_facing = &frontier.reaching_root_statements;
    let closed = &frontier.closed_statements;
    let mut candidates: Vec<(i64, String, Value)> = Vec::new();
    let (mut cross_profile, mut different_witness, mut no_direct_reuse, mut no_question) =
        (0, 0, 0, 0);
    let mut linked_attempts = 0;
    let anchor_conclusion = conclusion(anchor);
    let mut attempts = corpus.records("attempts");
    attempts.sort_by(|a, b| text(a, "id").cmp(text(b, "id")));
    for attempt in attempts {
        let evidence = list(attempt, "evidence");
        if !evidence.contains(&anchor_id) {
            continue;
        }
        linked_attempts += 1;
        if !pyfmt::truthy(attempt.get("blocker")) {
            no_question += 1;
            continue;
        }
        // Both *conclusions* must be the attempt's explicit focus; a mere
        // evidence-list or import overlap is insufficient.
        let focus_set: HashSet<&str> = list(attempt, "statement_ids").into_iter().collect();
        if !focus_set.contains(anchor_conclusion) {
            cross_profile += 1;
            continue;
        }
        let mut eligible: Vec<&Record> = Vec::new();
        let mut edges: Vec<(String, String)> = Vec::new();
        let peers: BTreeSet<&str> = evidence.iter().copied().collect();
        for other_id in peers {
            let Some(&other) = results.get(other_id).filter(|_| other_id != anchor_id) else {
                continue;
            };
            if !focus_set.contains(conclusion(other)) || !in_profile(other) {
                cross_profile += 1;
                continue;
            }
            if !scope_compatible(anchor, other) {
                different_witness += 1;
                continue;
            }
            match direct_edge(other) {
                Some(edge) if text(other, "argument_id") != text(anchor, "argument_id") => {
                    eligible.push(other);
                    edges.push(edge);
                }
                _ => no_direct_reuse += 1,
            }
        }
        if eligible.is_empty() {
            continue;
        }
        let focus: BTreeSet<&str> = focus_set
            .iter()
            .copied()
            .filter(|sid| statements.contains_key(sid))
            .collect();
        let open_focus: Vec<&str> = focus
            .iter()
            .copied()
            .filter(|sid| !closed.contains_key(*sid))
            .collect();
        let on_root: Vec<&str> = open_focus
            .iter()
            .copied()
            .filter(|sid| root_facing.contains(*sid))
            .collect();
        // Names are navigation hints only; they cannot certify negative controls.
        let controls: BTreeSet<&str> = evidence
            .iter()
            .copied()
            .filter(|rid| {
                results.get(rid).is_some_and(|&result| {
                    ["CONTROL", "OMISSION", "COUNTERMODEL"]
                        .iter()
                        .any(|word| rid.contains(word))
                        && in_profile(result)
                        && scope_compatible(anchor, result)
                })
            })
            .collect();
        let blocked = attempt.get("outcome").and_then(Value::as_str) == Some("blocked");
        // Score ranks a *bounded test opportunity*, not philosophical truth.
        let score = 5 * on_root.len().min(3) as i64
            + 4 * i64::from(blocked)
            + 2 * edges.len().min(3) as i64
            + 2 * i64::from(!controls.is_empty())
            + i64::from(!open_focus.is_empty());
        edges.sort();
        let mut bundles: Vec<&Record> = std::iter::once(anchor).chain(eligible).collect();
        bundles.sort_by(|a, b| text(a, "id").cmp(text(b, "id")));
        let attempt_id = text(attempt, "id").to_owned();
        candidates.push((
            score,
            attempt_id.clone(),
            json!({
                "attempt_id": attempt_id, "attempt_outcome": get(attempt, "outcome"),
                "recorded_blocker": get(attempt, "blocker"),
                "focus_statement_ids": focus, "open_focus_statement_ids": open_focus,
                "open_root_facing_statement_ids": on_root,
                "exact_import_edges": edges.iter().map(|(consumer, imported)| json!({
                    "consumer_result_id": consumer, "imported_result_id": imported,
                })).collect::<Vec<_>>(),
                "full_argument_bundles": bundles.into_iter().map(proof_bundle).collect::<Vec<_>>(),
                "control_hint_result_ids": controls,
                "negative_test": NEGATIVE_TEST,
                "priority_score": score,
                "priority_reasons": {"root_facing_open": on_root.len(), "blocked_attempt": blocked,
                                     "direct_reuse_edges": edges.len(),
                                     "named_control_hints": controls.len()},
                "qualification": QUALIFICATION,
            }),
        ));
    }
    candidates.sort_by(|a, b| (-a.0, &a.1).cmp(&(-b.0, &b.1)));
    let eligible = candidates.len();
    let limit = limit as usize;
    Ok(json!({
        "mode": "registered-evidence discovery; NOT a proof or refutation",
        "anchor_result_id": anchor_id, "requested_profile_module": profile_module,
        "profile_boundary": PROFILE_BOUNDARY,
        "summary": {"linked_attempts": linked_attempts, "eligible_experiments": eligible,
                    "excluded_peer_reasons": {"cross_profile": cross_profile,
                                              "different_witness": different_witness,
                                              "no_direct_reuse": no_direct_reuse,
                                              "no_remaining_question": no_question}},
        "experiments": candidates.into_iter().take(limit).map(|(_, _, value)| value).collect::<Vec<_>>(),
        "truncated": eligible.saturating_sub(limit),
        "absence_warning": ABSENCE_WARNING,
    }))
}

/// Python `format_experiments` (before `humanize`).
pub fn format_experiments(report: &Value) -> String {
    let field = |value: &Value, key: &str| value[key].as_str().unwrap_or_default().to_owned();
    let ids = |value: &Value| {
        value
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join(", ")
    };
    let mut lines = vec![
        format!(
            "Cross-argument experiments from {}",
            field(report, "anchor_result_id")
        ),
        format!(
            "Selected profile module: {}",
            field(report, "requested_profile_module")
        ),
        "Discovery only; direct imports are not proof of common instantiation.".to_owned(),
    ];
    let experiments = report["experiments"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    for (i, candidate) in experiments.iter().enumerate() {
        let blocker = pyfmt::text(&candidate["recorded_blocker"]);
        let mut question: String = blocker.chars().take(400).collect();
        if blocker.chars().count() > 400 {
            question.push_str("... (full in --json)");
        }
        let edges = candidate["exact_import_edges"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|edge| {
                format!(
                    "{} imports {}",
                    field(edge, "consumer_result_id"),
                    field(edge, "imported_result_id")
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        let open = ids(&candidate["open_focus_statement_ids"]);
        let controls = ids(&candidate["control_hint_result_ids"]);
        lines.extend([
            format!(
                "\n{}. {} [priority {}; {}]",
                i + 1,
                field(candidate, "attempt_id"),
                candidate["priority_score"],
                pyfmt::text(&candidate["attempt_outcome"])
            ),
            format!("   Open question: {question}"),
            format!("   Exact Solution imports: {edges}"),
            format!(
                "   Open focus statements: {}",
                if open.is_empty() { "none" } else { &open }
            ),
            format!(
                "   Control hints (read the theorems): {}",
                if controls.is_empty() {
                    "none recorded by name"
                } else {
                    &controls
                }
            ),
            "   Use --json for the complete AND-premise bundles, priority and negative-test protocol."
                .to_owned(),
        ]);
    }
    if experiments.is_empty() {
        lines.push(
            "No eligible same-module direct-import experiments found. This is NOT a refutation."
                .to_owned(),
        );
    }
    let truncated = report["truncated"].as_u64().unwrap_or(0);
    if truncated > 0 {
        lines.push(format!(
            "{truncated} additional candidates; increase --limit (maximum 20)."
        ));
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profile_modules_follow_python_lean_module() {
        assert!(lean_module("TruthCore.Semantics.Shared"));
        assert!(lean_module("TruthCore.A_1"));
        for bad in [
            "TruthCore",
            "TruthCore.",
            "TruthCore.1A",
            "TruthCore..A",
            "../../unsafe",
            "TruthCore.A\n",
        ] {
            assert!(!lean_module(bad), "{bad:?}");
        }
    }
}
