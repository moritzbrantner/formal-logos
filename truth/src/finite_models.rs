//! Registered finite interpretations: Python `scripts/finite_models.py`
//! `model_report` and the text `corpus.py models` prints (#954 slice B2).
//!
//! Registration only: the Lean check of exact evaluations, finite carriers
//! and zero axioms (`verify_models`, which `models --verify`, `--check` and
//! `--argument` run) stays in Python until slice A6.

use crate::configurations::{evaluations, str_of};
use crate::pyfmt::{repr, text};
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet};

type Obj = Map<String, Value>;

pub const SCOPE: &str = "Closed Lean applications in the registered finite vocabulary only; no metaphysical possibility, premise closure or entailment follows from registration.";

/// Python `model_report(models, target, premises)`: unknown evaluations
/// stay unknown; every requested premise must hold. `models` in file order.
pub fn model_report(models: &[&Obj], target: Option<&str>, premises: &[&str]) -> Value {
    let values = |model: &Obj| -> BTreeMap<String, Value> {
        evaluations(model)
            .into_iter()
            .map(|item| {
                (
                    str_of(item, "statement_id").to_owned(),
                    item.get("value").cloned().unwrap_or(Value::Null),
                )
            })
            .collect()
    };
    let premise_set: BTreeSet<&str> = premises.iter().copied().collect();
    let mut sorted = models.to_vec();
    sorted.sort_by_key(|model| str_of(model, "id"));
    let mut entries = Vec::new();
    for model in sorted {
        let values = values(model);
        let target_value = target.and_then(|target| values.get(target));
        if target.is_some() && target_value.is_none() {
            continue;
        }
        let missing: Vec<&str> = premise_set
            .iter()
            .copied()
            .filter(|premise| !values.contains_key(*premise))
            .collect();
        let mut failed: Vec<&str> = premises
            .iter()
            .copied()
            .filter(|premise| values.get(*premise).and_then(Value::as_str) == Some("violates"))
            .collect();
        failed.sort();
        let qualifies = missing.is_empty() && failed.is_empty();
        let classification = if qualifies && target.is_some() {
            if target_value.and_then(Value::as_str) == Some("violates") {
                "counterexample"
            } else {
                "satisfying_interpretation"
            }
        } else {
            "incomplete_or_inapplicable"
        };
        let mut entry = model.clone();
        entry.insert(
            "target_value".into(),
            target_value.cloned().unwrap_or(Value::Null),
        );
        entry.insert("missing_premises".into(), json!(missing));
        entry.insert("violated_premises".into(), json!(failed));
        entry.insert("classification".into(), json!(classification));
        entries.push(Value::Object(entry));
    }
    // Equal, nonempty failure sets across the same complete evaluation
    // coverage; never across vocabularies, never from absent evaluations.
    let vocabularies: BTreeSet<&str> = models
        .iter()
        .map(|model| str_of(model, "vocabulary"))
        .collect();
    let mut patterns = Vec::new();
    for vocabulary in vocabularies {
        let group: Vec<&Obj> = models
            .iter()
            .copied()
            .filter(|model| str_of(model, "vocabulary") == vocabulary)
            .collect();
        let evaluated: BTreeMap<&str, BTreeMap<String, Value>> = group
            .iter()
            .map(|model| (str_of(model, "id"), values(model)))
            .collect();
        let ids: BTreeSet<&str> = evaluated
            .values()
            .flat_map(|v| v.keys().map(String::as_str))
            .collect();
        let ids: Vec<&str> = ids.into_iter().collect();
        let violates = |value: &Value| value.as_str() == Some("violates");
        for (i, a) in ids.iter().enumerate() {
            for b in &ids[i + 1..] {
                if !evaluated
                    .values()
                    .all(|v| v.contains_key(*a) && v.contains_key(*b))
                {
                    continue;
                }
                let failures: Vec<&str> = evaluated
                    .iter()
                    .filter(|(_, v)| violates(&v[*a]))
                    .map(|(mid, _)| *mid)
                    .collect();
                if !failures.is_empty()
                    && evaluated
                        .values()
                        .all(|v| violates(&v[*a]) == violates(&v[*b]))
                {
                    patterns.push(json!({"statement_ids": [a, b], "vocabulary": vocabulary,
                                         "model_ids": evaluated.keys().collect::<Vec<_>>(),
                                         "cofailure_model_ids": failures, "status": "candidate_only"}));
                }
            }
        }
    }
    if let Some(target) = target {
        patterns.retain(|pattern| {
            pattern["statement_ids"]
                .as_array()
                .is_some_and(|ids| ids.iter().any(|id| id == target))
        });
    }
    json!({
        "target": target,
        "premise_statement_ids": premise_set,
        "models": entries,
        "cofailure_candidates": patterns,
        "scope": SCOPE,
    })
}

/// The text `corpus.py models` prints for `report` (without `--verify`).
pub fn format_models(report: &Value) -> String {
    let mut lines = vec![text(&report["scope"])];
    let premises: Vec<String> = report["premise_statement_ids"]
        .as_array()
        .into_iter()
        .flatten()
        .map(text)
        .collect();
    lines.push(format!(
        "Premises: {}",
        if premises.is_empty() {
            "none (empty premise set)".to_owned()
        } else {
            premises.join(", ")
        }
    ));
    let models = report["models"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default();
    for model in models {
        let target = if crate::pyfmt::truthy(Some(&model["target_value"])) {
            text(&model["target_value"])
        } else {
            "registered".to_owned()
        };
        lines.push(format!(
            "{}: {}; {}; vocabulary {}",
            text(&model["id"]),
            target,
            text(&model["classification"]),
            text(&model["vocabulary"])
        ));
        lines.push(format!(
            "  Lean model: {}",
            text(&model["lean_declaration"])
        ));
        for evaluation in model["evaluations"].as_array().into_iter().flatten() {
            lines.push(format!(
                "  {} {}: {}",
                text(&evaluation["value"]),
                text(&evaluation["statement_id"]),
                text(&evaluation["theorem"])
            ));
        }
        if crate::pyfmt::truthy(Some(&model["missing_premises"]))
            || crate::pyfmt::truthy(Some(&model["violated_premises"]))
        {
            lines.push(format!(
                "  unknown premises: {}; violated premises: {}",
                repr(&model["missing_premises"]),
                repr(&model["violated_premises"])
            ));
        }
    }
    if models.is_empty() {
        lines.push(
            "No registered evaluation; no conclusion about derivability or consistency.".into(),
        );
    }
    for pattern in report["cofailure_candidates"]
        .as_array()
        .into_iter()
        .flatten()
    {
        lines.push(format!(
            "Candidate co-failure only: {} in {}; models {}",
            repr(&pattern["statement_ids"]),
            text(&pattern["vocabulary"]),
            repr(&pattern["model_ids"])
        ));
    }
    lines.join("\n")
}
