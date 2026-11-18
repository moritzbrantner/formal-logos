//! `truth currentness` (#1751 slice 1): a read-only discovery view of which
//! open premises reaching a frontier root carry a recorded, scoped
//! `current_assessment` (docs/premise-dossiers.md), which have only legacy
//! attempts, and which have none.
//!
//! The view establishes nothing. A missing current assessment is *unknown*
//! currentness, not a failure or an unfinished task; the advisory flags are
//! heuristics that point at records to re-read, never verdicts about a
//! premise, an objection or an attempt. Items are grouped by the earliest
//! case stage they reach and ordered by route position (the length of the
//! recorded path to the root); no leaf count or strength score orders them.
use crate::Corpus;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The date of the substantive objection standard (AGENTS.md, owner
/// direction 2026-11-12). An attempt dated earlier was written before it.
pub const OBJECTION_STANDARD_DATE: &str = "2026-11-12";

pub const BOUNDARY: &str = "Discovery view only: currentness states and advisory heuristic flags point at records to re-read. They establish, defeat and close nothing; absence of a current assessment is unknown currentness, not failure.";

/// Old-policy framings in legacy `blocker` text (case-insensitive substring
/// matches). Each names the superseded policy it echoes: rival exhaustion as
/// the only defence route and "does not discriminate" blockers (2026-11-10/12
/// provisional judgments, cumulative warrant), route cost as a progress
/// measure (2026-11-12 breadth), and owner approval as warrant (2026-11-10).
/// A match only says the wording resembles the old framing.
pub const OLD_POLICY_PATTERNS: &[(&str, &[&str])] = &[
    (
        "rival_exhaustion",
        &[
            "does not discriminate against",
            "refute every rival",
            "refutes every rival",
            "refuting every rival",
            "every recorded rival",
            "no rival is refuted",
        ],
    ),
    (
        "route_cost",
        &[
            "route cost",
            "route-cost",
            "one open leaf",
            "one leaf",
            "leaf of every route",
        ],
    ),
    (
        "owner_approval",
        &[
            "owner approv",
            "owner has approved",
            "owner_approval",
            "remain owner decisions",
        ],
    ),
];

/// The names of the [`OLD_POLICY_PATTERNS`] families that `text` matches.
pub fn old_policy_matches(text: &str) -> Vec<&'static str> {
    let lower = text.to_lowercase();
    OLD_POLICY_PATTERNS
        .iter()
        .filter(|(_, patterns)| patterns.iter().any(|p| lower.contains(p)))
        .map(|(name, _)| *name)
        .collect()
}

fn text<'a>(value: &'a Value, key: &str) -> &'a str {
    value[key].as_str().unwrap_or_default()
}

fn strings(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect()
}

/// The report: `frontier` is a `frontier --reaching-root` report for the
/// selected root, `allowlist` the sense-index allowlist and `impacts` the
/// declared revision impacts (`lifecycle::impacts`) for the reported
/// statements. `limit` bounds the listed items, not the summary.
pub fn report(
    frontier: &Value,
    corpus: &Corpus,
    allowlist: &Value,
    impacts: &[Value],
    limit: Option<usize>,
) -> Value {
    let attempts = corpus.entries("attempts");
    let mut by_statement: BTreeMap<&str, Vec<&serde_json::Map<String, Value>>> = BTreeMap::new();
    for attempt in &attempts {
        for id in strings(&attempt.fields["statement_ids"]) {
            by_statement.entry(id).or_default().push(&attempt.fields);
        }
    }
    let allowlisted: BTreeSet<&str> = allowlist["arguments"]
        .as_object()
        .map(|arguments| arguments.keys().map(String::as_str).collect())
        .unwrap_or_default();
    let mut pending: BTreeMap<String, usize> = BTreeMap::new();
    for impact in impacts {
        for consumer in impact["consumers"].as_array().into_iter().flatten() {
            if text(consumer, "disposition") == "pending"
                && let Some(id) = text(consumer, "consumer").strip_prefix("statements:")
            {
                *pending.entry(id.to_owned()).or_default() += 1;
            }
        }
    }

    let mut items = Vec::new();
    for item in frontier["items"].as_array().into_iter().flatten() {
        let id = text(item, "statement_id");
        let stages: Vec<u64> = frontier["statement_stages"][id]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_u64)
            .collect();
        let current = crate::lifecycle::current(corpus, &BTreeSet::from([id.to_owned()]));
        let own = by_statement.get(id).cloned().unwrap_or_default();
        let state = if !current.is_empty() {
            "current"
        } else if !own.is_empty() {
            "legacy_only"
        } else {
            "none"
        };
        let latest_date = own
            .iter()
            .filter_map(|a| a.get("date").and_then(Value::as_str))
            .filter(|d| !d.is_empty())
            .max();

        let mut flags = Vec::new();
        if item["transcription_only"] == true {
            flags.push(json!({"flag": "transcription_only_support"}));
        }
        let consumers: Vec<&str> = strings(&item["dependent_arguments"])
            .into_iter()
            .filter(|argument| allowlisted.contains(argument))
            .collect();
        if !consumers.is_empty() {
            flags.push(
                json!({"flag": "consumer_on_sense_index_allowlist", "argument_ids": consumers}),
            );
        }
        // Alternatives are `{statement_id, refuted}` objects, objections strings:
        // count entries of either shape.
        let count = |key: &str| item[key].as_array().map_or(0, Vec::len);
        let rivals = count("alternatives") + count("objections");
        if rivals > 0 && current.is_empty() {
            flags.push(json!({"flag": "rivals_without_current_assessment",
                "alternatives": item["alternatives"], "objections": item["objections"]}));
        }
        if let Some(date) = latest_date.filter(|d| *d < OBJECTION_STANDARD_DATE) {
            flags.push(json!({"flag": "latest_attempt_predates_objection_standard", "date": date}));
        }
        for attempt in own.iter().filter(|a| !a.contains_key("current_assessment")) {
            let blocker = attempt.get("blocker").and_then(Value::as_str);
            let matched = old_policy_matches(blocker.unwrap_or_default());
            if !matched.is_empty() {
                flags.push(json!({"flag": "legacy_blocker_old_policy_framing",
                    "attempt_id": attempt["id"], "patterns": matched}));
            }
        }
        let latest_current = current.first().map(|c| {
            json!({"attempt_id": c["attempt_id"], "date": c["date"], "review": c["review"],
                "publication": c["publication"], "scope": c["scope"]})
        });
        items.push(json!({
            "statement_id": id,
            "state": state,
            "stage": stages.first(),
            "stages": stages,
            "route_position": item["path_to_root"].as_array().map_or(0, Vec::len),
            "depth": item["depth"],
            "attempt_count": own.len(),
            "latest_attempt_date": latest_date,
            "current_assessment": latest_current,
            "current_assessment_count": current.len(),
            "pending_revision_impacts": pending.get(id).copied().unwrap_or(0),
            "flags": flags,
        }));
    }
    // Earliest stage first (unstaged last), then nearest the root.
    items.sort_by(|a, b| {
        let stage = |v: &Value| v["stage"].as_u64().unwrap_or(u64::MAX);
        stage(a)
            .cmp(&stage(b))
            .then(
                a["route_position"]
                    .as_u64()
                    .cmp(&b["route_position"].as_u64()),
            )
            .then(text(a, "statement_id").cmp(text(b, "statement_id")))
    });

    let mut states = BTreeMap::from([("current", 0), ("legacy_only", 0), ("none", 0)]);
    let mut flag_counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut stage_states: BTreeMap<String, BTreeMap<&str, usize>> = BTreeMap::new();
    for item in &items {
        let state = match text(item, "state") {
            "current" => "current",
            "legacy_only" => "legacy_only",
            _ => "none",
        };
        *states.get_mut(state).unwrap() += 1;
        let stage = item["stage"]
            .as_u64()
            .map_or("unstaged".to_owned(), |s| s.to_string());
        *stage_states
            .entry(stage)
            .or_insert_with(|| BTreeMap::from([("current", 0), ("legacy_only", 0), ("none", 0)]))
            .get_mut(state)
            .unwrap() += 1;
        let names: BTreeSet<&str> = item["flags"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|f| text(f, "flag"))
            .collect();
        for name in names {
            *flag_counts.entry(name.to_owned()).or_default() += 1;
        }
    }
    let total = items.len();
    if let Some(limit) = limit {
        items.truncate(limit);
    }
    json!({
        "schema_version": 1,
        "boundary": BOUNDARY,
        "root": frontier["root"],
        "stages": frontier["stages"],
        "objection_standard_date": OBJECTION_STANDARD_DATE,
        "old_policy_patterns": OLD_POLICY_PATTERNS.iter().map(|(name, patterns)| json!({"name": name, "patterns": patterns})).collect::<Vec<_>>(),
        "summary": {
            "open_premises": total,
            "states": states,
            "by_stage": stage_states,
            "items_with_flag": flag_counts,
        },
        "listed": items.len(),
        "items": items,
    })
}

/// The text view: the boundary, the summary and one block per item.
pub fn format(report: &Value) -> String {
    let summary = &report["summary"];
    let states = &summary["states"];
    let mut lines = vec![
        report["boundary"].as_str().unwrap_or_default().to_owned(),
        format!(
            "Open premises reaching {}: {} — current {}, legacy_only {}, none {}",
            text(report, "root"),
            summary["open_premises"],
            states["current"],
            states["legacy_only"],
            states["none"]
        ),
    ];
    for (stage, counts) in summary["by_stage"].as_object().into_iter().flatten() {
        lines.push(format!(
            "  stage {stage}: current {}, legacy_only {}, none {}",
            counts["current"], counts["legacy_only"], counts["none"]
        ));
    }
    if let Some(flags) = summary["items_with_flag"]
        .as_object()
        .filter(|f| !f.is_empty())
    {
        lines.push("Advisory heuristic flags (items to re-read; not verdicts):".into());
        for (flag, count) in flags {
            lines.push(format!("  {flag}: {count}"));
        }
    }
    let mut stage = None;
    for item in report["items"].as_array().into_iter().flatten() {
        let this = item["stage"].as_u64();
        if stage != Some(this) {
            stage = Some(this);
            lines.push(String::new());
            lines.push(match this {
                Some(s) => format!("Stage {s}"),
                None => "Unstaged".into(),
            });
        }
        let detail = match &item["current_assessment"] {
            Value::Null if item["attempt_count"] == 0 => "no attempt".to_owned(),
            Value::Null => format!(
                "{} attempt(s), latest {}",
                item["attempt_count"],
                text(item, "latest_attempt_date")
            ),
            c => format!(
                "{} [{}; {}] in {}",
                text(c, "date"),
                text(c, "review"),
                text(c, "publication"),
                text(c, "attempt_id")
            ),
        };
        lines.push(format!(
            "  {} — {} ({}; route position {}, {})",
            text(item, "statement_id"),
            text(item, "state"),
            detail,
            item["route_position"],
            text(item, "depth")
        ));
        if item["pending_revision_impacts"].as_u64().unwrap_or(0) > 0 {
            lines.push(format!(
                "    pending revision impacts: {}",
                item["pending_revision_impacts"]
            ));
        }
        for flag in item["flags"].as_array().into_iter().flatten() {
            let extra = match text(flag, "flag") {
                "legacy_blocker_old_policy_framing" => format!(
                    " ({} in {})",
                    strings(&flag["patterns"]).join(", "),
                    text(flag, "attempt_id")
                ),
                "latest_attempt_predates_objection_standard" => {
                    format!(" ({})", text(flag, "date"))
                }
                "consumer_on_sense_index_allowlist" => format!(
                    " ({} consuming argument(s); see --json)",
                    strings(&flag["argument_ids"]).len()
                ),
                _ => String::new(),
            };
            lines.push(format!("    heuristic: {}{extra}", text(flag, "flag")));
        }
    }
    if report["listed"] != report["summary"]["open_premises"] {
        lines.push(format!(
            "\n(listed {} of {}; --limit)",
            report["listed"], report["summary"]["open_premises"]
        ));
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    const CURRENT: &str = "e0000000-0000-4000-8000-000000000001";
    const LEGACY: &str = "e0000000-0000-4000-8000-000000000002";
    const NONE: &str = "e0000000-0000-4000-8000-000000000003";

    fn fixture() -> std::path::PathBuf {
        let root = std::env::temp_dir().join(format!(
            "truth-currentness-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("corpus/attempts")).unwrap();
        let write = |name: &str, value: Value| {
            std::fs::write(
                root.join("corpus/attempts").join(name),
                serde_json::to_vec(&value).unwrap(),
            )
            .unwrap()
        };
        write(
            "current.json",
            json!({"id": "d0000000-0000-4000-8000-000000000001", "label": "current",
                "statement_ids": [CURRENT], "date": "2026-11-17", "kind": "derivation",
                "outcome": "blocked", "summary": "s", "evidence": [],
                "current_assessment": {"date": "2026-11-17", "statement_ids": [CURRENT],
                    "scope": "cluster", "assessment": "qualified", "next_test": "t",
                    "note": "docs/notes/x.md#a",
                    "reviewed_revision": "1234567890123456789012345678901234567890",
                    "review": "accepted_qualified", "publication": "merged",
                    "evidence": "PR", "supersedes": "none"}}),
        );
        write(
            "legacy.json",
            json!({"id": "d0000000-0000-4000-8000-000000000002", "label": "legacy",
                "statement_ids": [LEGACY], "date": "2026-11-01", "kind": "derivation",
                "outcome": "blocked", "summary": "s", "evidence": [],
                "blocker": "The bridge does not discriminate against a rival who denies it."}),
        );
        root
    }

    #[test]
    fn states_flags_and_order() {
        let root = fixture();
        let corpus = Corpus::load(&root).unwrap();
        let frontier = json!({
            "root": "ROOT",
            "stages": [{"stage": 1, "statement_id": "ROOT"}],
            "statement_stages": {LEGACY: [1, 2], CURRENT: [1]},
            "items": [
                {"statement_id": NONE, "path_to_root": [NONE, "a", "ROOT"], "depth": "bare",
                 "transcription_only": true, "dependent_arguments": ["ARG"],
                 "alternatives": [], "objections": []},
                {"statement_id": LEGACY, "path_to_root": [LEGACY, "a", "b", "c", "ROOT"],
                 "depth": "stated", "transcription_only": false, "dependent_arguments": [],
                 "alternatives": [{"statement_id": "RIVAL", "refuted": false}], "objections": []},
                {"statement_id": CURRENT, "path_to_root": [CURRENT, "a", "ROOT"],
                 "depth": "supported", "transcription_only": false, "dependent_arguments": [],
                 "alternatives": [{"statement_id": "RIVAL", "refuted": false}], "objections": []},
            ]
        });
        let allowlist = json!({"arguments": {"ARG": {"PRIOR": ["s"]}}});
        let report = report(&frontier, &corpus, &allowlist, &[], None);
        assert_eq!(
            report["summary"]["states"],
            json!({"current": 1, "legacy_only": 1, "none": 1})
        );
        let items = report["items"].as_array().unwrap();
        // Stage 1 by route position, then unstaged.
        let order: Vec<_> = items.iter().map(|i| text(i, "statement_id")).collect();
        assert_eq!(order, [CURRENT, LEGACY, NONE]);
        assert_eq!(items[0]["state"], "current");
        assert_eq!(
            items[0]["current_assessment"]["review"],
            "accepted_qualified"
        );
        assert_eq!(items[0]["current_assessment"]["publication"], "merged");
        assert_eq!(
            items[0]["flags"],
            json!([]),
            "a covering assessment clears the rival flag"
        );
        let legacy: Vec<_> = items[1]["flags"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| text(f, "flag"))
            .collect();
        assert_eq!(
            legacy,
            [
                "rivals_without_current_assessment",
                "latest_attempt_predates_objection_standard",
                "legacy_blocker_old_policy_framing"
            ]
        );
        assert_eq!(
            items[1]["flags"][2]["patterns"],
            json!(["rival_exhaustion"])
        );
        assert_eq!(items[2]["state"], "none");
        assert_eq!(items[2]["stage"], Value::Null);
        assert_eq!(items[2]["flags"][0]["flag"], "transcription_only_support");
        assert_eq!(items[2]["flags"][1]["argument_ids"], json!(["ARG"]));
        let text = format(&report);
        assert!(text.contains("current 1, legacy_only 1, none 1"));
        let limited = super::report(&frontier, &corpus, &allowlist, &[], Some(1));
        assert_eq!(limited["listed"], 1);
        assert_eq!(limited["summary"]["open_premises"], 3);
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn pending_impacts_count_statement_consumers() {
        let root = fixture();
        let corpus = Corpus::load(&root).unwrap();
        let frontier = json!({"root": "ROOT", "stages": [], "statement_stages": {},
            "items": [{"statement_id": LEGACY, "path_to_root": [LEGACY, "ROOT"]}]});
        let impacts = [json!({"consumers": [
            {"consumer": format!("statements:{LEGACY}"), "disposition": "pending"},
            {"consumer": format!("statements:{LEGACY}"), "disposition": "retained"},
            {"consumer": "arguments:X", "disposition": "pending"}]})];
        let report = report(&frontier, &corpus, &json!({}), &impacts, None);
        assert_eq!(report["items"][0]["pending_revision_impacts"], 1);
        std::fs::remove_dir_all(root).unwrap();
    }
}
