//! Navigation commands ported from `scripts/corpus.py`: `next` (the source
//! candidate queue), the ID lists `arguments` and `results`, `sort-lists`
//! and the `next-steps` text view of the frontier's `next_steps` projection
//! (`scripts/next_steps.py`, `format_next_steps`). The projection itself is
//! computed by [`crate::frontier`].

use crate::{Corpus, pyfmt, pyjson::Ordered};
use serde_json::Value;
use std::{fs, path::Path};

/// Order-free lists that many PRs append to (Python `SORTED_LIST_FIELDS`):
/// directory under `corpus/` and its fields.
pub const SORTED_LIST_FIELDS: &[(&str, &[&str])] = &[("sources", &["edition_urns"])];

/// The highest-priority source candidate (Python `command_next`: least
/// `(priority, id)`), as its record and as `json.dumps(candidate, indent=2,
/// ensure_ascii=False)` prints it, in file key order. `None`: no candidates.
pub fn next_candidate(root: &Path, corpus: &Corpus) -> Result<Option<(Value, String)>, String> {
    let entries = corpus.entries("candidates");
    let key = |fields: &serde_json::Map<String, Value>| {
        (
            fields.get("priority").and_then(Value::as_i64).unwrap_or(0),
            fields
                .get("id")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_owned(),
        )
    };
    let Some(best) = entries
        .iter()
        .min_by(|a, b| key(&a.fields).cmp(&key(&b.fields)))
    else {
        return Ok(None);
    };
    let raw = fs::read_to_string(root.join(&best.path))
        .map_err(|error| format!("{}: {error}", best.path))?;
    let ordered = Ordered::parse(&raw).map_err(|error| format!("{}: {error}", best.path))?;
    Ok(Some((
        Value::Object(best.fields.clone()),
        ordered.dumps(Some(2)),
    )))
}

/// The IDs of one record kind in file order (Python `command_ids`).
pub fn ids(corpus: &Corpus, kind: &str) -> Vec<String> {
    corpus
        .records(kind)
        .into_iter()
        .filter_map(|fields| fields.get("id").and_then(Value::as_str).map(str::to_owned))
        .collect()
}

/// One list `sort_lists` sorted: the record path relative to the checkout
/// and the field.
pub struct Sorted {
    pub path: String,
    pub field: String,
}

/// Python `command_sort_lists`: sorts every unsorted order-free list of
/// string items in place, rewriting the record with Python's
/// `json.dumps(record, ensure_ascii=False, indent=2 or None) + "\n"` (indent 2
/// when the file was indented), keys in file order.
pub fn sort_lists(root: &Path) -> Result<Vec<Sorted>, String> {
    let mut sorted = Vec::new();
    for (directory, fields) in SORTED_LIST_FIELDS {
        let mut paths: Vec<_> = match fs::read_dir(root.join("corpus").join(directory)) {
            Ok(entries) => entries
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
                .collect(),
            Err(_) => Vec::new(),
        };
        paths.sort();
        for path in paths {
            let relative = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .into_owned();
            let raw = fs::read_to_string(&path).map_err(|error| format!("{relative}: {error}"))?;
            let mut record =
                Ordered::parse(&raw).map_err(|error| format!("{relative}: {error}"))?;
            for field in *fields {
                let Some(Ordered::Array(items)) = record.get_mut(field) else {
                    continue;
                };
                let mut strings: Vec<String> = Vec::new();
                for item in items.iter() {
                    match item {
                        Ordered::String(text) => strings.push(text.clone()),
                        _ => {
                            return Err(format!(
                                "{relative}: {field} has a non-string item; cannot sort it"
                            ));
                        }
                    }
                }
                let mut ordered = strings.clone();
                ordered.sort();
                if ordered == strings {
                    continue;
                }
                *items = ordered.into_iter().map(Ordered::String).collect();
                let indent = raw.contains("\n  \"").then_some(2);
                fs::write(&path, record.dumps(indent) + "\n")
                    .map_err(|error| format!("{relative}: {error}"))?;
                sorted.push(Sorted {
                    path: relative.clone(),
                    field: (*field).to_owned(),
                });
            }
        }
    }
    Ok(sorted)
}

fn strs(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

fn joined(value: &Value) -> String {
    strs(value).join(", ")
}

fn or_none(text: String) -> String {
    if text.is_empty() { "none".into() } else { text }
}

fn items(value: &Value) -> &[Value] {
    value.as_array().map(Vec::as_slice).unwrap_or_default()
}

/// Python `format_next_steps`: the text view of a frontier `next_steps`
/// projection.
pub fn format_next_steps(report: &Value) -> String {
    let t = pyfmt::text;
    let root = match report.get("root") {
        Some(root) if pyfmt::truthy(Some(root)) => t(&root["statement_id"]),
        _ => "no root".into(),
    };
    let mut lines = vec![format!("Next steps for {root}")];
    let progress = &report["progress"];
    lines.push(format!(
        "Foundational progress: {} established root-reaching statements; \
         {} of {} unestablished premises with verified support alternatives; \
         {} distinct conditional bundles",
        t(&progress["root_reaching_established_count"]),
        t(&progress["with_verified_alternative_count"]),
        t(&progress["unestablished_premise_count"]),
        t(&progress["verified_alternative_bundle_count"]),
    ));
    lines.push(
        "Inspectable premise support options (conditional; not independence certificates):".into(),
    );
    for item in items(&report["support_options"]["items"]) {
        let available = if pyfmt::truthy(item.get("direct_assumption_available")) {
            "direct assumption available"
        } else {
            "established in corpus"
        };
        lines.push(format!("  {}: {available}", t(&item["statement_id"])));
        for bundle in items(&item["verified_alternative_bundles"]) {
            lines.push(format!(
                "    premises: {}",
                or_none(joined(&bundle["premise_statement_ids"]))
            ));
            lines.push(format!(
                "    arguments: {}",
                joined(&bundle["argument_ids"])
            ));
            lines.push(format!(
                "    verified results: {}",
                joined(&bundle["result_ids"])
            ));
        }
    }
    // Python keeps the rules' insertion order: floor, derive, defend.
    if let Some(rules) = report["settlement_rules"].as_object() {
        let order = ["floor", "derive", "defend"];
        let mut kinds: Vec<&String> = order
            .iter()
            .filter_map(|kind| rules.get_key_value(*kind).map(|(key, _)| key))
            .collect();
        kinds.extend(rules.keys().filter(|key| !order.contains(&key.as_str())));
        for kind in kinds {
            lines.push(format!("{kind}: {}", t(&rules[kind])));
        }
    }
    lines.push(
        "Expanded routes (cost diagnostic; joint settlement unresolved without complete failure-mode coverage):"
            .into(),
    );
    for route in items(&report["routes"]) {
        lines.push(format!(
            "  {:>3} {}",
            t(&route["cost"]),
            t(&route["argument_id"])
        ));
    }
    lines.push(
        "Lowest-expanded-cost route leaves, ranked by counterfactual settlement impact (diagnostic):"
            .into(),
    );
    for leaf in items(&report["leaves"]) {
        if !pyfmt::truthy(leaf.get("on_cheapest_route")) {
            continue;
        }
        let depth = if pyfmt::truthy(leaf.get("depth")) {
            t(&leaf["depth"])
        } else {
            "proved from open premises".into()
        };
        lines.push(format!(
            "  {} [{depth}]: {} routes improve; total cost drop {}",
            t(&leaf["statement_id"]),
            t(&leaf["impact"]["routes_improved"]),
            t(&leaf["impact"]["total_cost_drop"]),
        ));
        lines.push("    floor: owner decision required".into());
        for proof in items(&leaf["derivations"]) {
            let unverified = if pyfmt::truthy(proof.get("verified")) {
                ""
            } else {
                " (no verified result)"
            };
            lines.push(format!(
                "    derive via {}: missing {}{unverified}",
                t(&proof["argument_id"]),
                or_none(joined(&proof["missing_statement_ids"])),
            ));
        }
        lines.push(format!(
            "    defend: undefeated recorded rivals {}",
            joined(&leaf["defense"]["undefeated_statement_ids"])
        ));
    }
    lines.push("Recorded owner decisions:".into());
    for decision in items(&report["owner_decisions"]) {
        for action in items(&decision["actions"]) {
            lines.push(format!(
                "  {}: {} / {}: {}",
                t(&decision["statement_id"]),
                t(&action["kind"]),
                t(&action["status"]),
                t(&action["description"]),
            ));
        }
    }
    lines.push("Partition opportunities:".into());
    for partition in items(&report["partitions"]) {
        lines.push(format!(
            "  {}: target {}; missing background {}",
            t(&partition["result_id"]),
            t(&partition["target_statement_id"]),
            or_none(joined(&partition["missing_background_statement_ids"])),
        ));
        for cell in items(&partition["cases"]) {
            let state = if pyfmt::truthy(cell.get("refuted")) {
                "refuted"
            } else {
                "undefeated"
            };
            lines.push(format!(
                "    {}: {state} ({})",
                t(&cell["label"]),
                t(&cell["lean_declaration"]),
            ));
        }
    }
    lines.push(format!(
        "Joint settlement: {} unresolved route pairs; see JSON for all failure modes.",
        items(&report["joint_settlements"]).len()
    ));
    let joint = &report["joint_settlement_summary"];
    let shared = items(&joint["shared_by_all_reported_routes"]);
    lines.push(format!(
        "Shared by all {} reported verified routes: {} open obligations (not exhaustive route necessity).",
        t(&joint["verified_route_count"]),
        shared.len()
    ));
    lines.extend(shared.iter().map(|sid| format!("  {}", t(sid))));
    lines.push(t(&report["impact_scope"]));
    lines.join("\n")
}
