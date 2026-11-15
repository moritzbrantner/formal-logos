//! Result premises whose bound hypothesis the proof term never uses (#571),
//! ported from `scripts/corpus.py unused-premises`.
//!
//! Lean stays the verifier: `scripts/UnusedPremises.lean` decides, per
//! theorem, which propositional binders the proof term uses, and
//! `scripts/BindTypes.lean` (through [`crate::bind_check`]) which premise
//! statement each binder carries. This module only joins the two exporter
//! outputs, as Python's `unused_premise_findings` does, applies the
//! checked-in exemptions (`apply_unused_exemptions`) and prints the report.

use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::Path,
};

/// The exporter that reports proof-term use of each binder.
pub const UNUSED_TOOL: &str = "scripts/UnusedPremises.lean";
/// The default exemption file of the strict gate.
pub const EXEMPTIONS: &str = "scripts/unused-premise-exemptions.json";
/// Its file name, as the text output names it.
pub const EXEMPTIONS_NAME: &str = "unused-premise-exemptions.json";

/// `(result_id, statement_id) -> reason`.
pub type Exemptions = BTreeMap<(String, String), String>;

/// Python `load_unused_exemptions`: a missing file exempts nothing.
pub fn load_exemptions(path: &Path) -> Result<Exemptions, String> {
    let name = path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(Exemptions::new());
        }
        Err(error) => return Err(format!("{name}: cannot read: {error}")),
    };
    let data: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("{name}: invalid JSON: {error}"))?;
    let Some(entries) = data.get("exemptions").and_then(Value::as_array) else {
        return Err(format!(
            "{name}: expected an object with an `exemptions` list"
        ));
    };
    let mut exemptions = Exemptions::new();
    for (index, entry) in entries.iter().enumerate() {
        let place = format!("{name}: exemption {index}");
        let keys: BTreeSet<&str> = entry
            .as_object()
            .map(|object| object.keys().map(String::as_str).collect())
            .unwrap_or_default();
        if !entry.is_object() || keys != BTreeSet::from(["reason", "result_id", "statement_ids"]) {
            return Err(format!(
                "{place}: needs exactly `result_id`, `statement_ids` and `reason`"
            ));
        }
        let result_id = match entry["result_id"].as_str() {
            Some(id) if !id.is_empty() => id,
            _ => return Err(format!("{place}: `result_id` must be a nonempty string")),
        };
        if !entry["reason"]
            .as_str()
            .is_some_and(|reason| !reason.trim().is_empty())
        {
            return Err(format!(
                "{place} ({result_id}): `reason` must be a nonempty string"
            ));
        }
        let reason = entry["reason"].as_str().unwrap_or_default();
        let statements: Option<Vec<&str>> = entry["statement_ids"].as_array().and_then(|items| {
            items
                .iter()
                .map(|item| item.as_str().filter(|id| !id.is_empty()))
                .collect()
        });
        let statements = match statements {
            Some(statements) if !statements.is_empty() => statements,
            _ => {
                return Err(format!(
                    "{place} ({result_id}): `statement_ids` must be a nonempty list of ids"
                ));
            }
        };
        for statement in statements {
            let key = (result_id.to_owned(), statement.to_owned());
            if exemptions.contains_key(&key) {
                return Err(format!(
                    "{place}: {result_id} / {statement} is exempted twice"
                ));
            }
            exemptions.insert(key, reason.to_owned());
        }
    }
    Ok(exemptions)
}

/// A JSON value as a hashable key (Python dict keys compare by value).
fn key(value: &Value) -> String {
    value.to_string()
}

/// Python truthiness of an indexed list element.
fn truthy(value: Option<&Value>) -> bool {
    crate::pyfmt::truthy(value)
}

/// Python `unused_premise_findings`: joins bind-check's premise binding
/// (`bind_entries`, the `results` of a bind report) with the exporter's
/// per-binder usage. Results bind-check leaves unbound (`mismatch`), and
/// results the exporter did not describe, are skipped and listed.
pub fn findings(bind_entries: &[Value], usage: &[Value], root_open: &HashSet<String>) -> Value {
    let mut by_theorem: HashMap<String, &Value> = HashMap::new();
    for entry in usage {
        by_theorem.insert(key(entry.get("theorem").unwrap_or(&Value::Null)), entry);
    }
    let mut findings = Vec::new();
    let mut skipped: BTreeSet<String> = BTreeSet::new();
    let mut checked = 0usize;
    for entry in bind_entries {
        if entry.get("kind").and_then(Value::as_str) == Some("schema-registration") {
            continue;
        }
        let id = crate::pyfmt::text(&entry["id"]);
        let described = by_theorem.get(&key(&entry["theorem"])).copied();
        let described = match described {
            Some(described)
                if entry["status"] != "mismatch"
                    && described
                        .as_object()
                        .is_some_and(|o| !o.contains_key("error")) =>
            {
                described
            }
            _ => {
                skipped.insert(id);
                continue;
            }
        };
        checked += 1;
        let mut by_position: HashMap<String, &Value> = HashMap::new();
        for item in described["hypotheses"].as_array().into_iter().flatten() {
            by_position.insert(key(&item["position"]), item);
        }
        for premise in entry["premises"].as_array().into_iter().flatten() {
            let Some(item) = by_position.get(&key(&premise["position"])) else {
                skipped.insert(id.clone());
                break;
            };
            let conjunct = premise.as_object().and_then(|p| p.get("conjunct"));
            let used = match conjunct {
                Some(conjunct) => match item.get("conjuncts_used") {
                    Some(Value::Array(flags)) => truthy(
                        conjunct
                            .as_u64()
                            .and_then(|index| flags.get(index as usize)),
                    ),
                    _ => true,
                },
                None => truthy(item.get("used")),
            };
            if used {
                continue;
            }
            let statement = premise["statement_id"].clone();
            let mut finding = Map::new();
            finding.insert("result_id".into(), entry["id"].clone());
            finding.insert("theorem".into(), entry["theorem"].clone());
            finding.insert("hypothesis".into(), premise["hypothesis"].clone());
            finding.insert("statement_id".into(), statement.clone());
            finding.insert(
                "open_on_root_path".into(),
                json!(
                    statement
                        .as_str()
                        .is_some_and(|statement| root_open.contains(statement))
                ),
            );
            if let Some(conjunct) = conjunct {
                finding.insert("bundle".into(), premise["bundle"].clone());
                finding.insert("conjunct".into(), conjunct.clone());
            }
            findings.push(Value::Object(finding));
        }
    }
    json!({
        "summary": {"checked": checked, "findings": findings.len(), "skipped": skipped.len()},
        "findings": findings,
        "skipped": skipped,
    })
}

fn finding_key(finding: &Value) -> (String, String) {
    (
        crate::pyfmt::text(&finding["result_id"]),
        crate::pyfmt::text(&finding["statement_id"]),
    )
}

/// Python `apply_unused_exemptions`: splits the findings into gating and
/// exempted ones and lists the stale exemptions (an exemption without a
/// finding fails the strict gate like a finding).
pub fn apply_exemptions(mut report: Value, exemptions: &Exemptions) -> Value {
    let all = report["findings"].as_array().cloned().unwrap_or_default();
    let found: HashSet<(String, String)> = all.iter().map(finding_key).collect();
    let mut gating = Vec::new();
    let mut exempted = Vec::new();
    for finding in all {
        match exemptions.get(&finding_key(&finding)) {
            Some(reason) => {
                let mut finding = finding;
                finding["exemption_reason"] = json!(reason);
                exempted.push(finding);
            }
            None => gating.push(finding),
        }
    }
    let mut stale: Vec<String> = exemptions
        .keys()
        .filter(|key| !found.contains(*key))
        .map(|(result, statement)| format!("{result} / {statement}"))
        .collect();
    stale.sort();
    report["summary"]["exempted"] = json!(exempted.len());
    report["summary"]["gating"] = json!(gating.len());
    report["summary"]["stale_exemptions"] = json!(stale.len());
    report["findings"] = json!(gating);
    report["exempted"] = json!(exempted);
    report["stale_exemptions"] = json!(stale);
    report
}

/// Whether the strict gate fails: an unexempted finding or a stale exemption.
pub fn gate_fails(report: &Value) -> bool {
    let nonempty = |field: &str| {
        report[field]
            .as_array()
            .is_some_and(|list| !list.is_empty())
    };
    nonempty("findings") || nonempty("stale_exemptions")
}

/// The text report, before uuids are humanized.
pub fn format(report: &Value) -> String {
    let text = crate::pyfmt::text;
    let mut lines = Vec::new();
    for finding in report["findings"].as_array().into_iter().flatten() {
        let place = if finding.get("bundle").is_some() {
            format!(
                " (conjunct {} of {})",
                finding["conjunct"].as_i64().unwrap_or_default() + 1,
                text(&finding["bundle"])
            )
        } else {
            String::new()
        };
        let root = if truthy(finding.get("open_on_root_path")) {
            " [open, on root path]"
        } else {
            ""
        };
        lines.push(format!(
            "unused: {}: {} via {}{place}{root}",
            text(&finding["result_id"]),
            text(&finding["statement_id"]),
            text(&finding["hypothesis"]),
        ));
    }
    for finding in report["exempted"].as_array().into_iter().flatten() {
        lines.push(format!(
            "exempted: {}: {} ({})",
            text(&finding["result_id"]),
            text(&finding["statement_id"]),
            text(&finding["exemption_reason"]),
        ));
    }
    for stale in report["stale_exemptions"].as_array().into_iter().flatten() {
        lines.push(format!(
            "stale exemption: {} has no unused-premise finding; remove it from {EXEMPTIONS_NAME}",
            text(stale)
        ));
    }
    for result in report["skipped"].as_array().into_iter().flatten() {
        lines.push(format!(
            "skipped: {} (not bound by bind-check)",
            text(result)
        ));
    }
    let summary = &report["summary"];
    lines.push(format!(
        "unused-premises: {} results checked, {} unexempted and {} exempted unused premise(s), \
         {} stale exemption(s), {} skipped",
        summary["checked"],
        summary["gating"],
        summary["exempted"],
        summary["stale_exemptions"],
        summary["skipped"],
    ));
    lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    fn premise(statement: &str, position: u64) -> Value {
        json!({"hypothesis": format!("h{statement}"), "position": position, "statement_id": statement})
    }

    #[test]
    fn joins_binding_and_usage_like_python() {
        let bound = vec![
            json!({"id": "R", "theorem": "T.R", "status": "bound",
                   "premises": [premise("P", 1), premise("Q", 2),
                                {"hypothesis": "hT", "position": 3, "statement_id": "B",
                                 "bundle": "T.Theory", "conjunct": 1}]}),
            json!({"id": "S", "theorem": "T.S", "status": "mismatch", "premises": []}),
        ];
        let usage = vec![json!({"theorem": "T.R", "hypotheses": [
            {"position": 1, "name": "h1", "used": true},
            {"position": 2, "name": "h2", "used": false},
            {"position": 3, "name": "h3", "used": true, "conjuncts_used": [true, false]}]})];
        let open = HashSet::from(["Q".to_owned()]);
        let report = findings(&bound, &usage, &open);
        assert_eq!(
            report["summary"],
            json!({"checked": 1, "findings": 2, "skipped": 1})
        );
        assert_eq!(report["findings"][0]["open_on_root_path"], true);
        assert_eq!(report["findings"][1]["conjunct"], 1);
        let exemptions = Exemptions::from([
            (("R".into(), "Q".into()), "bundle".into()),
            (("R".into(), "Z".into()), "gone".into()),
        ]);
        let report = apply_exemptions(report, &exemptions);
        assert_eq!(report["summary"]["gating"], 1);
        assert_eq!(report["stale_exemptions"], json!(["R / Z"]));
        assert!(gate_fails(&report));
        assert!(format(&report).ends_with(
            "unused-premises: 1 results checked, 1 unexempted and 1 exempted unused premise(s), \
             1 stale exemption(s), 1 skipped\n"
        ));
    }
}
