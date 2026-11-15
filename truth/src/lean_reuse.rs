//! Lean proof-term theorem reuse (#959), ported from `scripts/corpus.py
//! lean-reuse` and the proof-use part of `scripts/argument_context.py`
//! (`classify_result_reuse`, `lean_reuse_review`).
//!
//! Lean stays the authority: `scripts/LeanReuse.lean` lists, per inspected
//! result theorem, the registered result theorems its elaborated proof term
//! reaches. This module writes the exporter input, validates its output
//! (`lean_reuse_usage_map`) and classifies each observed reference against
//! the Solution's import closure and the argument graph. Review only: it
//! writes no records and certifies nothing.

use crate::{Corpus, context::Lean, pyfmt};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::Path,
};

/// The exporter.
pub const TOOL: &str = "scripts/LeanReuse.lean";
/// The command named in the missing-`lake` message (Python passes
/// `command_name="lean-reuse"` for `context --proof-use` as well).
pub const COMMAND: &str = "lean-reuse";

pub const GRAPH_LINKED: &str = "theorem-used, graph-linked";
pub const NOT_IN_GRAPH: &str = "theorem-used, not in argument graph";
pub const IMPORT_ONLY: &str = "import only";

type Record = Map<String, Value>;

fn text<'a>(record: &'a Record, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn get(record: &Record, field: &str) -> Value {
    record.get(field).cloned().unwrap_or(Value::Null)
}

/// Python `run_lean_reuse_tool`'s input, serialized as `json.dump` writes
/// it: the Solution modules of the inspected results, every result theorem
/// and the inspected theorems (all of them when `inspect` is `None`).
pub fn tool_input(corpus: &Corpus, inspect: Option<&[String]>) -> String {
    let results = corpus.records("results");
    let theorems: BTreeSet<&str> = results.iter().map(|r| text(r, "theorem")).collect();
    let inspected: BTreeSet<&str> = match inspect {
        Some(names) => names.iter().map(String::as_str).collect(),
        None => theorems.clone(),
    };
    let modules: BTreeSet<&str> = results
        .iter()
        .filter(|r| inspected.contains(text(r, "theorem")))
        .map(|r| text(r, "solution_module"))
        .collect();
    let list = |items: &BTreeSet<&str>| {
        format!(
            "[{}]",
            items
                .iter()
                .map(|item| pyfmt::json_str(item, true))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "{{\"modules\": {}, \"theorems\": {}, \"inspect\": {}}}",
        list(&modules),
        list(&theorems),
        list(&inspected)
    )
}

/// Python `read_lean_reuse_json`'s shape check of a parsed output.
pub fn rows(value: Value) -> Result<Vec<Value>, String> {
    match value {
        Value::Array(rows) => Ok(rows),
        _ => Err("Lean reuse output must be a JSON array".into()),
    }
}

/// Python `lean_reuse_usage_map`: the referenced result theorems per
/// expected theorem (without itself), sorted. A theorem the exporter did
/// not inspect is an error, never an unused import.
pub fn usage_map(
    rows: &[Value],
    expected: &[String],
) -> Result<BTreeMap<String, Vec<String>>, String> {
    let expected_set: BTreeSet<&str> = expected.iter().map(String::as_str).collect();
    let mut uses = BTreeMap::new();
    for row in rows {
        let Some(theorem) = row.get("theorem").and_then(Value::as_str) else {
            return Err("Lean reuse output contains an invalid theorem entry".into());
        };
        if !row.is_object() {
            return Err("Lean reuse output contains an invalid theorem entry".into());
        }
        if !expected_set.contains(theorem) {
            continue;
        }
        if uses.contains_key(theorem) {
            return Err(format!("duplicate Lean reuse entry for {theorem}"));
        }
        if pyfmt::truthy(row.get("error")) {
            return Err(format!(
                "Lean reuse could not inspect {theorem}: {}",
                pyfmt::text(&row["error"])
            ));
        }
        let names: Option<BTreeSet<&str>> = row
            .get("proof_theorems")
            .and_then(Value::as_array)
            .and_then(|items| items.iter().map(Value::as_str).collect());
        let Some(mut names) = names else {
            return Err(format!(
                "Lean reuse entry for {theorem} needs proof_theorems: [strings]"
            ));
        };
        names.remove(theorem);
        uses.insert(
            theorem.to_owned(),
            names.into_iter().map(str::to_owned).collect(),
        );
    }
    let missing: Vec<&str> = expected_set
        .iter()
        .filter(|name| !uses.contains_key(**name))
        .copied()
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "Lean reuse did not inspect these theorems (built library may be stale): {}",
            missing.join(", ")
        ));
    }
    Ok(uses)
}

/// One classified reference (Python `classify_result_reuse` entry).
#[derive(Debug, Clone)]
pub struct Reuse {
    pub module: Value,
    pub depth: Option<usize>,
    pub result_id: String,
    pub argument_id: String,
    pub theorem: Value,
    pub status: Value,
    pub graph_linked: bool,
    pub theorem_used: bool,
    pub classification: &'static str,
}

impl Reuse {
    /// The Python entry as a JSON object.
    pub fn to_value(&self) -> Value {
        json!({
            "module": self.module, "depth": self.depth, "result_id": self.result_id,
            "argument_id": self.argument_id, "theorem": self.theorem, "status": self.status,
            "graph_linked": self.graph_linked, "theorem_used": self.theorem_used,
            "classification": self.classification,
        })
    }
}

/// The result records in load order and by their Solution and Challenge
/// modules, built once for many classifications.
pub(crate) struct Results<'a> {
    all: Vec<&'a Record>,
    by_module: HashMap<&'a str, Vec<&'a Record>>,
}

impl<'a> Results<'a> {
    pub(crate) fn new(corpus: &'a Corpus) -> Self {
        let all = corpus.records("results");
        let mut by_module: HashMap<&str, Vec<&Record>> = HashMap::new();
        for other in &all {
            for key in ["solution_module", "challenge_module"] {
                if pyfmt::truthy(other.get(key)) {
                    by_module.entry(text(other, key)).or_default().push(other);
                }
            }
        }
        Self { all, by_module }
    }
}

/// Python `classify_result_reuse`: each result reached through the
/// Solution's import closure or referenced by the proof term, classified
/// as theorem-used and graph-linked (it concludes a premise or commitment
/// of this argument), theorem-used without a graph link, or import only.
pub(crate) fn classify(
    lean: &Lean,
    corpus: &Corpus,
    index: &Results,
    result: &Record,
    used_theorems: &[String],
) -> Vec<Reuse> {
    let module = text(result, "solution_module");
    let closure = if module.is_empty() {
        Vec::new()
    } else {
        lean.closure(module)
    };
    let (results, by_module) = (&index.all, &index.by_module);
    let graph = corpus
        .get("arguments", text(result, "argument_id"))
        .map(|argument| &argument.fields);
    let graph_premises: BTreeSet<&str> = graph
        .into_iter()
        .flat_map(|argument| {
            ["premise_statement_ids", "commitment_statement_ids"]
                .into_iter()
                .flat_map(|field| {
                    argument
                        .get(field)
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                })
        })
        .filter_map(Value::as_str)
        .collect();
    let used: BTreeSet<&str> = used_theorems.iter().map(String::as_str).collect();
    let mut found: BTreeMap<String, Reuse> = BTreeMap::new();
    let add = |found: &mut BTreeMap<String, Reuse>,
               other: &Record,
               imported: Option<&str>,
               depth: Option<usize>| {
        if text(other, "id") == text(result, "id") {
            return;
        }
        let conclusion = corpus
            .get("arguments", text(other, "argument_id"))
            .and_then(|argument| argument.fields.get("conclusion_statement_id"))
            .and_then(Value::as_str);
        let graph_linked = conclusion.is_some_and(|c| graph_premises.contains(c));
        let theorem_used = other
            .get("theorem")
            .and_then(Value::as_str)
            .is_some_and(|theorem| used.contains(theorem));
        let classification = match (theorem_used, graph_linked) {
            (true, true) => GRAPH_LINKED,
            (true, false) => NOT_IN_GRAPH,
            (false, _) => IMPORT_ONLY,
        };
        let module = match imported {
            Some(module) if !module.is_empty() => json!(module),
            _ => get(other, "solution_module"),
        };
        found.insert(
            text(other, "id").to_owned(),
            Reuse {
                module,
                depth,
                result_id: text(other, "id").to_owned(),
                argument_id: text(other, "argument_id").to_owned(),
                theorem: get(other, "theorem"),
                status: get(other, "status"),
                graph_linked,
                theorem_used,
                classification,
            },
        );
    };
    for (imported, depth) in &closure {
        for other in by_module.get(imported.as_str()).into_iter().flatten() {
            add(&mut found, other, Some(imported), Some(*depth));
        }
    }
    for other in results {
        let theorem_used = other
            .get("theorem")
            .and_then(Value::as_str)
            .is_some_and(|theorem| used.contains(theorem));
        if theorem_used && !found.contains_key(text(other, "id")) {
            add(&mut found, other, None, None);
        }
    }
    let mut entries: Vec<Reuse> = found.into_values().collect();
    entries.sort_by(|a, b| {
        (a.depth.is_none(), a.depth.unwrap_or(0), &a.result_id).cmp(&(
            b.depth.is_none(),
            b.depth.unwrap_or(0),
            &b.result_id,
        ))
    });
    entries
}

/// Python `lean_reuse_review`: every inspected result's classified
/// references, in result-id order, with per-class counts.
pub fn review(root: &Path, corpus: &Corpus, uses: &BTreeMap<String, Vec<String>>) -> Value {
    let lean = Lean::new(root);
    let index = Results::new(corpus);
    let mut results = corpus.records("results");
    results.sort_by_key(|record| text(record, "id"));
    let mut findings = Vec::new();
    for result in results {
        let Some(used) = result
            .get("theorem")
            .and_then(Value::as_str)
            .and_then(|theorem| uses.get(theorem))
        else {
            continue;
        };
        for reuse in classify(&lean, corpus, &index, result, used) {
            let mut entry = Map::new();
            entry.insert("source_result_id".into(), get(result, "id"));
            if let Value::Object(fields) = reuse.to_value() {
                entry.extend(fields);
            }
            findings.push(Value::Object(entry));
        }
    }
    let count = |class: &str| {
        findings
            .iter()
            .filter(|finding| finding["classification"] == class)
            .count()
    };
    let summary = json!({
        "results_inspected": uses.len(),
        GRAPH_LINKED: count(GRAPH_LINKED),
        NOT_IN_GRAPH: count(NOT_IN_GRAPH),
        IMPORT_ONLY: count(IMPORT_ONLY),
    });
    json!({
        "authority": "Lean proof-term references; advisory only, not graph or proof certification",
        "summary": summary,
        "findings": findings,
    })
}

/// The `lean-reuse --review` text, before uuids are humanized.
pub fn format_review(report: &Value) -> String {
    let mut lines = Vec::new();
    for entry in report["findings"].as_array().into_iter().flatten() {
        if entry["classification"] != NOT_IN_GRAPH {
            continue;
        }
        let depth = match &entry["depth"] {
            Value::Null => "no source import".to_owned(),
            depth => depth.to_string(),
        };
        lines.push(format!(
            "review: {} uses {} ({}; {depth}; no matching argument premise)",
            pyfmt::text(&entry["source_result_id"]),
            pyfmt::text(&entry["result_id"]),
            pyfmt::text(&entry["theorem"]),
        ));
    }
    let summary = &report["summary"];
    let parts: Vec<String> = ["results_inspected", GRAPH_LINKED, NOT_IN_GRAPH, IMPORT_ONLY]
        .iter()
        .map(|key| format!("{key}: {}", summary[*key]))
        .collect();
    lines.push(format!("lean-reuse: {}", parts.join(", ")));
    lines.push(
        "All classifications: lean-reuse --review --json (advisory; no graph changes)".into(),
    );
    lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn usage_map_validates_like_python() {
        let expected = vec!["A".to_owned()];
        let rows = vec![
            json!({"theorem": "A", "proof_theorems": ["B", "A", "B"]}),
            json!({"theorem": "Z", "error": "ignored: not expected"}),
        ];
        assert_eq!(
            usage_map(&rows, &expected).unwrap()["A"],
            vec!["B".to_owned()]
        );
        assert!(
            usage_map(&rows[1..], &expected)
                .unwrap_err()
                .contains("stale")
        );
        let duplicate = vec![rows[0].clone(), rows[0].clone()];
        assert!(
            usage_map(&duplicate, &expected)
                .unwrap_err()
                .starts_with("duplicate")
        );
        let error = vec![json!({"theorem": "A", "error": "unknown theorem"})];
        assert_eq!(
            usage_map(&error, &expected).unwrap_err(),
            "Lean reuse could not inspect A: unknown theorem"
        );
        assert!(usage_map(&[json!(1)], &expected).is_err());
    }
}
