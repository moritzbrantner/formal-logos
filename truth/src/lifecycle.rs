//! Explicit, scoped research currentness and revision reassessment. These are
//! recorded judgments and work dispositions, never proof or acceptance gates.
use crate::{Corpus, evidence_graph::EvidenceGraph};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::Path,
};

fn text<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key].as_str().unwrap_or_default()
}

/// Canonical attempt extension; legacy attempts remain valid and unmarked.
pub fn validate(
    attempt: &serde_json::Map<String, Value>,
    statements: &HashSet<&str>,
) -> Result<(), String> {
    let Some(current) = attempt.get("current_assessment") else {
        if attempt.get("revisions").is_some() {
            return Err("revisions require a scoped current_assessment".into());
        }
        return Ok(());
    };
    for field in [
        "date",
        "scope",
        "assessment",
        "next_test",
        "note",
        "reviewed_revision",
        "review",
        "publication",
        "supersedes",
        "evidence",
    ] {
        if text(current, field).trim().is_empty() {
            return Err(format!("current_assessment.{field} must be nonempty"));
        }
    }
    if !["unreviewed", "accepted_qualified", "changes_requested"].contains(&text(current, "review"))
    {
        return Err("invalid current_assessment.review".into());
    }
    if !["unpublished", "published", "merged"].contains(&text(current, "publication")) {
        return Err("invalid current_assessment.publication".into());
    }
    let revision = text(current, "reviewed_revision");
    if revision.len() != 40 || !revision.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("reviewed_revision must be a full commit hash".into());
    }
    let ids = current["statement_ids"]
        .as_array()
        .ok_or("current assessment needs statement_ids")?;
    if ids
        .iter()
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>()
        .len()
        != ids.len()
    {
        return Err("current statement_ids must be unique strings".into());
    }
    if ids.is_empty()
        || ids.iter().any(|id| {
            !id.as_str().is_some_and(|id| {
                statements.contains(id)
                    && attempt["statement_ids"]
                        .as_array()
                        .is_some_and(|all| all.contains(&json!(id)))
            })
        })
    {
        return Err("current assessment scope must name statements in its attempt".into());
    }
    if let Some(changes) = attempt.get("revisions") {
        let mut revisions = BTreeSet::new();
        for change in changes.as_array().ok_or("revisions must be an array")? {
            if !["meaning", "premise_warrant", "judgment"].contains(&text(change, "kind"))
                || text(change, "reason").trim().is_empty()
                || text(change, "revision").trim().is_empty()
                || text(change, "previous").trim().is_empty()
            {
                return Err(
                    "revision needs kind (meaning/premise_warrant/judgment), revision, previous evidence locator and reason"
                        .into(),
                );
            }
            if !revisions.insert(text(change, "revision")) {
                return Err("revision identifiers must be unique within an attempt".into());
            }
            let targets = change["statement_ids"]
                .as_array()
                .ok_or("revision needs statement_ids")?;
            if targets
                .iter()
                .filter_map(Value::as_str)
                .collect::<BTreeSet<_>>()
                .len()
                != targets.len()
                || targets.is_empty()
                || targets.iter().any(|id| !ids.contains(id))
            {
                return Err("revision targets must be within current assessment scope".into());
            }
            if let Some(dispositions) = change.get("reassessments") {
                for d in dispositions
                    .as_array()
                    .ok_or("reassessments must be an array")?
                {
                    if text(d, "consumer").is_empty()
                        || text(d, "reason").trim().is_empty()
                        || !["pending", "retained", "revised", "not_applicable"]
                            .contains(&text(d, "disposition"))
                    {
                        return Err(
                            "reassessment needs consumer, explicit disposition and reason".into(),
                        );
                    }
                }
            }
        }
    }
    Ok(())
}

pub fn current(corpus: &Corpus, ids: &BTreeSet<String>) -> Vec<Value> {
    let mut out = Vec::new();
    for record in corpus.entries("attempts") {
        let Some(current) = record.fields.get("current_assessment") else {
            continue;
        };
        if current["statement_ids"].as_array().is_some_and(|scope| {
            scope
                .iter()
                .any(|id| id.as_str().is_some_and(|id| ids.contains(id)))
        }) {
            let mut entry = current.clone();
            entry["attempt_id"] = record.fields["id"].clone();
            entry["path"] = json!(record.path);
            out.push(entry);
        }
    }
    out.sort_by(|a, b| {
        text(b, "date")
            .cmp(text(a, "date"))
            .then_with(|| text(a, "attempt_id").cmp(text(b, "attempt_id")))
    });
    out
}

// Targets and review ledgers register work, rather than consuming its warrant.
// Keep substantive prose (including the selected assessment) in other attempts.
fn attempt_use(field: &str) -> bool {
    let mut parts = field.trim_start_matches('/').split('/');
    match parts.next() {
        Some("statement_ids" | "revisions") => false,
        Some("current_assessment") => {
            matches!(parts.next(), Some("assessment" | "scope" | "next_test"))
        }
        _ => true,
    }
}

/// Reverse explicit references expose potential uses, not semantic equivalence.
/// Propagate argument conclusions as well as references so downstream routes are
/// visible. No result's formal status is changed, even for unresolved uses.
pub fn impacts(root: &Path, corpus: &Corpus, ids: &BTreeSet<String>) -> Result<Vec<Value>, String> {
    let changes: Vec<_> = corpus
        .entries("attempts")
        .into_iter()
        .flat_map(|r| {
            r.fields
                .get("revisions")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .map(move |c| (r, c))
        })
        .collect();
    if changes.is_empty() {
        return Ok(Vec::new());
    }
    let graph = EvidenceGraph::build(root, corpus, None)?;
    // Reuse context's source-level import parser. Imports expose possible
    // semantic consumers; only Lean proof-use inspection can establish use.
    let lean = crate::context::Lean::new(root);
    let results = corpus.entries("results");
    let producer_conclusions: BTreeMap<String, String> = results
        .iter()
        .filter_map(|r| {
            let argument = corpus.get("arguments", r.fields["argument_id"].as_str()?)?;
            Some((
                format!("results:{}", r.fields["id"].as_str()?),
                format!(
                    "statements:{}",
                    argument.fields["conclusion_statement_id"].as_str()?
                ),
            ))
        })
        .collect();
    let mut imports = Vec::new();
    for consumer in &results {
        let module = consumer
            .fields
            .get("solution_module")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if module.is_empty() {
            continue;
        }
        let closure = lean.closure(module);
        for source in &results {
            if source.fields["id"] != consumer.fields["id"]
                && source
                    .fields
                    .get("solution_module")
                    .and_then(Value::as_str)
                    .is_some_and(|m| closure.iter().any(|(imported, _)| imported == m))
            {
                imports.push((
                    format!(
                        "results:{}",
                        consumer.fields["id"].as_str().unwrap_or_default()
                    ),
                    format!(
                        "results:{}",
                        source.fields["id"].as_str().unwrap_or_default()
                    ),
                ));
            }
        }
    }

    let mut out = Vec::new();
    for (attempt, change) in changes {
        let seeds: BTreeSet<String> = change["statement_ids"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(|id| format!("statements:{id}"))
            .collect();
        let mut seen = seeds.clone();
        let mut via = BTreeMap::new();
        let mut import_sources = BTreeMap::new();
        let declaring_attempt = format!(
            "attempts:{}",
            attempt.fields["id"].as_str().unwrap_or_default()
        );
        loop {
            let mut next = Vec::new();
            for edge in graph.edges() {
                // Lifecycle metadata is an assessment record, not its own consumer.
                if seen.contains(&edge.to)
                    // Producers of a reached conclusion are alternative support,
                    // not consumers of the changed upstream premise.
                    && !matches!(edge.provenance.field.as_str(), "/conclusion_statement_id" | "/output_statement_id")
                    && !seen.contains(&edge.from)
                    && edge.from != declaring_attempt
                    && (!edge.from.starts_with("attempts:") || attempt_use(&edge.provenance.field))
                {
                    next.push((edge.from.clone(), edge.to.clone(), None));
                }
            }
            for (consumer, source) in &imports {
                // A producer is an import-discovery source even when only its
                // conclusion is reached. It is not thereby an affected consumer.
                let parent = if seen.contains(source) {
                    Some(source)
                } else {
                    producer_conclusions
                        .get(source)
                        .filter(|conclusion| seen.contains(*conclusion))
                };
                if let Some(parent) = parent.filter(|_| !seen.contains(consumer)) {
                    next.push((consumer.clone(), parent.clone(), Some(source.clone())));
                }
            }
            for key in &seen {
                if let Some(node) = graph.nodes().get(key).filter(|n| n.kind == "arguments")
                    && let Some(id) = node.content["conclusion_statement_id"].as_str()
                {
                    let target = format!("statements:{id}");
                    if !seen.contains(&target) {
                        next.push((target, key.clone(), None));
                    }
                }
            }
            // Imported results can bypass an argument's declared premise list.
            for key in &seen {
                if let Some(node) = graph.nodes().get(key).filter(|n| n.kind == "results")
                    && let Some(argument) = node.content["argument_id"]
                        .as_str()
                        .and_then(|id| corpus.get("arguments", id))
                    && let Some(id) = argument.fields["conclusion_statement_id"].as_str()
                {
                    let target = format!("statements:{id}");
                    if !seen.contains(&target) {
                        next.push((target, key.clone(), None));
                    }
                }
            }
            if next.is_empty() {
                break;
            }
            for (key, parent, import_source) in next {
                if seen.insert(key.clone()) {
                    if let Some(source) = import_source {
                        import_sources.insert(key.clone(), source);
                    }
                    via.insert(key, parent);
                }
            }
        }
        if !seeds
            .iter()
            .chain(seen.iter())
            .any(|key| ids.iter().any(|id| key == &format!("statements:{id}")))
        {
            continue;
        }
        let mut dispositions = BTreeSet::new();
        for d in change["reassessments"].as_array().into_iter().flatten() {
            let consumer = text(d, "consumer");
            if !seen.contains(consumer)
                || seeds.contains(consumer)
                || !dispositions.insert(consumer)
            {
                return Err(format!(
                    "revision reassessment names duplicate or unaffected consumer: {consumer}"
                ));
            }
        }
        let consumers: Vec<_> = seen.difference(&seeds).map(|key| {
            let disposition = change["reassessments"].as_array().into_iter().flatten().find(|d| d["consumer"].as_str() == Some(key));
            json!({"consumer":key,"via":via.get(key),"import_source":import_sources.get(key),"disposition":disposition.map_or("pending", |d| text(d,"disposition")),"reason":disposition.map(|d| &d["reason"])})
        }).collect();
        out.push(json!({"attempt_id":attempt.fields["id"],"change":change,"consumers":consumers,"boundary":"potential explicit downstream uses and source-level Lean imports (not proof-use evidence); pending reassessment does not invalidate any formal theorem or accept a judgment"}));
    }
    Ok(out)
}

pub fn lines(current: &[Value], impacts: &[Value]) -> Vec<String> {
    let mut lines = Vec::new();
    for c in current {
        lines.push(format!(
            "Current recorded assessment [{}; {}]: {}",
            text(c, "review"),
            text(c, "publication"),
            text(c, "assessment")
        ));
        lines.push(format!(
            "  scope: {}; reviewed revision: {}; evidence: {}",
            text(c, "scope"),
            text(c, "reviewed_revision"),
            text(c, "note")
        ));
        lines.push(format!(
            "  review/publication evidence: {}",
            text(c, "evidence")
        ));
        lines.push(format!("  supersedes: {}", text(c, "supersedes")));
        lines.push(format!("  next test: {}", text(c, "next_test")));
    }
    for impact in impacts {
        lines.push(format!(
            "Declared {} revision {} — downstream reassessment (formal validity unchanged):",
            text(&impact["change"], "kind"),
            text(&impact["change"], "revision")
        ));
        lines.push(format!(
            "  change: {}; prior evidence: {}",
            text(&impact["change"], "reason"),
            text(&impact["change"], "previous")
        ));
        for consumer in impact["consumers"].as_array().into_iter().flatten() {
            lines.push(format!(
                "  {}: {}{}",
                text(consumer, "consumer"),
                text(consumer, "disposition"),
                consumer["reason"]
                    .as_str()
                    .map(|s| format!(" — {s}"))
                    .unwrap_or_default()
            ));
        }
    }
    lines
}
