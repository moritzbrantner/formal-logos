//! Retrieve registered Lean results independently of research notes.
use super::retrieval::{LeanSource, Query, expanded_identifiers, qualified_declarations};
use crate::{
    Corpus, Record,
    context::{comparator_config, module_path},
    synthesis::result_witness,
};
use rusqlite::{Connection, params};
use serde::Serialize;
use serde_json::{Value, json};
use std::{cmp::Reverse, collections::BTreeMap, path::Path};

fn field<'a>(record: &'a Record, key: &str) -> &'a str {
    record
        .fields
        .get(key)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn exact(record: &Record, query: &str) -> bool {
    let theorem = field(record, "theorem");
    [
        field(record, "id"),
        field(record, "legacy_id"),
        theorem,
        theorem.rsplit('.').next().unwrap_or_default(),
    ]
    .contains(&query)
}

fn witness(root: &Path, corpus: &Corpus, result: &Record) -> Value {
    let mut evidence = result_witness(root, result);
    if let Some(label) = result.fields.get("label") {
        evidence["result_label"] = label.clone();
    }
    if let Some(argument) = corpus.get("arguments", field(result, "argument_id")) {
        evidence["argument_label"] = argument.fields["label"].clone();
        evidence["argument_meaning"] = argument.fields["meaning"].clone();
        for key in [
            "conclusion_statement_id",
            "premise_statement_ids",
            "commitment_statement_ids",
        ] {
            if let Some(value) = argument.fields.get(key) {
                evidence[key] = value.clone();
            }
        }
    }
    evidence
}

#[derive(Serialize)]
struct AttemptCitation<'a> {
    attempt_id: &'a str,
    path: &'a str,
}

fn citation_coverage(query: &Query, corpus: &Corpus, result: &Record) -> (usize, usize) {
    let argument = corpus.get("arguments", field(result, "argument_id"));
    let conclusion =
        argument.and_then(|a| corpus.get("statements", field(a, "conclusion_statement_id")));
    let labels = [
        field(result, "label"),
        argument.map_or("", |a| field(a, "label")),
        conclusion.map_or("", |s| field(s, "label")),
    ]
    .join(" ");
    let aliases = BTreeMap::new();
    let coverage = |text: &str| query.content_coverage(&query.matched(text, &aliases)).0;
    (
        coverage(&labels),
        coverage(conclusion.map_or("", |s| field(s, "paraphrase"))),
    )
}

/// Resolve only canonical result IDs explicitly listed in the displayed
/// attempts' evidence. These citations belong to the attempt as a whole.
pub(super) fn cited_results(
    root: &Path,
    corpus: &Corpus,
    attempts: &[Value],
    query: &Query,
    direct: &mut [Value],
    limit: usize,
) -> Vec<Value> {
    let mut citations: BTreeMap<_, Vec<AttemptCitation<'_>>> = BTreeMap::new();
    let mut cited_in_order = Vec::new();
    for matched in attempts.iter().take(limit) {
        let Some(attempt_id) = matched["attempt_id"].as_str() else {
            continue;
        };
        let Some(attempt) = corpus.get("attempts", attempt_id) else {
            continue;
        };
        let mut evidence: Vec<_> = attempt
            .fields
            .get("evidence")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .filter_map(|id| corpus.get("results", id))
            .collect();
        if matched["kind"] == "current_assessment"
            && let Some(targets) = matched["statement_ids"].as_array()
        {
            let in_scope = |result: &Record| {
                corpus
                    .get("arguments", field(result, "argument_id"))
                    .and_then(|a| a.fields.get("conclusion_statement_id"))
                    .is_some_and(|id| targets.contains(id))
            };
            evidence.sort_by_cached_key(|result| !in_scope(result));
            // Lead with the closest scoped citation; keep the remaining
            // evidence in the investigator's order within each group.
            if let Some((index, _)) = evidence
                .iter()
                .take_while(|result| in_scope(result))
                .enumerate()
                .min_by_key(|(_, result)| Reverse(citation_coverage(query, corpus, result)))
            {
                evidence[..=index].rotate_right(1);
            }
        }
        for result in evidence {
            let sources = citations.entry(field(result, "id")).or_default();
            if sources.is_empty() {
                cited_in_order.push(result);
            }
            if sources
                .last()
                .is_none_or(|source| source.attempt_id != attempt_id)
            {
                sources.push(AttemptCitation {
                    attempt_id,
                    path: &attempt.path,
                });
            }
        }
    }
    for result in direct {
        let id = result["id"].as_str().unwrap_or_default();
        if let Some(sources) = citations.remove(id) {
            result["cited_by"] = json!(sources);
        }
    }
    cited_in_order
        .into_iter()
        .filter_map(|result| {
            citations
                .remove(field(result, "id"))
                .map(|sources| (result, sources))
        })
        .take(limit)
        .map(|(result, sources)| {
            let mut evidence = witness(root, corpus, result);
            evidence["cited_by"] = json!(sources);
            evidence
        })
        .collect()
}

pub(super) fn qualified_name(query: &str) -> bool {
    let name = query.trim().trim_matches('`');
    name.contains('.')
        && name.split('.').all(|part| {
            part.starts_with(|c: char| c.is_alphabetic() || c == '_')
                && part
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        })
}

#[derive(Serialize)]
pub(super) struct ComparatorCompanion<'a> {
    pub result_id: &'a str,
    pub result_label: &'a str,
    pub comparator_config: &'a str,
    pub challenge_path: Option<String>,
    pub challenge_line: Option<usize>,
}

/// Match the full names configured for each registered result. This reports
/// the configured scope only. A companion has no primary result status here.
pub(super) fn comparator_companions<'a>(
    root: &Path,
    corpus: &'a Corpus,
    query: &str,
) -> Vec<ComparatorCompanion<'a>> {
    let name = query.trim().trim_matches('`');
    let mut configs = BTreeMap::new();
    let mut challenge_lines = BTreeMap::new();
    corpus
        .records_by_id("results")
        .filter_map(|(id, result)| {
            let path = field(result, "comparator_config");
            if path.is_empty() || field(result, "theorem") == name {
                return None;
            }
            let config = configs
                .entry(path)
                .or_insert_with(|| comparator_config(root, path));
            if !config
                .get("theorem_names")?
                .as_array()?
                .iter()
                .any(|item| item == name)
            {
                return None;
            }
            let challenge_path = config
                .get("challenge_module")
                .and_then(Value::as_str)
                .filter(|module| !module.is_empty())
                .map(module_path);
            let challenge_line = challenge_path.as_ref().and_then(|path| {
                *challenge_lines.entry(path.clone()).or_insert_with(|| {
                    let source = std::fs::read_to_string(root.join(path)).ok()?;
                    qualified_declarations(&source)
                        .into_iter()
                        .find_map(|(declaration, line)| (declaration == name).then_some(line + 1))
                })
            });
            Some(ComparatorCompanion {
                result_id: id,
                result_label: field(result, "label"),
                comparator_config: path,
                challenge_path: challenge_path.map(|path| path.to_string_lossy().into_owned()),
                challenge_line,
            })
        })
        .collect()
}

/// Local library theorems and definitions can be inspected by their qualified
/// name even when nobody has registered them as arguments in the graph.
pub(super) fn library_declaration(root: &Path, query: &str) -> Option<Value> {
    let name = query.trim().trim_matches('`');
    let (path, line, source) = LeanSource::new(root).implementation_block(name)?;
    Some(json!({"name":name,"path":path,"line":line,"source":source}))
}

/// Include reusable implementations that are not already displayed as a result.
pub(super) fn library_candidates(
    root: &Path,
    corpus: &Corpus,
    query: &Query,
    shown: &[Value],
    cited: &[Value],
    limit: usize,
) -> Vec<Value> {
    let excluded = shown
        .iter()
        .chain(cited)
        .filter_map(|entry| entry["theorem"].as_str().map(str::to_owned))
        .collect();
    let mut candidates = LeanSource::new(root).theorem_candidates(query, &excluded, limit);
    for candidate in &mut candidates {
        let name = candidate["name"].as_str().unwrap_or_default();
        let ids: Vec<_> = corpus
            .records_by_id("results")
            .filter(|(_, record)| field(record, "theorem") == name)
            .map(|(id, _)| id)
            .collect();
        candidate["registered_result_ids"] = json!(ids);
    }
    candidates
}

/// Prefer an exact formal identifier. For ordinary questions search the theorem
/// names and registered argument/conclusion labels. Read Lean only for the
/// selected witnesses. Notes and attempts never enter the candidate set.
pub(super) fn find(
    root: &Path,
    corpus: &Corpus,
    query: &Query,
    limit: usize,
) -> rusqlite::Result<Vec<Value>> {
    let token = query.text.trim().trim_matches('`');
    if token.is_empty() || limit == 0 {
        return Ok(Vec::new());
    }
    let qualified = qualified_name(token);
    let exact_hits: Vec<_> = corpus
        .records_by_id("results")
        .filter(|(_, record)| {
            if qualified {
                field(record, "theorem") == token
            } else {
                exact(record, token)
            }
        })
        .take(limit)
        .map(|(_, record)| witness(root, corpus, record))
        .collect();
    if !exact_hits.is_empty() || qualified {
        return Ok(exact_hits);
    }
    let Some(terms) = super::assessment_search::expression(query) else {
        return Ok(Vec::new());
    };
    let db = Connection::open_in_memory()?;
    db.execute_batch(
        "CREATE VIRTUAL TABLE proofs USING fts5(
        id UNINDEXED, name, argument, conclusion_label, paraphrase, description, tokenize='porter unicode61'
    )",
    )?;
    let mut insert = db.prepare("INSERT INTO proofs VALUES (?1,?2,?3,?4,?5,?6)")?;
    for (id, result) in corpus.records_by_id("results") {
        let Some(argument) = corpus.get("arguments", field(result, "argument_id")) else {
            continue;
        };
        let conclusion = corpus.get("statements", field(argument, "conclusion_statement_id"));
        let name = expanded_identifiers(&format!(
            "{} {}",
            field(result, "theorem"),
            field(result, "legacy_id")
        ));
        insert.execute(params![
            id,
            name,
            field(argument, "label"),
            conclusion.map(|s| field(s, "label")).unwrap_or_default(),
            conclusion
                .map(|s| field(s, "paraphrase"))
                .unwrap_or_default(),
            field(result, "description")
        ])?;
    }
    let mut ranked = db.prepare(
        "SELECT id, name || ' ' || argument || ' ' || conclusion_label || ' ' || paraphrase || ' ' || description
        FROM proofs WHERE proofs MATCH ?1 ORDER BY bm25(proofs,0,2,2,2,1,0.5), id",
    )?;
    let mut rows = ranked.query([terms])?;
    let mut hits = Vec::new();
    let aliases = BTreeMap::new();
    while let Some(row) = rows.next()? {
        let body: String = row.get(1)?;
        if !query.substantial(&query.matched(&body, &aliases)) {
            continue;
        }
        let id: String = row.get(0)?;
        let result = corpus.get("results", &id).expect("indexed result");
        hits.push(witness(root, corpus, result));
        if hits.len() == limit {
            break;
        }
    }
    Ok(hits)
}
