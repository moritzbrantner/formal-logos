//! Retrieve registered Lean results independently of research notes.
use super::retrieval::{LeanSource, Query};
use crate::{Corpus, Record, synthesis::result_witness};
use rusqlite::{Connection, params};
use serde_json::{Value, json};
use std::{collections::BTreeMap, path::Path};

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
    if let Some(argument) = corpus.get("arguments", field(result, "argument_id")) {
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

/// Local library theorems and definitions can be inspected by their qualified
/// name even when nobody has registered them as arguments in the graph.
pub(super) fn library_declaration(root: &Path, query: &str) -> Option<Value> {
    let name = query.trim().trim_matches('`');
    if !name.contains('.')
        || !name.split('.').all(|part| {
            !part.is_empty()
                && part
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        })
    {
        return None;
    }
    let (path, line, source) = LeanSource::new(root).qualified_block(name)?;
    Some(json!({"name":name,"path":path,"line":line,"source":source}))
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
    if token.is_empty() {
        return Ok(Vec::new());
    }
    let exact_hits: Vec<_> = corpus
        .records_by_id("results")
        .filter(|(_, record)| exact(record, token))
        .take(limit)
        .map(|(_, record)| witness(root, corpus, record))
        .collect();
    if !exact_hits.is_empty() {
        return Ok(exact_hits);
    }
    let Some(terms) = super::assessment_search::expression(query) else {
        return Ok(Vec::new());
    };
    let db = Connection::open_in_memory()?;
    db.execute_batch(
        "CREATE VIRTUAL TABLE proofs USING fts5(
        id UNINDEXED, name, argument, conclusion, tokenize='porter unicode61'
    )",
    )?;
    let mut insert = db.prepare("INSERT INTO proofs VALUES (?1,?2,?3,?4)")?;
    for (id, result) in corpus.records_by_id("results") {
        let Some(argument) = corpus.get("arguments", field(result, "argument_id")) else {
            continue;
        };
        let conclusion = corpus.get("statements", field(argument, "conclusion_statement_id"));
        let name = format!(
            "{} {}",
            field(result, "theorem"),
            field(result, "legacy_id")
        );
        insert.execute(params![
            id,
            name,
            field(argument, "label"),
            conclusion
                .map(|s| field(s, "paraphrase"))
                .unwrap_or_default()
        ])?;
    }
    let mut ranked = db.prepare(
        "SELECT id, name || ' ' || argument || ' ' || conclusion
        FROM proofs WHERE proofs MATCH ?1 ORDER BY bm25(proofs,0,2,2,1), id",
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
