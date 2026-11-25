//! Question entry point to the statement synthesis. Current judgments and earlier
//! investigations retain their provenance even when they share a topic.
use super::retrieval::{Query, words};
use crate::Corpus;
use rusqlite::{Connection, params};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

fn expression(query: &Query) -> Option<String> {
    let terms = query.fts_expression()?;
    // Preserve adjacent content words such as "actual recipient". Joining across
    // stop words would manufacture phrases that the user did not write.
    let lower = query.text.to_lowercase();
    let tokens = words(&lower);
    let indexed: BTreeSet<_> = query
        .items
        .iter()
        .map(|item| item.text.to_lowercase())
        .collect();
    let mut phrases = BTreeSet::new();
    for width in [2, 3] {
        for phrase in tokens.windows(width) {
            if phrase.iter().all(|token| indexed.contains(*token)) {
                phrases.insert(format!("\"{}\"", phrase.join(" ")));
            }
        }
    }
    Some(
        std::iter::once(terms)
            .chain(phrases)
            .collect::<Vec<_>>()
            .join(" OR "),
    )
}

fn targets(corpus: &Corpus, ids: &Value) -> Vec<Value> {
    ids.as_array().into_iter().flatten().filter_map(|id| {
        let id = id.as_str()?;
        let statement = &corpus.get("statements", id)?.fields;
        Some(json!({"id":id, "label":statement.get("label").or_else(||statement.get("paraphrase")),
            "paraphrase":statement.get("paraphrase")}))
    }).collect()
}

fn string<'a>(entry: &'a Value, key: &str) -> &'a str {
    entry[key].as_str().unwrap_or_default()
}

/// One search document per attempt. Only the selected fields of a current
/// assessment are indexed; a hit in its superseded handoff cannot promote it.
pub fn matches(corpus: &Corpus, question: &str) -> rusqlite::Result<Vec<Value>> {
    let query = Query::parse(question);
    let Some(terms) = expression(&query) else {
        return Ok(Vec::new());
    };
    let db = Connection::open_in_memory()?;
    db.execute_batch(
        "CREATE VIRTUAL TABLE findings USING fts5(
        id UNINDEXED, scope, finding, targets, tokenize='porter unicode61')",
    )?;
    let mut insert = db.prepare("INSERT INTO findings VALUES (?1, ?2, ?3, ?4)")?;
    let mut entries = BTreeMap::new();
    for attempt in corpus.entries("attempts") {
        let a = &attempt.fields;
        let mut entry = if let Some(current) = a.get("current_assessment") {
            let mut current = current.clone();
            current["kind"] = json!("current_assessment");
            current
        } else {
            json!({"kind":"prior_investigation", "scope":a.get("label"),
                "statement_ids":a.get("statement_ids"), "summary":a.get("summary"),
                "blocker":a.get("blocker"), "outcome":a.get("outcome"), "date":a.get("date")})
        };
        let statements = targets(corpus, &entry["statement_ids"]);
        let labels = statements
            .iter()
            .map(|s| string(s, "paraphrase"))
            .collect::<Vec<_>>()
            .join("\n");
        let scope = if entry["kind"] == "prior_investigation" {
            format!("{} {}", string(&entry, "scope"), attempt.path)
        } else {
            string(&entry, "scope").to_owned()
        };
        let finding = entry
            .get("assessment")
            .or_else(|| entry.get("summary"))
            .and_then(Value::as_str);
        let id = a["id"].as_str().expect("loaded attempt ID");
        insert.execute(params![id, scope, finding, labels])?;
        entry["targets"] = json!(statements);
        entry["attempt_id"] = json!(id);
        entry["path"] = json!(attempt.path);
        entries.insert(id, entry);
    }
    let mut search = db.prepare(
        "SELECT id, bm25(findings,0,2,1,2) FROM findings
        WHERE findings MATCH ?1 ORDER BY 2, id",
    )?;
    let rows = search.query_map([terms], |row| {
        Ok((row.get::<_, String>(0)?, -row.get::<_, f64>(1)?))
    })?;
    let mut ranked = Vec::new();
    for row in rows {
        let (id, score) = row?;
        let entry = entries.remove(id.as_str()).expect("indexed attempt");
        ranked.push((score, entry));
    }
    // Prefer an explicitly scoped judgment when it is a comparably close
    // text match. A directly relevant older study outranks incidental current
    // references. BM25 here determines navigation only.
    if let Some(best) = ranked.first().map(|(score, _)| *score) {
        let close = ranked.partition_point(|(score, _)| *score >= best * 0.7);
        ranked[..close].sort_by_key(|(_, r)| r["kind"] != "current_assessment");
    }
    Ok(ranked.into_iter().map(|(_, entry)| entry).collect())
}

fn earlier_excerpt<'a>(text: &'a str, query: &Query) -> &'a str {
    // A whole recorded sentence or paragraph retains its qualifiers. Do not
    // glue fragments from different judgments together.
    text.split_inclusive(['.', '!', '?', '\n'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .max_by_key(|s| {
            query
                .content_coverage(&query.matched(s, &BTreeMap::new()))
                .0
        })
        .unwrap_or(text)
}

pub fn render(question: &str, entries: &[Value], limit: usize) -> String {
    let mut lines = vec![format!("Research question: {question}")];
    let Some(first) = entries.first() else {
        lines.push(
            "No matching assessment or investigation. Search notes with truth brief --question."
                .into(),
        );
        return lines.join("\n");
    };
    let query = Query::parse(question);
    for (index, entry) in entries.iter().take(limit).enumerate() {
        let field = |key| string(entry, key);
        let current = entry["kind"] == "current_assessment";
        let disposition = if current {
            format!("{}; {}", field("review"), field("publication"))
        } else {
            "earlier investigation; current assessment unrecorded".to_owned()
        };
        lines.push(format!("\n{} [{}]", field("scope"), disposition));
        if index == 0 {
            if current {
                lines.push(field("assessment").to_owned());
                lines.push(format!("Next test: {}", field("next_test")));
                lines.push(format!(
                    "Source: {} (assessment revision {})",
                    field("note"),
                    field("reviewed_revision")
                ));
            } else {
                lines.push(format!(
                    "From the recorded finding: {}",
                    earlier_excerpt(field("summary"), &query)
                ));
                if !field("blocker").is_empty() {
                    lines.push(format!("Recorded limitation: {}", field("blocker")));
                }
            }
        }
        lines.push(format!(
            "{} · truth inspect {}",
            field("path"),
            field("attempt_id")
        ));
    }
    let mut candidates = first["targets"].as_array().cloned().unwrap_or_default();
    candidates.sort_by_cached_key(|s| {
        std::cmp::Reverse(
            query
                .content_coverage(&query.matched(string(s, "paraphrase"), &BTreeMap::new()))
                .0,
        )
    });
    let total = candidates.len();
    for s in candidates.iter().take(4) {
        lines.push(format!(
            "  {} — truth synthesis {}",
            super::retrieval::excerpt(string(s, "label"), 90),
            string(s, "id")
        ));
    }
    if total > 4 {
        lines.push(format!(
            "{} additional propositions in this record (--json).",
            total - 4
        ));
    }
    if entries.len() > limit {
        lines.push(format!(
            "\n{} further matches available in --json.",
            entries.len() - limit
        ));
    }
    lines.join("\n")
}

pub fn report(corpus: &Corpus, question: &str, limit: usize) -> Result<(Value, String), String> {
    let entries = matches(corpus, question).map_err(|err| err.to_string())?;
    let text = render(question, &entries, limit);
    Ok((
        json!({"schema_version":1,"mode":"question","question":question,"matches":entries,
        "input_identity":corpus.input_identity()}),
        text,
    ))
}
