//! Question entry point to the statement synthesis. Search only explicitly scoped
//! judgments. A word match in historical work never promotes it to a current finding.
use super::retrieval::{Query, words};
use crate::Corpus;
use rusqlite::{Connection, params};
use serde_json::{Value, json};
use std::collections::BTreeSet;

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

fn targets(corpus: &Corpus, current: &Value) -> Vec<Value> {
    current["statement_ids"].as_array().into_iter().flatten().filter_map(|id| {
        let id = id.as_str()?;
        let statement = corpus.get("statements", id)?;
        Some(json!({"id":id, "label":statement.fields.get("paraphrase").or_else(|| statement.fields.get("label"))}))
    }).collect()
}

/// This transient FTS table is small (one row per current assessment). In
/// particular, asking a question here never indexes the note archive or computes
/// a frontier for an ambiguously matched proposition.
pub fn matches(corpus: &Corpus, question: &str) -> rusqlite::Result<Vec<Value>> {
    let Some(terms) = expression(&Query::parse(question)) else {
        return Ok(Vec::new());
    };
    let db = Connection::open_in_memory()?;
    db.execute_batch(
        "CREATE VIRTUAL TABLE findings USING fts5(
        id UNINDEXED, scope, assessment, targets, tokenize='porter unicode61')",
    )?;
    let mut insert = db.prepare("INSERT INTO findings VALUES (?1, ?2, ?3, ?4)")?;
    for attempt in corpus.entries("attempts") {
        let Some(current) = attempt.fields.get("current_assessment") else {
            continue;
        };
        let labels = targets(corpus, current)
            .iter()
            .filter_map(|s| s["label"].as_str())
            .collect::<Vec<_>>()
            .join("\n");
        insert.execute(params![
            attempt.fields["id"].as_str(),
            current["scope"].as_str(),
            current["assessment"].as_str(),
            labels
        ])?;
    }
    let mut search = db.prepare(
        "SELECT id FROM findings WHERE findings MATCH ?1
        ORDER BY bm25(findings, 0, 2, 1, 2), id",
    )?;
    let ids = search.query_map([terms], |row| row.get::<_, String>(0))?;
    ids.map(|id| {
        let id = id?;
        let attempt = corpus.get("attempts", &id).expect("indexed attempt");
        let mut entry = attempt.fields["current_assessment"].clone();
        entry["targets"] = json!(targets(corpus, &entry));
        entry["attempt_id"] = json!(id);
        entry["path"] = json!(attempt.path);
        Ok(entry)
    })
    .collect()
}

pub fn render(question: &str, entries: &[Value], limit: usize) -> String {
    let mut lines = vec![format!("Research question: {question}")];
    if entries.is_empty() {
        lines.push("No scoped assessment matched these words. Use truth brief --question for notes and earlier investigations.".to_owned());
    } else {
        lines.push("Matching recorded judgments, ordered by wording. Each applies within its stated scope.".to_owned());
        for entry in entries.iter().take(limit) {
            let field = |key: &str| entry[key].as_str().unwrap_or_default();
            lines.push(format!(
                "\n{} [{}; {}]\n{}\nNext test: {}\nSource: {} (assessment revision {})",
                field("scope"),
                field("review"),
                field("publication"),
                field("assessment"),
                field("next_test"),
                field("note"),
                field("reviewed_revision")
            ));
            for target in entry["targets"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "  {} — truth synthesis {}",
                    target["label"].as_str().unwrap_or_default(),
                    target["id"].as_str().unwrap_or_default()
                ));
            }
        }
        if entries.len() > limit {
            lines.push(format!(
                "\n{} further matches available in --json.",
                entries.len() - limit
            ));
        }
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
