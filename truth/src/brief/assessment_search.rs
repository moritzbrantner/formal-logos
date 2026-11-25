//! Question entry point to the statement synthesis. Current judgments and earlier
//! investigations retain their provenance even when they share a topic.
use super::retrieval::{Query, words};
use crate::Corpus;
use rusqlite::{Connection, params};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// Keep adjacent words from the user's question without inventing a phrase
/// across dropped words. Reuse the same phrases to locate note passages.
fn phrases(query: &Query) -> BTreeSet<String> {
    let lower = query.text.to_lowercase();
    let tokens = words(&lower);
    let indexed: BTreeSet<_> = query
        .items
        .iter()
        .filter(|item| matches!(item.kind, "word" | "identifier"))
        .map(|item| item.text.to_lowercase())
        .collect();
    [2, 3]
        .into_iter()
        .flat_map(|width| tokens.windows(width))
        .filter(|phrase| phrase.iter().all(|token| indexed.contains(*token)))
        .map(|phrase| phrase.join(" "))
        .collect()
}

fn expression(query: &Query) -> Option<String> {
    // FTS's Porter tokenizer folds inflections. Prefixing a cropped stem
    // would also retrieve different words such as "temporary" for "temporally".
    let terms: Vec<_> = query
        .items
        .iter()
        .filter(|item| matches!(item.kind, "word" | "identifier" | "symbol"))
        .map(|item| format!("\"{}\"", item.text.replace('"', "\"\"")))
        .collect();
    (!terms.is_empty()).then(|| {
        terms
            .into_iter()
            .chain(phrases(query).into_iter().map(|p| format!("\"{p}\"")))
            .collect::<Vec<_>>()
            .join(" OR ")
    })
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

/// Score the sentences a researcher can actually read. File paths and linked
/// statement labels identify records but cannot supply a finding for this question.
fn searchable(text: &str) -> String {
    text.split_whitespace()
        .filter(|word| {
            !word.contains("://")
                && !word.starts_with("www.")
                && !word.contains(".md")
                && !word.contains(".json")
                && !word.contains(".lean")
                && !word.contains("corpus/")
                && !word.contains("docs/")
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Keep punctuation in the cited sentence and periods within names and paths.
fn sentences(text: &str) -> impl Iterator<Item = &str> {
    let mut start = 0;
    text.char_indices().filter_map(move |(index, c)| {
        let end = index + c.len_utf8();
        let boundary = c == '\n'
            || end == text.len()
            || (matches!(c, '.' | '!' | '?')
                && text[end..].starts_with(char::is_whitespace)
                && !["e.g.", "i.e.", "cf."]
                    .iter()
                    .any(|abbr| text[..end].ends_with(abbr)));
        if !boundary {
            return None;
        }
        let sentence = text[start..end].trim();
        start = end;
        (!sentence.is_empty()).then_some(sentence)
    })
}

pub fn matches(corpus: &Corpus, question: &str) -> rusqlite::Result<Vec<Value>> {
    let query = Query::parse(question);
    let Some(terms) = expression(&query) else {
        return Ok(Vec::new());
    };
    let db = Connection::open_in_memory()?;
    db.execute_batch(
        "CREATE VIRTUAL TABLE findings USING fts5(
        id UNINDEXED, scope, finding, passage UNINDEXED, tokenize='porter unicode61');
         CREATE VIRTUAL TABLE documents USING fts5(id UNINDEXED, scope, finding, tokenize='porter unicode61')",
    )?;
    let mut insert = db.prepare("INSERT INTO findings VALUES (?1, ?2, ?3, ?4)")?;
    let mut document = db.prepare("INSERT INTO documents VALUES (?1, ?2, ?3)")?;
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
        let id = a["id"].as_str().expect("loaded attempt ID");
        let scope = searchable(string(&entry, "scope"));
        let finding = entry
            .get("assessment")
            .or_else(|| entry.get("summary"))
            .and_then(Value::as_str)
            .unwrap_or_default();
        let mut body = String::new();
        for passage in sentences(finding) {
            let prose = searchable(passage);
            if words(&prose).len() >= 3 && !prose.ends_with(" unchanged.") {
                body.push_str(&prose);
                body.push(' ');
                insert.execute(params![id, scope, prose, passage])?;
            }
        }
        document.execute(params![id, scope, body])?;
        entry["targets"] = json!(targets(corpus, &entry["statement_ids"]));
        entry["attempt_id"] = json!(id);
        entry["path"] = json!(attempt.path);
        entries.insert(id, entry);
    }
    // A passing reference in one sentence can have high BM25. Require both
    // that passage and the record's overall subject to support its position.
    let mut records =
        db.prepare("SELECT id, -bm25(documents,0,1,1) FROM documents WHERE documents MATCH ?1")?;
    let document_scores: BTreeMap<String, f64> = records
        .query_map([&terms], |row| Ok((row.get(0)?, row.get(1)?)))?
        .collect::<rusqlite::Result<_>>()?;
    let mut search = db.prepare(
        "SELECT id, bm25(findings,0,0.6,1,0), scope, finding, passage FROM findings
        WHERE findings MATCH ?1 ORDER BY 2, rowid",
    )?;
    let mut rows = search.query([terms])?;
    let mut ranked = Vec::new();
    while let Some(row) = rows.next()? {
        let id: String = row.get(0)?;
        if !entries.contains_key(id.as_str()) {
            continue;
        }
        let scope: String = row.get(2)?;
        let finding: String = row.get(3)?;
        let matched = query.matched(&finding, &BTreeMap::new());
        let (covered, total) = query.content_coverage(&matched);
        let in_scope = query.matched(&scope, &BTreeMap::new());
        if covered == 0 || (total >= 3 && covered.max(query.content_coverage(&in_scope).0) < 2) {
            continue;
        }
        let mut entry = entries.remove(id.as_str()).expect("indexed attempt");
        entry["matched_terms"] = json!(super::retrieval::matched_items(&query, &matched));
        entry["passage"] = json!(row.get::<_, String>(4)?);
        ranked.push((-row.get::<_, f64>(1)? * document_scores[&id], entry));
    }
    ranked.sort_by(|(a, _), (b, _)| b.total_cmp(a));
    // Among comparably close textual matches, lead with a scoped assessment.
    if let Some(best) = ranked.first().map(|(score, _)| *score) {
        let close = ranked.partition_point(|(score, _)| *score >= best * 0.7);
        ranked[..close].sort_by_key(|(_, r)| r["kind"] != "current_assessment");
    }
    Ok(ranked.into_iter().map(|(_, entry)| entry).collect())
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
        if index == 0 && current {
            lines.push(field("assessment").to_owned());
            lines.push(format!("Next test: {}", field("next_test")));
            lines.push(format!(
                "Source: {} (assessment revision {})",
                field("note"),
                field("reviewed_revision")
            ));
        } else {
            lines.push(format!("From the recorded finding: {}", field("passage")));
            if index == 0 && !field("blocker").is_empty() {
                lines.push(format!("Recorded limitation: {}", field("blocker")));
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

/// Look up a literal question phrase in the note archive when the leading
/// attempt misses it. Notes retain their section locator and research status.
pub fn report_for_root(
    root: &std::path::Path,
    corpus: &Corpus,
    question: &str,
    limit: usize,
) -> Result<(Value, String), String> {
    let (mut report, mut text) = report(corpus, question, limit)?;
    let query = Query::parse(question);
    let requested = phrases(&query);
    let leading = &report["matches"][0];
    let leading_text = [string(leading, "scope"), string(leading, "passage")]
        .join(" ")
        .to_lowercase();
    let leading_words = words(&leading_text).join(" ");
    if !requested.is_empty()
        && !requested.iter().any(|p| leading_words.contains(p))
        && let Some(note) = note_passage(root, &query, &requested)?
    {
        let excerpt = format!(
            "\n\nResearch note · {}\n{}\n{} (line {})",
            string(&note, "heading"),
            string(&note, "passage"),
            string(&note, "section"),
            note["line"]
        );
        text.insert_str(text.find('\n').unwrap_or(text.len()), &excerpt);
        report["note_match"] = note;
    }
    Ok((report, text))
}

fn note_passage(
    root: &std::path::Path,
    query: &Query,
    requested: &BTreeSet<String>,
) -> Result<Option<Value>, String> {
    let mut best = None;
    for path in crate::notes::inputs(root)? {
        let raw = std::fs::read_to_string(root.join(&path)).map_err(|e| format!("{path}: {e}"))?;
        // Avoid parsing the archive's unrelated notes for a fallback passage.
        let flat = raw
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .to_lowercase();
        if !requested.iter().any(|p| flat.contains(p)) {
            continue;
        }
        let note = crate::notes::parse(&path, &raw);
        for section in &note.sections {
            for (line, paragraph) in
                super::retrieval::paragraphs(&section.body, super::retrieval::body_line(section))
            {
                let flat = paragraph.split_whitespace().collect::<Vec<_>>().join(" ");
                for sentence in sentences(&flat) {
                    let plain = searchable(sentence).to_lowercase();
                    let hits = requested.iter().filter(|p| plain.contains(*p)).count();
                    if hits == 0 {
                        continue;
                    }
                    let coverage = |s| {
                        query
                            .content_coverage(&query.matched(s, &BTreeMap::new()))
                            .0
                    };
                    let score = (
                        hits,
                        coverage(&plain),
                        coverage(&flat),
                        std::cmp::Reverse(flat.len()),
                    );
                    if best.as_ref().is_none_or(|(prior, _)| score > *prior) {
                        best = Some((
                            score,
                            json!({"kind":"research_note","section":note.key(section),
                            "heading":section.heading, "line":line, "passage": if flat.chars().count() <= 1100 {flat.as_str()} else {sentence}}),
                        ));
                    }
                }
            }
        }
    }
    Ok(best.map(|(_, hit)| hit))
}
