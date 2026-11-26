//! Who worked on each proposition (owner direction, 2026-11-26).
//!
//! An attempt record may carry an appended `workers` list: one entry per
//! agent and role (`author`, `repair`, `review`) with its provider, model,
//! optional effort, date and optional PR. [`line`] renders one entry for the
//! dossier, context and brief views; [`report`] is the revisit query of
//! `truth workers`: for each statement with attempts, the latest attempt's
//! outcome and the models that authored attempts on it, so that work done by
//! one model can be revisited with another. It reads the attempt records and a
//! computed frontier only; it writes nothing and establishes nothing.

use crate::Corpus;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet};

type Record = Map<String, Value>;

/// One worker entry as text: `author codex/gpt-6.2-sol (high) 2026-11-26 PR-2020`.
pub fn line(worker: &Value) -> String {
    let field = |name: &str| worker.get(name).and_then(Value::as_str).unwrap_or_default();
    let mut text = format!("{} {}/{}", field("role"), field("provider"), field("model"));
    if !field("effort").is_empty() {
        text.push_str(&format!(" ({})", field("effort")));
    }
    for name in ["date", "pr"] {
        if !field(name).is_empty() {
            text.push(' ');
            text.push_str(field(name));
        }
    }
    text
}

/// The `workers` entries of an attempt, in recorded order.
pub fn entries(attempt: &Record) -> &[Value] {
    attempt
        .get("workers")
        .and_then(Value::as_array)
        .map_or(&[], Vec::as_slice)
}

/// The models recorded for `role` on an attempt.
fn models<'a>(attempt: &'a Record, role: &str) -> impl Iterator<Item = &'a str> {
    entries(attempt)
        .iter()
        .filter(move |worker| worker["role"] == role)
        .filter_map(|worker| worker["model"].as_str())
}

/// For each statement named in some attempt's `statement_ids`, the models
/// recorded as `author` on its attempts (empty when no attempt records one).
pub fn authors(corpus: &Corpus) -> BTreeMap<String, BTreeSet<String>> {
    let mut by_statement: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for attempt in corpus.records("attempts") {
        for id in attempt
            .get("statement_ids")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
        {
            by_statement
                .entry(id.to_owned())
                .or_default()
                .extend(models(attempt, "author").map(str::to_owned));
        }
    }
    by_statement
}

/// Whether `authored` is exactly `{model}`: the `--authored-only-by` test of
/// `truth workers` and `truth bottlenecks`.
pub fn authored_only_by<S: AsRef<str>>(authored: &BTreeSet<S>, model: &str) -> bool {
    authored.len() == 1 && authored.iter().all(|name| name.as_ref() == model)
}

/// The `truth workers` filters.
#[derive(Debug, Default, Clone)]
pub struct Filter {
    /// Keep statements whose recorded attempt authors are exactly this model.
    pub authored_only_by: Option<String>,
    /// Keep statements that are not closed in the computed frontier.
    pub open: bool,
}

/// For each statement with attempts: its latest attempt (by date, then id),
/// the models that authored or reviewed its attempts, how many attempts
/// record no author, and whether the computed frontier leaves it open.
/// Statements are listed by latest attempt, newest first.
pub fn report(
    corpus: &Corpus,
    closed: &BTreeMap<String, String>,
    reaching_root: &BTreeSet<String>,
    filter: &Filter,
) -> Value {
    let mut by_statement: BTreeMap<&str, Vec<&Record>> = BTreeMap::new();
    for attempt in corpus.records("attempts") {
        for id in attempt
            .get("statement_ids")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
        {
            by_statement.entry(id).or_default().push(attempt);
        }
    }
    let text = |record: &Record, field: &str| -> String {
        record
            .get(field)
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_owned()
    };
    let mut rows: Vec<Value> = Vec::new();
    for (id, attempts) in by_statement {
        let latest = attempts
            .iter()
            .max_by_key(|attempt| (text(attempt, "date"), text(attempt, "id")))
            .expect("a statement listed here has an attempt");
        let authored: BTreeSet<&str> = attempts.iter().flat_map(|a| models(a, "author")).collect();
        let reviewed: BTreeSet<&str> = attempts.iter().flat_map(|a| models(a, "review")).collect();
        let unrecorded = attempts
            .iter()
            .filter(|a| models(a, "author").next().is_none())
            .count();
        let open = !closed.contains_key(id);
        if filter.open && !open {
            continue;
        }
        if let Some(model) = &filter.authored_only_by
            && !authored_only_by(&authored, model)
        {
            continue;
        }
        rows.push(json!({
            "statement_id": id,
            "label": corpus.get("statements", id).map(|s| text(&s.fields, "label")),
            "open": open,
            "reaches_root": reaching_root.contains(id),
            "attempts": attempts.len(),
            "attempts_without_author": unrecorded,
            "latest_attempt": {
                "id": text(latest, "id"),
                "date": text(latest, "date"),
                "kind": text(latest, "kind"),
                "outcome": text(latest, "outcome"),
                "workers": entries(latest),
            },
            "authored_by": authored,
            "reviewed_by": reviewed,
        }));
    }
    rows.sort_by(|a, b| {
        let key = |row: &Value| {
            (
                row["latest_attempt"]["date"]
                    .as_str()
                    .unwrap_or_default()
                    .to_owned(),
                row["statement_id"].as_str().unwrap_or_default().to_owned(),
            )
        };
        key(b).cmp(&key(a))
    });
    json!({
        "filter": {"authored_only_by": filter.authored_only_by, "open": filter.open},
        "statements": rows,
    })
}

/// The text of [`report`]: one block per statement, uuids left for
/// `Aliases::humanize`.
pub fn format(report: &Value) -> String {
    let rows = report["statements"].as_array().cloned().unwrap_or_default();
    let mut filters = Vec::new();
    if let Some(model) = report["filter"]["authored_only_by"].as_str() {
        filters.push(format!("authored only by {model}"));
    }
    if report["filter"]["open"] == true {
        filters.push("open in the frontier".to_owned());
    }
    let mut lines = vec![format!(
        "Statements with attempts, latest attempt first ({}{}; attempt outcomes establish nothing):",
        rows.len(),
        if filters.is_empty() {
            String::new()
        } else {
            format!("; {}", filters.join(", "))
        }
    )];
    let names = |value: &Value| {
        let names: Vec<&str> = value
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        if names.is_empty() {
            "none recorded".to_owned()
        } else {
            names.join(", ")
        }
    };
    for row in &rows {
        let latest = &row["latest_attempt"];
        lines.push(format!(
            "  {} [{}{}]",
            row["statement_id"].as_str().unwrap_or_default(),
            if row["open"] == true {
                "open"
            } else {
                "closed"
            },
            if row["reaches_root"] == true {
                "; reaches root"
            } else {
                ""
            },
        ));
        lines.push(format!(
            "    latest attempt {} [{}; {}; {}]",
            latest["id"].as_str().unwrap_or_default(),
            latest["date"].as_str().unwrap_or_default(),
            latest["kind"].as_str().unwrap_or_default(),
            latest["outcome"].as_str().unwrap_or_default(),
        ));
        lines.push(format!(
            "    authored by: {}; reviewed by: {}; attempts without an author entry: {} of {}",
            names(&row["authored_by"]),
            names(&row["reviewed_by"]),
            row["attempts_without_author"],
            row["attempts"],
        ));
    }
    if rows.is_empty() {
        lines.push("  none".into());
    }
    lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_lines_omit_absent_optional_fields() {
        assert_eq!(
            line(
                &json!({"role": "author", "provider": "codex", "model": "gpt-6.2-sol",
                         "effort": "high", "date": "2026-11-26", "pr": "PR-2020"})
            ),
            "author codex/gpt-6.2-sol (high) 2026-11-26 PR-2020"
        );
        assert_eq!(
            line(
                &json!({"role": "repair", "provider": "claude", "model": "claude-opus-5-5",
                         "date": "2026-11-26"})
            ),
            "repair claude/claude-opus-5-5 2026-11-26"
        );
    }

    #[test]
    fn report_lists_latest_attempt_and_filters_by_sole_author_and_openness() {
        let root = std::env::temp_dir().join(format!("truth-workers-{}", std::process::id()));
        let attempts = root.join("corpus/attempts");
        std::fs::create_dir_all(&attempts).unwrap();
        let author = |model: &str| json!({"role": "author", "provider": "codex", "model": model, "date": "2026-11-26"});
        let review = json!({"role": "review", "provider": "codex", "model": "astra",
                            "date": "2026-11-26"});
        for (id, statements, date, outcome, workers) in [
            (
                "a1",
                json!(["S", "T"]),
                "2026-11-01",
                "failed",
                json!([author("sol")]),
            ),
            (
                "a2",
                json!(["S"]),
                "2026-11-20",
                "blocked",
                json!([author("sol"), review]),
            ),
            (
                "a3",
                json!(["T"]),
                "2026-11-25",
                "succeeded",
                json!([author("other")]),
            ),
            ("a4", json!(["U"]), "2026-11-02", "succeeded", Value::Null),
        ] {
            let mut record = json!({"id": id, "statement_ids": statements, "date": date,
                                    "kind": "derivation", "outcome": outcome});
            if !workers.is_null() {
                record["workers"] = workers;
            }
            std::fs::write(attempts.join(format!("{id}.json")), record.to_string()).unwrap();
        }
        let corpus = Corpus::load(&root).unwrap();
        let closed = BTreeMap::from([("T".to_owned(), "proved".to_owned())]);
        let reaching = BTreeSet::from(["S".to_owned()]);
        let all = report(&corpus, &closed, &reaching, &Filter::default());
        let ids: Vec<&str> = all["statements"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["statement_id"].as_str().unwrap())
            .collect();
        assert_eq!(ids, ["T", "S", "U"]);
        let s = &all["statements"][1];
        assert_eq!(s["latest_attempt"]["id"], "a2");
        assert_eq!(s["latest_attempt"]["outcome"], "blocked");
        assert_eq!(s["authored_by"], json!(["sol"]));
        assert_eq!(s["reviewed_by"], json!(["astra"]));
        assert_eq!(
            (s["open"].clone(), s["reaches_root"].clone()),
            (json!(true), json!(true))
        );
        assert_eq!(all["statements"][2]["attempts_without_author"], 1);
        assert_eq!(all["statements"][0]["authored_by"], json!(["other", "sol"]));
        let sole = Filter {
            authored_only_by: Some("sol".into()),
            open: false,
        };
        let only: Vec<Value> = report(&corpus, &closed, &reaching, &sole)["statements"]
            .as_array()
            .unwrap()
            .clone();
        assert_eq!(only.len(), 1);
        assert_eq!(only[0]["statement_id"], "S");
        let open = Filter {
            authored_only_by: None,
            open: true,
        };
        let text = format(&report(&corpus, &closed, &reaching, &open));
        assert!(
            text.starts_with(
                "Statements with attempts, latest attempt first (2; open in the frontier;"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "authored by: sol; reviewed by: astra; attempts without an author entry: 0 of 2"
            ),
            "{text}"
        );
        assert!(!text.contains("  T [closed"), "{text}");
        std::fs::remove_dir_all(&root).unwrap();
    }
}
