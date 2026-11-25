//! Direct checkout and host references for an issue-led research handoff.
use super::retrieval::{Issues, Revision, is_pull_request, issue_header};
use crate::{Corpus, KINDS, notes};
use fancy_regex::Regex;
use serde_json::{Map, Value, json};
use std::collections::BTreeSet;
use std::fmt::Write;
use std::path::Path;
use std::sync::LazyLock;

type Fields = Map<String, Value>;

// Consume URLs as complete tokens so another repository's link or fragment
// never supplies a local shorthand reference.
static REFERENCE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"https?://[^\s()<>\[\]"`]+|(?<![\w&#/.-])(?:([\w.-]+/[\w.-]+))?#([0-9]+(?:/#[0-9]+)*)(?![\w])"#)
        .expect("issue reference pattern")
});

fn github_item(url: &str) -> Option<(&str, u64)> {
    let path = url
        .strip_prefix("https://github.com/")
        .or_else(|| url.strip_prefix("http://github.com/"))?;
    let end = path.find(['?', '#']).unwrap_or(path.len());
    let path = path[..end]
        .trim_end_matches(['.', ',', ';', ':', '!'])
        .trim_end_matches('/');
    let (prefix, number) = path.rsplit_once('/')?;
    let (repo, kind) = prefix.rsplit_once('/')?;
    if !matches!(kind, "issues" | "pull") || repo.split('/').count() != 2 {
        return None;
    }
    Some((repo, number.parse().ok()?))
}

fn references(text: &str, repository: Option<&str>) -> BTreeSet<u64> {
    let mut numbers = BTreeSet::new();
    for captures in REFERENCE.captures_iter(text).flatten() {
        let is_local =
            |repo: &str| repository.is_some_and(|local| repo.eq_ignore_ascii_case(local));
        if let Some(ids) = captures.get(2) {
            if captures.get(1).is_none_or(|repo| is_local(repo.as_str())) {
                numbers.extend(
                    ids.as_str()
                        .split("/#")
                        .filter_map(|id| id.parse::<u64>().ok()),
                );
            }
        } else if let Some((repo, id)) = github_item(&captures[0])
            && is_local(repo)
        {
            numbers.insert(id);
        }
    }
    numbers
}

fn checkout_repository(root: &Path) -> Option<String> {
    if !root.join(".git").exists() {
        return None;
    }
    let result = std::process::Command::new("git")
        .args(["config", "--get", "remote.origin.url"])
        .current_dir(root)
        .output()
        .ok()?;
    let url = std::str::from_utf8(&result.stdout)
        .ok()?
        .trim()
        .trim_end_matches('/')
        .trim_end_matches(".git");
    let name = url
        .strip_prefix("https://github.com/")
        .or_else(|| url.strip_prefix("git@github.com:"))
        .or_else(|| url.strip_prefix("ssh://git@github.com/"))?;
    Some(name.to_ascii_lowercase())
}

fn host_text(row: &Fields) -> impl Iterator<Item = &str> {
    ["title", "body"]
        .iter()
        .filter_map(|k| row.get(*k)?.as_str())
        .chain(
            row.get("comments")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|c| c.get("body")?.as_str()),
        )
}

fn contains_ref(value: &Value, matches: &impl Fn(&str) -> bool) -> bool {
    match value {
        Value::String(text) => matches(text),
        Value::Array(values) => values.iter().any(|v| contains_ref(v, matches)),
        Value::Object(values) => values.values().any(|v| contains_ref(v, matches)),
        _ => false,
    }
}

/// Quote a bounded passage around the issue mention, even when one PR reports
/// several investigations in the same paragraph.
fn mention_excerpt(text: &str, number: u64, repository: Option<&str>) -> Option<String> {
    let token = number.to_string();
    for line in text.lines().filter(|line| line.contains(&token)) {
        for occurrence in REFERENCE.find_iter(line).flatten() {
            if references(occurrence.as_str(), repository).contains(&number) {
                let prior: Vec<_> = line[..occurrence.start()]
                    .split_whitespace()
                    .rev()
                    .take(4)
                    .collect();
                let mut words: Vec<_> = prior.into_iter().rev().collect();
                words.extend(line[occurrence.start()..].split_whitespace().take(32));
                return Some(words.join(" "));
            }
        }
    }
    None
}

pub fn report(
    root: &Path,
    corpus: &Corpus,
    number: u64,
    issues: &Issues,
    revision: Revision,
) -> Result<Value, String> {
    let items = issues.snapshot().map_or(&[][..], |s| s.issues.as_slice());
    let mut targets = items
        .iter()
        .filter(|i| i.get("number").and_then(Value::as_u64) == Some(number));
    let target = targets.next();
    if targets.next().is_some() {
        return Err(format!(
            "multiple snapshot items numbered #{number}; supply a single-repository snapshot"
        ));
    }
    if target.is_some_and(is_pull_request) {
        return Err(format!(
            "#{number} is a pull request in the supplied snapshot; use its research issue"
        ));
    }
    let repo_of = |row: &Fields| {
        row.get("url")
            .and_then(Value::as_str)
            .and_then(github_item)
            .map(|(repo, _)| repo.to_ascii_lowercase())
    };
    let repo = target.and_then(repo_of).or_else(|| {
        let names: BTreeSet<_> = items.iter().filter_map(repo_of).collect();
        (names.len() == 1)
            .then(|| names.into_iter().next())
            .flatten()
    });
    let repo = repo.or_else(|| checkout_repository(root));
    let local = repo.as_deref();
    let digits = number.to_string();
    let matches = |text: &str| text.contains(&digits) && references(text, local).contains(&number);
    let mut named_records = BTreeSet::new();
    let mut named = BTreeSet::new();
    let mut timeline = BTreeSet::new();
    if let Some(target) = target {
        let lookup = notes::Lookup::of_corpus(corpus);
        for text in host_text(target) {
            named.extend(references(text, local));
            for section in notes::parse("issue", text).sections {
                for link in lookup.links(&section).0 {
                    named_records.insert((link.kind, link.id));
                }
            }
        }
        for url in target
            .get("crossReferences")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
        {
            timeline.extend(references(url, local));
        }
    }
    let mut prs = Vec::new();
    for item in items.iter().filter(|r| is_pull_request(r)) {
        if repo_of(item).is_some_and(|r| Some(r.as_str()) != local) {
            continue;
        }
        let pr = item["number"].as_u64().unwrap_or_default();
        let mut links = Vec::new();
        if timeline.contains(&pr) {
            links.push("issue timeline");
        }
        if named.contains(&pr) {
            links.push("named by issue");
        }
        let excerpt = host_text(item)
            .filter(|s| s.contains(&digits))
            .find_map(|s| mention_excerpt(s, number, local));
        if excerpt.is_some() {
            links.push("PR mentions issue");
        }
        if !links.is_empty() {
            let mut header = issue_header(item);
            header["references"] = json!(links);
            header["head"] = json!(item.get("headRefOid"));
            header["mention_excerpt"] = json!(excerpt);
            prs.push(header);
        }
    }
    prs.sort_by_key(|v| v["number"].as_u64());
    let mut records = Vec::new();
    for &kind in KINDS {
        for record in corpus.entries(kind) {
            let fields = &record.fields;
            let id = fields.get("id").and_then(Value::as_str).unwrap_or_default();
            let named_by_issue = named_records.contains(&(kind.to_owned(), id.to_owned()));
            let mentions_issue = fields.values().any(|v| contains_ref(v, &matches));
            if !named_by_issue && !mentions_issue {
                continue;
            }
            records.push(json!({"kind":kind,"path":record.path,"id":fields.get("id"),
                "label":fields.get("label").or_else(|| fields.get("paraphrase")),
                "named_by_issue":named_by_issue, "mentions_issue":mentions_issue,
                "scope_names_issue":fields.get("current_assessment").and_then(|v|v["scope"].as_str()).is_some_and(matches),
                "current_assessment":fields.get("current_assessment"),"outcome":fields.get("outcome"),
                "summary":fields.get("summary"),"blocker":fields.get("blocker")}));
        }
    }
    records.sort_by_key(|r| {
        (
            !r["scope_names_issue"].as_bool().unwrap_or(false),
            r["current_assessment"].is_null(),
            r["kind"] != "attempts",
        )
    });
    let mut sections = Vec::new();
    for (path, bytes) in notes::read_all(root)? {
        let text = std::str::from_utf8(&bytes).map_err(|e| format!("{path}: {e}"))?;
        if !text.contains(&digits) {
            continue;
        }
        for section in notes::parse(&path, text).sections {
            if matches(&section.heading) || matches(&section.body) {
                sections.push(json!({"path":path,"line":section.line,"heading":section.heading,"anchor":section.anchor}));
            }
        }
    }
    Ok(
        json!({"number":number,"revision":revision,"issue":target,"issue_history":issues,
        "pull_requests":prs,"records":records,"note_sections":sections,
        "boundary":"Direct references on this checkout and in the supplied history. Compare the requested scope with the cited delivery before dispatch or closure."}),
    )
}

pub fn render(report: &Value, limit: usize) -> String {
    let issue = &report["issue"];
    let mut out = format!(
        "Issue #{}  {}  {}\nCheckout {}\n",
        report["number"],
        issue["state"].as_str().unwrap_or("state unknown"),
        issue["title"].as_str().unwrap_or(""),
        report["revision"]["commit"]
            .as_str()
            .unwrap_or("revision unknown")
    );
    if let Some(url) = issue["url"].as_str() {
        writeln!(out, "  {url}").unwrap();
    }
    let history = &report["issue_history"];
    if history["availability"] == "missing" {
        writeln!(out, "{}", super::retrieval::MISSING_ISSUES).unwrap();
    } else {
        writeln!(
            out,
            "Snapshot {}  {} items",
            history["captured_at"].as_str().unwrap_or("date unknown"),
            history["items"]
        )
        .unwrap();
        if issue.is_null() {
            out.push_str("  Requested issue is absent from this snapshot.\n");
        }
        if history["pull_requests"] == 0 {
            out.push_str("  No PR records in this snapshot.\n");
        }
        if history["older_than_checkout"] == true {
            out.push_str("  Snapshot predates this checkout.\n");
        }
    }
    for pr in report["pull_requests"].as_array().unwrap() {
        writeln!(
            out,
            "PR #{}  {}  {}  {}",
            pr["number"],
            pr["state"].as_str().unwrap_or("unknown"),
            pr["title"].as_str().unwrap_or(""),
            pr["url"].as_str().unwrap_or("")
        )
        .unwrap();
        if let Some(s) = pr["mention_excerpt"].as_str() {
            writeln!(out, "    {s}").unwrap();
        }
    }
    let records = report["records"].as_array().unwrap();
    let sections = report["note_sections"].as_array().unwrap();
    writeln!(
        out,
        "Direct checkout references: {} records, {} note sections.",
        records.len(),
        sections.len()
    )
    .unwrap();
    for row in records.iter().take(limit) {
        writeln!(
            out,
            "  {}  {}",
            row["path"].as_str().unwrap_or(""),
            row["label"].as_str().unwrap_or("")
        )
        .unwrap();
        let a = &row["current_assessment"];
        if !a.is_null() {
            for field in [
                "scope",
                "review",
                "publication",
                "assessment",
                "reviewed_revision",
                "note",
                "supersedes",
                "next_test",
            ] {
                if matches!(field, "assessment" | "supersedes" | "next_test")
                    && !(row["scope_names_issue"] == true || row["named_by_issue"] == true)
                {
                    continue;
                }
                if let Some(s) = a[field].as_str() {
                    writeln!(out, "    {field}: {s}").unwrap();
                }
            }
        } else if let Some(s) = row["blocker"].as_str() {
            writeln!(out, "    Recorded blocker: {s}").unwrap();
        }
    }
    for s in sections.iter().take(limit) {
        writeln!(
            out,
            "  {}:{}  {}",
            s["path"].as_str().unwrap_or(""),
            s["line"],
            s["heading"].as_str().unwrap_or("")
        )
        .unwrap();
    }
    out.push_str("Use --json for the issue body, available discussions, all direct records, assessments and note locations.\n");
    out
}
