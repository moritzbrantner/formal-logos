//! Direct checkout and host references for an issue-led research handoff.
use super::retrieval::{Issues, Revision, excerpt, is_pull_request, issue_header};
use crate::{Corpus, KINDS, notes};
use fancy_regex::Regex;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet};
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

fn repository_name(name: &str) -> &str {
    if name.eq_ignore_ascii_case("moritzbrantner/truth-core") {
        "moritzbrantner/formal-logos"
    } else {
        name
    }
}

pub(crate) fn github_item(url: &str) -> Option<(&str, u64)> {
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
    Some((repository_name(repo), number.parse().ok()?))
}

fn references(text: &str, repository: Option<&str>) -> BTreeSet<u64> {
    let mut numbers = BTreeSet::new();
    for captures in REFERENCE.captures_iter(text).flatten() {
        let is_local = |repo: &str| {
            repository.is_some_and(|local| repository_name(repo).eq_ignore_ascii_case(local))
        };
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

pub(crate) fn checkout_repository(root: &Path) -> Option<String> {
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
    Some(repository_name(name).to_ascii_lowercase())
}

pub(crate) fn matches_checkout(repository: &str, checkout: Option<&str>) -> bool {
    repository.eq_ignore_ascii_case("moritzbrantner/formal-logos")
        || checkout.is_none_or(|local| repository.eq_ignore_ascii_case(local))
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
    let checkout = checkout_repository(root);
    if let (Some(host), Some(local)) = (&repo, &checkout)
        && !matches_checkout(host, Some(local))
    {
        return Err(format!(
            "issue snapshot belongs to {host}, checkout belongs to {local}"
        ));
    }
    let repo = repo.or(checkout);
    let local = repo.as_deref();
    let digits = number.to_string();
    let matches = |text: &str| text.contains(&digits) && references(text, local).contains(&number);
    let mut named_records = BTreeSet::new();
    let mut named = BTreeSet::new();
    let mut timeline = BTreeSet::new();
    let lookup = notes::Lookup::of_corpus(corpus);
    if let Some(target) = target {
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
    let mut related_prs = BTreeMap::new();
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
            related_prs.insert(format!("PR-{pr}"), pr);
            prs.push(header);
        }
    }
    prs.sort_by_key(|v| v["number"].as_u64());
    let mut sections = Vec::new();
    let mut section_keys = BTreeSet::new();
    let mut section_records = BTreeMap::<_, BTreeSet<_>>::new();
    for (path, bytes) in notes::read_all(root)? {
        let text = std::str::from_utf8(&bytes).map_err(|e| format!("{path}: {e}"))?;
        if !text.contains(&digits) {
            continue;
        }
        let note = notes::parse(&path, text);
        for section in &note.sections {
            if matches(&section.heading) || matches(&section.body) {
                for link in lookup.links(section).0 {
                    section_records
                        .entry((link.kind, link.id))
                        .or_default()
                        .insert(note.key(section));
                }
                if !section.anchor.is_empty() {
                    section_keys.insert(note.key(section));
                }
                sections.push(json!({"path":path,"line":section.line,"heading":section.heading,"anchor":section.anchor}));
            }
        }
    }
    let mut records = Vec::new();
    for &kind in KINDS {
        for record in corpus.entries(kind) {
            let fields = &record.fields;
            let id = fields.get("id").and_then(Value::as_str).unwrap_or_default();
            let key = (kind.to_owned(), id.to_owned());
            let named_by_issue = named_records.contains(&key);
            let named_by_sections = section_records.get(&key);
            let cited_prs: BTreeSet<_> = fields
                .get("evidence")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .filter_map(|reference| related_prs.get(reference))
                .collect();
            let mentions_issue = fields.values().any(|v| contains_ref(v, &matches));
            let assessment_section = fields
                .get("current_assessment")
                .and_then(|assessment| assessment["note"].as_str())
                .filter(|note| section_keys.contains(*note));
            let direct = named_by_issue || mentions_issue || assessment_section.is_some();
            if !direct && named_by_sections.is_none() && cited_prs.is_empty() {
                continue;
            }
            records.push(json!({"kind":kind,"path":record.path,"id":fields.get("id"),
                "label":fields.get("label").or_else(|| fields.get("paraphrase")),
                "named_by_issue":named_by_issue, "mentions_issue":mentions_issue,
                "assessment_section":assessment_section, "direct":direct,
                "named_by_sections":named_by_sections, "cited_related_prs":cited_prs,
                "scope_names_issue":fields.get("current_assessment").and_then(|v|v["scope"].as_str()).is_some_and(matches),
                "current_assessment":fields.get("current_assessment"),"outcome":fields.get("outcome"),
                "summary":fields.get("summary"),"blocker":fields.get("blocker")}));
        }
    }
    records.sort_by_key(|r| {
        (
            r["direct"] != true,
            r["direct"] != true && r["named_by_sections"].is_null(),
            !r["scope_names_issue"].as_bool().unwrap_or(false),
            r["assessment_section"].is_null(),
            r["current_assessment"].is_null(),
            r["kind"] != "attempts",
        )
    });
    Ok(
        json!({"number":number,"revision":revision,"issue":target,"issue_history":issues,
        "pull_requests":prs,"records":records,"note_sections":sections,
        "boundary":"References from this issue, its note sections and related PRs. Compare the requested scope with the cited delivery before dispatch or closure."}),
    )
}

/// Show the tail of the assigned issue's captured discussion. Keep the
/// snapshot ordinal as a locator even when a legacy comment lacks a URL.
fn render_issue_comments(out: &mut String, issue: &Value, limit: usize) {
    let Some(comments) = issue["comments"].as_array() else {
        return;
    };
    let mut discussion = comments
        .iter()
        .enumerate()
        .rev()
        .filter_map(|(i, comment)| {
            let body = comment["body"].as_str()?.trim();
            (!body.is_empty()).then_some((i + 1, comment, body))
        });
    for (ordinal, comment, body) in discussion.by_ref().take(limit) {
        write!(out, "Issue comment {ordinal}").unwrap();
        if let Some(login) = comment["author"]["login"].as_str() {
            write!(out, "  @{login}").unwrap();
        }
        if let Some(date) = comment["createdAt"].as_str() {
            write!(out, "  {date}").unwrap();
        }
        if let Some(url) = comment["url"].as_str() {
            write!(out, "  {url}").unwrap();
        }
        writeln!(out, "\n    {}", excerpt(body, 220)).unwrap();
    }
    if discussion.next().is_some() {
        out.push_str("  More issue comments in --json.\n");
    }
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
    render_issue_comments(&mut out, issue, limit);
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
        "Linked checkout evidence: {} records, {} note sections.",
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
        if let Some(sections) = row["named_by_sections"]
            .as_array()
            .filter(|_| row["direct"] != true)
        {
            for section in sections.iter().filter_map(Value::as_str) {
                writeln!(out, "    Named in {section}").unwrap();
            }
        }
        if let Some(prs) = row["cited_related_prs"]
            .as_array()
            .filter(|v| !v.is_empty())
        {
            let refs = prs
                .iter()
                .filter_map(Value::as_u64)
                .map(|n| format!("#{n}"))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(out, "    Cites related PR {refs}").unwrap();
            if row["direct"] != true && row["named_by_sections"].is_null() {
                // A batch can also contain work on independent issues.
                continue;
            }
        }
        let a = &row["current_assessment"];
        if !a.is_null() {
            if let Some(section) = row["assessment_section"].as_str() {
                writeln!(out, "    Assessment linked to issue section {section}").unwrap();
            }
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
                    && !(row["scope_names_issue"] == true
                        || row["named_by_issue"] == true
                        || !row["assessment_section"].is_null())
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
    out.push_str("Use --json for the issue body, available discussions, all linked records, assessments and note locations.\n");
    out
}
