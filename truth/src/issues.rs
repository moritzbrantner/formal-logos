//! Read-only reconciliation of issue acceptance blocks with corpus records
//! (#949): Python `scripts/issue_acceptance.py`.
//!
//! A projection only: it reads one offline `gh issue list --json
//! number,title,body,url,comments` snapshot and never calls GitHub; the
//! existence and status checks do not run Lean, Comparator or source
//! verification, and they close no issue.

use crate::{Corpus, pyfmt};
use fancy_regex::Regex;
use serde::Serialize;
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::Path,
    sync::LazyLock,
};

/// The acceptance fields, in the order their requirements are checked.
pub const FIELDS: &[&str] = &[
    "results",
    "theorems",
    "statements",
    "configurations",
    "attempts",
];
const STATUSES: &[&str] = &["closed", "proved", "sourced"];

fn pattern(text: &str) -> Regex {
    Regex::new(text).expect("issue acceptance pattern")
}

static FENCE: LazyLock<Regex> =
    LazyLock::new(|| pattern(r"(?ms)^```truth-core-acceptance[ \t]*\r?\n(.*?)^```[ \t]*$"));
static FENCE_START: LazyLock<Regex> =
    LazyLock::new(|| pattern(r"(?m)^```truth-core-acceptance[ \t]*$"));
static FIELD: LazyLock<Regex> = LazyLock::new(|| pattern(r"\A([a-z_]+):[ \t]*\[(.*)\][ \t]*\z"));
static COMMENT: LazyLock<Regex> = LazyLock::new(|| pattern(r"(?s)/-.*?-/"));
static DECLARATION: LazyLock<Regex> = LazyLock::new(|| {
    pattern(
        r"\A\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma)\s+([^\s:({\[⦃]+)",
    )
});
static NAMESPACE: LazyLock<Regex> = LazyLock::new(|| pattern(r"\A\s*namespace\s+([^\s]+)"));
// `mutual … end` also consumes an `end`, so it opens an (unnamed) scope too.
static SECTION: LazyLock<Regex> = LazyLock::new(|| {
    pattern(r"\A\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*(?:section|mutual)\b")
});
static END: LazyLock<Regex> = LazyLock::new(|| pattern(r"\A\s*end\b"));

fn is_match(regex: &Regex, text: &str) -> bool {
    regex.is_match(text).unwrap_or(false)
}

fn capture<'t>(regex: &Regex, text: &'t str, group: usize) -> Option<&'t str> {
    regex
        .captures(text)
        .ok()
        .flatten()
        .and_then(|captures| captures.get(group))
        .map(|found| found.as_str())
}

/// Python's `str(OSError)` for a failed read of `path`:
/// `[Errno 2] No such file or directory: 'path'`.
pub fn os_error(error: &std::io::Error, path: &str) -> String {
    match error.raw_os_error() {
        Some(code) => {
            let message = error.to_string();
            let suffix = format!(" (os error {code})");
            let message = message.strip_suffix(&suffix).unwrap_or(&message);
            format!("[Errno {code}] {message}: {}", pyfmt::repr_str(path))
        }
        None => error.to_string(),
    }
}

/// Python `read_issue_snapshot(path)`: the issue objects of one offline
/// `gh issue list --json …` snapshot, with its error messages.
pub fn read_snapshot(path: &str) -> Result<Vec<Map<String, Value>>, String> {
    let bytes = std::fs::read(path)
        .map_err(|error| format!("cannot read {path}: {}", os_error(&error, path)))?;
    let raw = String::from_utf8(bytes).map_err(|error| {
        let position = error.utf8_error().valid_up_to();
        let byte = error.as_bytes()[position];
        format!("'utf-8' codec can't decode byte 0x{byte:02x} in position {position}")
    })?;
    let items: Value = serde_json::from_str(&raw)
        .map_err(|error| format!("issue list is not valid JSON: {error}"))?;
    match items {
        Value::Array(items) => items
            .into_iter()
            .map(|item| match item {
                Value::Object(item) => Ok(item),
                _ => Err(()),
            })
            .collect::<Result<_, _>>()
            .map_err(|()| "issue list must be a JSON array of issue objects".into()),
        _ => Err("issue list must be a JSON array of issue objects".into()),
    }
}

/// Fully qualified names of `theorem`/`lemma` declarations, following
/// `namespace`/`section`/`end` (Python `declared_theorems`).
///
/// A lexical approximation of Lean's naming (comments stripped); enough to
/// tell `TruthCore.Demo.proof` from `TruthCore.Other.proof` or
/// `TruthCore.Demo.proof'`.
pub fn declared_theorems(source: &str) -> BTreeSet<String> {
    let source = COMMENT.replace_all(source, "");
    let mut scopes: Vec<Vec<String>> = Vec::new();
    let mut names = BTreeSet::new();
    for line in pyfmt::splitlines(&source) {
        let line = line.split_once("--").map_or(line, |(code, _)| code);
        if let Some(namespace) = capture(&NAMESPACE, line, 1) {
            scopes.push(namespace.split('.').map(str::to_owned).collect());
        } else if is_match(&SECTION, line) {
            scopes.push(Vec::new());
        } else if is_match(&END, line) {
            scopes.pop();
        } else if let Some(declared) = capture(&DECLARATION, line, 1) {
            match declared.strip_prefix("_root_.") {
                Some(rooted) => names.insert(rooted.to_owned()),
                None => names.insert(
                    scopes
                        .iter()
                        .flatten()
                        .map(String::as_str)
                        .chain([declared])
                        .collect::<Vec<_>>()
                        .join("."),
                ),
            };
        }
    }
    names
}

/// A body or comment text as Python's `x.get("body") or ""` reads it.
fn body(record: &Map<String, Value>) -> Result<String, String> {
    match record.get("body") {
        Some(Value::String(text)) => Ok(text.clone()),
        value if !pyfmt::truthy(value) => Ok(String::new()),
        _ => Err("issue and comment bodies must be strings".into()),
    }
}

/// The one designated acceptance block of an issue, in its body or a
/// comment, or the errors that keep it from being designated
/// (Python `acceptance_text`).
pub fn acceptance_text(
    issue: &Map<String, Value>,
) -> Result<(Option<String>, Vec<String>), String> {
    let comments: &[Value] = match issue.get("comments") {
        Some(Value::Array(comments)) => comments,
        comments if !pyfmt::truthy(comments) => &[],
        _ => return Ok((None, vec!["comments must be a list".into()])),
    };
    let mut bodies = vec![body(issue)?];
    for comment in comments {
        if let Value::Object(comment) = comment {
            bodies.push(body(comment)?);
        }
    }
    // GitHub keeps CRLF from some clients; fences must be found (and counted) either way.
    let bodies: Vec<String> = bodies
        .iter()
        .map(|body| body.replace("\r\n", "\n").replace('\r', "\n"))
        .collect();
    let mut matches = Vec::new();
    let mut markers = 0;
    for body in &bodies {
        for captures in FENCE.captures_iter(body).flatten() {
            matches.push(captures.get(1).map_or("", |m| m.as_str()).to_owned());
        }
        markers += FENCE_START.find_iter(body).flatten().count();
    }
    if markers > matches.len() {
        return Ok((
            None,
            vec!["unterminated or malformed truth-core-acceptance fence".into()],
        ));
    }
    if matches.len() > 1 {
        return Ok((
            None,
            vec!["multiple truth-core-acceptance blocks; select one canonical block".into()],
        ));
    }
    Ok((matches.pop(), Vec::new()))
}

/// The requirements of one field: ID and, for statements, the wanted status.
pub type Requirements = BTreeMap<&'static str, Vec<(String, Option<&'static str>)>>;

fn identifier(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'))
}

fn strip(text: &str) -> &str {
    text.trim_matches(pyfmt::is_space)
}

/// Parses the documented YAML-like subset, without a dependency or guesses
/// (Python `parse_acceptance`).
pub fn parse_acceptance(text: &str) -> (Requirements, Vec<String>) {
    let mut requirements = Requirements::new();
    let mut errors = Vec::new();
    for (index, raw) in pyfmt::splitlines(text).into_iter().enumerate() {
        let line_number = index + 1;
        let line = strip(raw);
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some(captures) = FIELD.captures(line).ok().flatten() else {
            errors.push(format!("line {line_number}: expected `field: [ID, ...]`"));
            continue;
        };
        let field_name = captures.get(1).map_or("", |m| m.as_str());
        let values = captures.get(2).map_or("", |m| m.as_str());
        let Some(&field) = FIELDS.iter().find(|field| **field == field_name) else {
            errors.push(format!("line {line_number}: unknown field {field_name}"));
            continue;
        };
        if requirements.contains_key(field) {
            errors.push(format!("line {line_number}: duplicate field {field}"));
            continue;
        }
        let statements = field == "statements";
        let mut parsed: Vec<(String, Option<&'static str>)> = Vec::new();
        for value in values.split(',') {
            let token = strip(value);
            let (name, separator, status) = match token.split_once(':') {
                Some((name, status)) if statements => (strip(name), true, strip(status)),
                _ => (token, false, ""),
            };
            let status = STATUSES.iter().find(|wanted| **wanted == status).copied();
            if !identifier(name) || (statements && (!separator || status.is_none())) {
                errors.push(format!(
                    "line {line_number}: invalid {field} requirement {}",
                    pyfmt::repr_str(token)
                ));
                continue;
            }
            parsed.push((name.to_owned(), if statements { status } else { None }));
        }
        if parsed.is_empty() {
            errors.push(format!(
                "line {line_number}: {field} list must not be empty"
            ));
        }
        let distinct: BTreeSet<&str> = parsed.iter().map(|(name, _)| name.as_str()).collect();
        if distinct.len() != parsed.len() {
            errors.push(format!("line {line_number}: duplicate {field} requirement"));
        }
        requirements.insert(field, parsed);
    }
    if requirements.is_empty() {
        errors.push("acceptance block contains no requirements".into());
    }
    (requirements, errors)
}

/// One checked requirement of an issue.
#[derive(Debug, Clone, Serialize)]
pub struct Requirement {
    pub kind: &'static str,
    pub id: String,
    pub expected: Option<&'static str>,
    pub met: bool,
    pub detail: Value,
}

/// One issue's reconciliation.
#[derive(Debug, Clone, Serialize)]
pub struct Issue {
    pub number: u64,
    pub title: Value,
    pub url: Value,
    pub status: &'static str,
    pub requirements: Vec<Requirement>,
    pub errors: Vec<String>,
}

/// Issue counts by status, in Python's (text) order.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Summary {
    pub delivered: usize,
    pub missing: usize,
    pub malformed: usize,
    pub untracked: usize,
}

/// Python `analyze_issues(...)`, with `selected_id` after `--for`.
#[derive(Debug, Clone, Serialize)]
pub struct Report {
    pub summary: Summary,
    pub issues: Vec<Issue>,
    pub reverse_index: BTreeMap<String, Vec<u64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selected_id: Option<String>,
}

fn issue_number(issue: &Map<String, Value>) -> Result<u64, String> {
    issue
        .get("number")
        .filter(|number| number.is_u64())
        .and_then(Value::as_u64)
        .filter(|number| *number > 0)
        .ok_or_else(|| "issue number must be a positive integer".into())
}

/// Evaluates only declared acceptance; unknown and malformed never mean
/// done (Python `analyze_issues`). `closed_statements` is the frontier's
/// closure map; with `root`, a theorem requirement also needs a source
/// declaration of exactly that name in the result's Solution module.
pub fn analyze(
    issues: &[Map<String, Value>],
    corpus: &Corpus,
    closed_statements: &BTreeMap<String, String>,
    root: Option<&Path>,
) -> Result<Report, String> {
    let mut by_kind: HashMap<&str, HashMap<&str, &Map<String, Value>>> = HashMap::new();
    for kind in ["results", "statements", "configurations", "attempts"] {
        let records = by_kind.entry(kind).or_default();
        for record in corpus.records(kind) {
            if let Some(id) = record.get("id").and_then(Value::as_str) {
                records.insert(id, record);
            }
        }
    }
    let sourced: BTreeSet<&str> = corpus
        .records("claims")
        .into_iter()
        .filter(|claim| {
            ["statement_id", "source_id", "locator"]
                .iter()
                .all(|field| pyfmt::truthy(claim.get(*field)))
        })
        .filter_map(|claim| claim.get("statement_id").and_then(Value::as_str))
        .collect();
    // Later records win, as in Python's dict comprehension.
    let mut theorem_results: HashMap<&str, &Map<String, Value>> = HashMap::new();
    for result in corpus.records("results") {
        if let Some(theorem) = result.get("theorem").and_then(Value::as_str) {
            theorem_results.insert(theorem, result);
        }
    }
    let mut numbered = issues
        .iter()
        .map(|issue| issue_number(issue).map(|number| (number, issue)))
        .collect::<Result<Vec<_>, _>>()?;
    numbered.sort_by_key(|(number, _)| *number);
    let solution_present = |record: &Map<String, Value>| {
        record.get("status").and_then(Value::as_str) == Some("solution-present")
    };
    let mut report = Vec::new();
    let mut reverse: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
    let mut summary = Summary::default();
    for (number, issue) in numbered {
        let (text, mut errors) = acceptance_text(issue)?;
        let mut requirements = Requirements::new();
        if let Some(text) = &text {
            let (parsed, parse_errors) = parse_acceptance(text);
            requirements = parsed;
            errors.extend(parse_errors);
        }
        let mut checks = Vec::new();
        if errors.is_empty() && text.is_some() {
            for &kind in FIELDS {
                for (name, wanted) in requirements.get(kind).into_iter().flatten() {
                    let found = by_kind
                        .get(kind)
                        .and_then(|records| records.get(name.as_str()))
                        .copied();
                    let mut detail = Value::from("absent");
                    let mut met = found.is_some();
                    match kind {
                        "results" => {
                            if let Some(found) = found {
                                detail = found
                                    .get("status")
                                    .cloned()
                                    .unwrap_or_else(|| "unknown".into());
                                met = detail == "solution-present";
                            }
                        }
                        "theorems" => {
                            let result = theorem_results.get(name.as_str()).copied();
                            met = result.is_some_and(solution_present);
                            if let (true, Some(root), Some(result)) = (met, root, result) {
                                let module = result
                                    .get("solution_module")
                                    .map_or_else(String::new, pyfmt::text);
                                let path = root.join(module.replace('.', "/") + ".lean");
                                // The registered fully-qualified name and a source declaration
                                // with exactly that name are both required; compilation remains
                                // CI's job.
                                met = path.is_file() && {
                                    let source =
                                        std::fs::read_to_string(&path).map_err(|error| {
                                            os_error(&error, &path.display().to_string())
                                        })?;
                                    declared_theorems(&source).contains(name.as_str())
                                };
                            }
                            detail = if met {
                                "registered/source-present"
                            } else {
                                "not a present registered solution theorem"
                            }
                            .into();
                        }
                        "statements" => {
                            let status = closed_statements
                                .get(name.as_str())
                                .filter(|status| !status.is_empty());
                            let is_sourced = sourced.contains(name.as_str());
                            met = found.is_some()
                                && match *wanted {
                                    Some("closed") => status.is_some(),
                                    Some("proved") => status.is_some_and(|s| s == "proved"),
                                    _ => is_sourced,
                                };
                            detail = match status {
                                Some(status) => status.as_str(),
                                None if is_sourced => "sourced",
                                None => "open/absent",
                            }
                            .into();
                        }
                        _ => {
                            if let Some(found) = found {
                                detail = if kind == "attempts" {
                                    found
                                        .get("outcome")
                                        .cloned()
                                        .unwrap_or_else(|| "present".into())
                                } else {
                                    "present".into()
                                };
                            }
                        }
                    }
                    checks.push(Requirement {
                        kind,
                        id: name.clone(),
                        expected: *wanted,
                        met,
                        detail,
                    });
                    reverse.entry(name.clone()).or_default().insert(number);
                }
            }
        }
        let status = if !errors.is_empty() {
            summary.malformed += 1;
            "malformed"
        } else if text.is_none() {
            summary.untracked += 1;
            "untracked"
        } else if checks.iter().all(|check| check.met) {
            summary.delivered += 1;
            "delivered"
        } else {
            summary.missing += 1;
            "missing"
        };
        report.push(Issue {
            number,
            title: issue.get("title").cloned().unwrap_or_else(|| "".into()),
            url: issue.get("url").cloned().unwrap_or_else(|| "".into()),
            status,
            requirements: checks,
            errors,
        });
    }
    Ok(Report {
        summary,
        issues: report,
        reverse_index: reverse
            .into_iter()
            .map(|(name, numbers)| (name, numbers.into_iter().collect()))
            .collect(),
        selected_id: None,
    })
}

impl Report {
    /// The issues whose acceptance names `id` (Python `issues_for_id`).
    pub fn issues_for_id(&self, id: &str) -> Vec<u64> {
        self.reverse_index.get(id).cloned().unwrap_or_default()
    }

    /// Keeps only the issues whose acceptance names `id` (`--for`).
    pub fn select(&mut self, id: &str) {
        let matching: BTreeSet<u64> = self.issues_for_id(id).into_iter().collect();
        self.issues.retain(|issue| matching.contains(&issue.number));
        self.selected_id = Some(id.to_owned());
    }

    /// The status of each issue number; a repeated number keeps its last
    /// entry, as Python's `{entry["number"]: entry}` does.
    pub fn statuses(&self) -> HashMap<u64, &'static str> {
        self.issues
            .iter()
            .map(|issue| (issue.number, issue.status))
            .collect()
    }
}

/// The text `corpus.py issues` prints, without the final newline.
pub fn format_report(report: &Report) -> String {
    let mut lines = Vec::new();
    for issue in &report.issues {
        lines.push(format!(
            "#{} [{}]: {}",
            issue.number,
            issue.status,
            pyfmt::text(&issue.title)
        ));
        for requirement in &issue.requirements {
            let label = match requirement.expected {
                Some(expected) => format!("{}: {expected}", requirement.id),
                None => requirement.id.clone(),
            };
            lines.push(format!(
                "  {} {}: {label} ({})",
                if requirement.met { "ok" } else { "missing" },
                requirement.kind,
                pyfmt::text(&requirement.detail)
            ));
        }
        for error in &issue.errors {
            lines.push(format!("  malformed: {error}"));
        }
    }
    let summary = &report.summary;
    lines.push(format!(
        "Summary: delivered={}, missing={}, malformed={}, untracked={}",
        summary.delivered, summary.missing, summary.malformed, summary.untracked
    ));
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn issue(number: u64, body: &str) -> Map<String, Value> {
        json!({"number": number, "title": format!("Research #{number}"), "body": body})
            .as_object()
            .unwrap()
            .clone()
    }

    fn acceptance(body: &str) -> String {
        format!("Notes before the contract.\n\n```truth-core-acceptance\n{body}\n```\n")
    }

    #[test]
    fn parses_the_documented_subset_and_reports_malformed_lines() {
        let (requirements, errors) =
            parse_acceptance("# comment\nresults: [A, B]\nstatements: [S: proved]\n");
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(requirements["results"].len(), 2);
        assert_eq!(
            requirements["statements"],
            vec![("S".to_owned(), Some("proved"))]
        );
        let (_, errors) = parse_acceptance("results: []\nstatements: [S: magic]\nx: [A]");
        assert_eq!(
            errors,
            vec![
                "line 1: invalid results requirement ''",
                "line 1: results list must not be empty",
                "line 2: invalid statements requirement 'S: magic'",
                "line 2: statements list must not be empty",
                "line 3: unknown field x",
            ]
        );
    }

    #[test]
    fn finds_one_fence_and_rejects_duplicates_and_unterminated_ones() {
        let found = acceptance_text(&issue(1, &acceptance("results: [A]"))).unwrap();
        assert_eq!(found, (Some("results: [A]\n".into()), vec![]));
        let crlf = acceptance("results: [A]").replace('\n', "\r\n");
        assert!(acceptance_text(&issue(1, &crlf)).unwrap().0.is_some());
        let twice = format!(
            "{}{}",
            acceptance("results: [A]"),
            acceptance("results: [B]")
        );
        assert_eq!(acceptance_text(&issue(1, &twice)).unwrap().1.len(), 1);
        let open = "```truth-core-acceptance\nresults: [A]\n";
        assert_eq!(
            acceptance_text(&issue(1, open)).unwrap().1,
            vec!["unterminated or malformed truth-core-acceptance fence"]
        );
        assert_eq!(
            acceptance_text(&issue(1, "no block")).unwrap(),
            (None, vec![])
        );
    }

    #[test]
    fn declared_theorems_follow_namespaces_and_skip_comments() {
        let source = "namespace TruthCore\nsection\nnamespace Demo\n/- theorem hidden : True -/\n\
                      theorem proof : True := by trivial -- theorem other\n\
                      @[simp] private lemma aux : True := trivial\n\
                      end Demo\nend\nend TruthCore\ntheorem _root_.top : True := trivial\n";
        let names: Vec<String> = declared_theorems(source).into_iter().collect();
        assert_eq!(
            names,
            vec!["TruthCore.Demo.aux", "TruthCore.Demo.proof", "top"]
        );
    }
}
