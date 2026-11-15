//! Lexical and structural retrieval shared by `brief` and `novelty`.
//!
//! Everything here finds **candidate evidence**; nothing decides what a
//! record means, whether two texts say the same thing or whether a premise
//! is established. A match records exactly which query items occur in which
//! unit (a note paragraph, a record's prose, an issue paragraph, a Lean
//! declaration), so a reader can check it.

use crate::{index, notes};
use fancy_regex::Regex;
use rusqlite::Connection;
use serde::Serialize;
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Path, PathBuf},
    process::Command,
    sync::LazyLock,
    time::UNIX_EPOCH,
};

fn pattern(text: &str) -> Regex {
    Regex::new(text).expect("retrieval pattern")
}

/// `` `D(x,y)` for the existing `DependsForBeing x y` ``: a note's local
/// notation for a Lean identifier.
static ALIAS: LazyLock<Regex> = LazyLock::new(|| {
    pattern(
        r"`([A-Za-z]{1,3})\([^`)]*\)`\s*(?:for|=|:=|denotes|means|abbreviates)\s+(?:the\s+)?(?:existing\s+)?`([A-Za-z_][\w.']*)",
    )
});
static DATE: LazyLock<Regex> = LazyLock::new(|| pattern(r"\b(20\d\d-[01]\d-[0-3]\d)\b"));
/// Words marking a superseded, retired or replaced text.
static SUPERSEDED: LazyLock<Regex> = LazyLock::new(|| {
    pattern(r"(?i)\b(?:superseded|supersedes|retired|obsolete|no longer current)\b")
});
/// Headings of recorded judgments, assessments and reopening conditions.
pub static ASSESSMENT_HEADING: LazyLock<Regex> = LazyLock::new(|| {
    pattern(
        r"(?i)provisional|judg(?:e)?ment|assessment|reopen|revision condition|remaining (?:gap|burden)|open burden|parity",
    )
});
/// Headings of recorded rival and objection analysis.
pub static RIVAL_HEADING: LazyLock<Regex> = LazyLock::new(|| {
    pattern(r"(?i)rival|objection|surviv|alternative|countermodel|counterexample|repl(?:y|ies)")
});
/// Sentences stating that something is (not) settled.
static STATUS_SENTENCE: LazyLock<Regex> = LazyLock::new(|| {
    pattern(
        r"(?i)provisional|not (?:been )?(?:established|settled|shown)|remains? (?:open|unresolved|live)|still open|unresolved|\bOPEN\b|reopen|revision condition|not a (?:proof|certificate)|has not",
    )
});

/// Logical operators a query may contain, each with the spellings a unit
/// may use for it.
/// Logical operators a query may contain, each with the spellings a unit
/// may use for it once its symbols are normalized ([`normalize_symbols`]).
const OPERATORS: &[(&str, &[&str])] = &[
    ("↔", &["↔", " iff ", "equivalen"]),
    ("→", &["→", "implies"]),
    ("¬", &["¬"]),
    ("∧", &["∧"]),
    ("∨", &["∨"]),
    ("∀", &["∀", "for all"]),
    ("∃", &["∃", "there exists"]),
];

/// Symbolic operator spellings a query may use, longest first, with the
/// operator each normalizes to.
const SYMBOLS: &[(&str, &str)] = &[
    ("<->", "↔"),
    ("->", "→"),
    ("/\\", "∧"),
    ("\\/", "∨"),
    ("↔", "↔"),
    ("⇔", "↔"),
    ("→", "→"),
    ("⇒", "→"),
    ("¬", "¬"),
    ("~", "¬"),
    ("∧", "∧"),
    ("∨", "∨"),
    ("∀", "∀"),
    ("∃", "∃"),
];

/// `text` with every symbolic operator spelling replaced by its canonical
/// operator, longest spelling first, so `<->` is one `↔` and never also an
/// `→`. A `~` is left alone in evidence (prose uses it for "about").
pub fn normalize_symbols(text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::with_capacity(text.len());
    let mut index = 0;
    while index < chars.len() {
        let rest: String = chars[index..chars.len().min(index + 3)].iter().collect();
        match SYMBOLS
            .iter()
            .find(|(spelling, _)| *spelling != "~" && rest.starts_with(spelling))
        {
            Some((spelling, operator)) => {
                out.push_str(operator);
                index += spelling.chars().count();
            }
            None => {
                out.push(chars[index]);
                index += 1;
            }
        }
    }
    out
}

const STOPWORDS: &[&str] = &[
    "the", "and", "for", "with", "that", "this", "from", "into", "are", "was", "were", "has",
    "have", "had", "not", "but", "its", "his", "her", "their", "our", "your", "any", "all", "some",
    "can", "may", "might", "would", "should", "could", "does", "did", "who", "what", "which",
    "when", "where", "why", "how", "than", "then", "there", "here", "about", "between", "under",
    "over", "only", "also", "very", "more", "most", "such", "each", "every", "other", "whether",
    "being", "been", "via", "per", "already", "new", "novel", "theorem", "result", "claim",
    "proof", "prove", "proves", "show", "shows", "does", "issue", "note",
];

/// One item of a query: a word (matched by its stem as a word prefix), a
/// Lean-style identifier (matched as a whole word, or through a note's
/// notation), a one-letter function symbol (`D(`) or a logical operator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Item {
    pub text: String,
    pub kind: &'static str,
    #[serde(skip)]
    key: String,
}

/// A parsed query: its items in first-occurrence order.
#[derive(Clone, Debug, Serialize)]
pub struct Query {
    pub text: String,
    pub items: Vec<Item>,
}

/// Words of `text`: maximal runs of alphanumerics and `_`.
pub fn words(text: &str) -> Vec<&str> {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|word| !word.is_empty())
        .collect()
}

/// A CamelCase or snake_case identifier (`DependsForBeing`, `can_be`), not
/// an ordinary capitalised word.
pub fn is_identifier(word: &str) -> bool {
    let mut chars = word.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    let rest: Vec<char> = chars.collect();
    (first.is_alphabetic()
        && rest.iter().any(|c| c.is_uppercase())
        && rest.iter().any(|c| c.is_lowercase()))
        || (word.contains('_') && word.chars().any(char::is_alphabetic) && word.len() > 3)
}

fn stem(word: &str) -> String {
    let lower = word.to_lowercase();
    let count = lower.chars().count();
    if count <= 6 {
        lower
    } else {
        lower.chars().take((count - 3).max(5)).collect()
    }
}

impl Query {
    pub fn parse(text: &str) -> Self {
        let mut items: Vec<Item> = Vec::new();
        let mut push = |item: Item| {
            if !items
                .iter()
                .any(|known| known.key == item.key && known.kind == item.kind)
            {
                items.push(item);
            }
        };
        let chars: Vec<char> = text.chars().collect();
        let mut index = 0;
        while index < chars.len() {
            let c = chars[index];
            if c.is_alphanumeric() || c == '_' {
                let start = index;
                while index < chars.len() && (chars[index].is_alphanumeric() || chars[index] == '_')
                {
                    index += 1;
                }
                let word: String = chars[start..index].iter().collect();
                let called = chars.get(index) == Some(&'(');
                let lower = word.to_lowercase();
                if is_identifier(&word) {
                    push(Item {
                        key: lower,
                        text: word,
                        kind: "identifier",
                    });
                } else if word.chars().count() == 1
                    && called
                    && word.chars().all(char::is_alphabetic)
                {
                    push(Item {
                        key: word.clone(),
                        text: word,
                        kind: "symbol",
                    });
                } else if lower == "iff" {
                    push(Item {
                        key: "↔".into(),
                        text: "↔".into(),
                        kind: "operator",
                    });
                } else if word.chars().count() >= 3
                    && !STOPWORDS.contains(&lower.as_str())
                    && !word.chars().all(|c| c.is_ascii_digit())
                {
                    push(Item {
                        key: stem(&word),
                        text: word,
                        kind: "word",
                    });
                }
                continue;
            }
            // An ASCII spelling is consumed whole, so `<->` is one `↔`, not
            // also a `→`.
            let rest: String = chars[index..chars.len().min(index + 3)].iter().collect();
            let found = SYMBOLS
                .iter()
                .find(|(spelling, _)| rest.starts_with(spelling))
                .map(|(spelling, operator)| (spelling.chars().count(), *operator));
            match found {
                Some((width, operator)) => {
                    push(Item {
                        key: operator.into(),
                        text: operator.into(),
                        kind: "operator",
                    });
                    index += width;
                }
                None => index += 1,
            }
        }
        Self {
            text: text.to_owned(),
            items,
        }
    }

    /// How many of `matched` are content items (words, identifiers,
    /// symbols) rather than operators, and of how many.
    pub fn content_coverage(&self, matched: &[bool]) -> (usize, usize) {
        let content: Vec<bool> = self
            .items
            .iter()
            .zip(matched)
            .filter(|(item, _)| item.kind != "operator")
            .map(|(_, hit)| *hit)
            .collect();
        coverage(&content)
    }

    /// Whether `matched` covers at least half of all items and at least
    /// half of the content items: operators alone are weak evidence.
    pub fn substantial(&self, matched: &[bool]) -> bool {
        let (covered, total) = coverage(matched);
        let (content, content_total) = self.content_coverage(matched);
        covered > 0 && covered * 2 >= total && content * 2 >= content_total
    }

    /// The identifiers of the query.
    pub fn identifiers(&self) -> Vec<&str> {
        self.items
            .iter()
            .filter(|item| item.kind == "identifier")
            .map(|item| item.text.as_str())
            .collect()
    }

    /// The FTS5 expression for candidate retrieval: any word (by stem
    /// prefix) or identifier. `None` when the query has neither.
    pub fn fts_expression(&self) -> Option<String> {
        let parts: Vec<String> = self
            .items
            .iter()
            .filter_map(|item| match item.kind {
                "word" => Some(format!("\"{}\"*", item.key.replace('"', "\"\""))),
                "identifier" => Some(format!("\"{}\"", item.text.replace('"', "\"\""))),
                _ => None,
            })
            .collect();
        (!parts.is_empty()).then(|| parts.join(" OR "))
    }

    /// Which items occur in `unit`. `aliases` maps a lower-cased identifier
    /// to the notation a note introduced for it (`D` for `DependsForBeing`).
    pub fn matched(&self, unit: &str, aliases: &BTreeMap<String, String>) -> Vec<bool> {
        let lower = unit.to_lowercase();
        let unit_words: BTreeSet<String> = words(&lower).into_iter().map(str::to_owned).collect();
        let spaced = format!(
            " {} ",
            normalize_symbols(&lower)
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
        );
        self.items
            .iter()
            .map(|item| match item.kind {
                "word" => unit_words.iter().any(|word| word.starts_with(&item.key)),
                "identifier" => {
                    unit_words.contains(&item.key)
                        || aliases
                            .get(&item.key)
                            .is_some_and(|alias| has_call(unit, alias))
                }
                "symbol" => has_call(unit, &item.text),
                _ => OPERATORS
                    .iter()
                    .find(|(operator, _)| *operator == item.key)
                    .is_some_and(|(_, spellings)| {
                        spellings.iter().any(|spelling| spaced.contains(spelling))
                    }),
            })
            .collect()
    }
}

/// Whether `text` applies the symbol `name` (`D(` or `D y x` in code, not
/// inside a longer word).
fn has_call(text: &str, name: &str) -> bool {
    let chars: Vec<char> = text.chars().collect();
    let target: Vec<char> = name.chars().collect();
    (0..chars.len()).any(|start| {
        chars[start..].starts_with(&target)
            && (start == 0 || !(chars[start - 1].is_alphanumeric() || chars[start - 1] == '_'))
            && chars.get(start + target.len()) == Some(&'(')
    })
}

/// How many of `matched` hold, and of how many.
pub fn coverage(matched: &[bool]) -> (usize, usize) {
    (matched.iter().filter(|hit| **hit).count(), matched.len())
}

/// The matched item texts.
pub fn matched_items(query: &Query, matched: &[bool]) -> Vec<String> {
    query
        .items
        .iter()
        .zip(matched)
        .filter(|(_, hit)| **hit)
        .map(|(item, _)| item.text.clone())
        .collect()
}

/// The notation a note introduces for identifiers: lower-cased identifier
/// to symbol. The first definition of a symbol wins.
pub fn note_aliases(text: &str) -> BTreeMap<String, String> {
    let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut aliases = BTreeMap::new();
    for captures in ALIAS.captures_iter(&flat).flatten() {
        let (Some(symbol), Some(identifier)) = (captures.get(1), captures.get(2)) else {
            continue;
        };
        let identifier = identifier.as_str().rsplit('.').next().unwrap_or_default();
        aliases
            .entry(identifier.to_lowercase())
            .or_insert_with(|| symbol.as_str().to_owned());
    }
    aliases
}

/// Paragraphs of `body` (blank-line separated) with the 1-based file line
/// of their first line, given the line of the body's first line.
pub fn paragraphs(body: &str, first_line: usize) -> Vec<(usize, String)> {
    let mut out: Vec<(usize, String)> = Vec::new();
    let mut current: Option<(usize, String)> = None;
    for (offset, line) in body.lines().enumerate() {
        if line.trim().is_empty() {
            out.extend(current.take());
        } else {
            let entry = current.get_or_insert_with(|| (first_line + offset, String::new()));
            entry.1.push_str(line);
            entry.1.push('\n');
        }
    }
    out.extend(current);
    out
}

/// The 1-based file line of a section's first body line.
pub fn body_line(section: &notes::Section) -> usize {
    if section.level == 0 {
        section.line
    } else {
        section.line + 1
    }
}

/// Issue and PR numbers referenced by `text` (`#123`, not `&#123;` or a
/// path fragment, and GitHub `/issues/N` or `/pull/N` URLs), in
/// first-occurrence order. Scanned by hand: fancy-regex look-behind can stop
/// early on long texts.
pub fn issue_references(text: &str) -> Vec<u64> {
    let chars: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let digits_at = |start: usize| -> (usize, Option<u64>) {
        let mut end = start;
        while end < chars.len() && chars[end].is_ascii_digit() {
            end += 1;
        }
        let number: String = chars[start..end].iter().collect();
        (end, number.parse().ok())
    };
    let mut index = 0;
    while index < chars.len() {
        let mut found = None;
        if chars[index] == '#'
            && (index == 0
                || !(chars[index - 1].is_alphanumeric()
                    || matches!(chars[index - 1], '&' | '/' | '#' | '_')))
        {
            let (end, number) = digits_at(index + 1);
            if (2..=6).contains(&(end - index - 1))
                && !chars
                    .get(end)
                    .is_some_and(|c| c.is_alphanumeric() || *c == '_')
            {
                found = number;
            }
        } else {
            for marker in ["/issues/", "/pull/"] {
                let marker: Vec<char> = marker.chars().collect();
                if chars[index..].starts_with(&marker) {
                    let start = chars[..index]
                        .iter()
                        .rposition(|c| c.is_whitespace() || matches!(c, '(' | '<' | '[' | '"'))
                        .map_or(0, |position| position + 1);
                    let prefix: String = chars[start..index].iter().collect();
                    if prefix.contains("github.com/") {
                        found = digits_at(index + marker.len()).1;
                    }
                }
            }
        }
        if let Some(number) = found.filter(|number| *number > 0)
            && !out.contains(&number)
        {
            out.push(number);
        }
        index += 1;
    }
    out
}

/// The latest `YYYY-MM-DD` written in `text`.
pub fn latest_date(text: &str) -> Option<String> {
    DATE.captures_iter(text)
        .flatten()
        .filter_map(|captures| captures.get(1).map(|found| found.as_str().to_owned()))
        .max()
}

/// Lines of `text` that mark it superseded or retired, with their offsets.
pub fn superseded_lines(text: &str) -> Vec<(usize, String)> {
    text.lines()
        .enumerate()
        .filter(|(_, line)| SUPERSEDED.is_match(line).unwrap_or(false))
        .map(|(offset, line)| (offset, excerpt(line, 240)))
        .collect()
}

/// The first paragraph of a section that states what is or is not settled,
/// else its first paragraph.
pub fn status_paragraph(paragraphs: &[(usize, String)]) -> Option<&(usize, String)> {
    paragraphs
        .iter()
        .find(|(_, text)| STATUS_SENTENCE.is_match(text).unwrap_or(false))
        .or_else(|| paragraphs.first())
}

/// `text` with collapsed whitespace, clipped to `max` characters.
pub fn excerpt(text: &str, max: usize) -> String {
    let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if flat.chars().count() <= max {
        flat
    } else {
        let mut clipped: String = flat.chars().take(max.saturating_sub(1)).collect();
        clipped = clipped.trim_end().to_owned();
        clipped.push('…');
        clipped
    }
}

/// The latest first-parent commits that changed `path` (newest first, at
/// most `limit`): date, subject and the PR number a merge subject names.
/// Empty when git cannot tell (no repository, untracked file).
pub fn history(root: &Path, path: &str, limit: usize) -> Vec<Value> {
    let output = Command::new("git")
        .args([
            "log",
            "--first-parent",
            &format!("-n{limit}"),
            "--format=%h%x09%cs%x09%s",
            "--",
            path,
        ])
        .current_dir(root)
        .output();
    let Some(output) = output.ok().filter(|output| output.status.success()) else {
        return Vec::new();
    };
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let mut parts = line.splitn(3, '\t');
            let (commit, date, subject) = (parts.next()?, parts.next()?, parts.next()?);
            let pull = subject
                .strip_prefix("Merge pull request #")
                .and_then(|rest| rest.split_whitespace().next())
                .or_else(|| subject.rsplit_once("(#").and_then(|(_, rest)| rest.strip_suffix(')')))
                .and_then(|number| number.parse::<u64>().ok());
            Some(serde_json::json!({"commit": commit, "date": date, "subject": subject, "pull_request": pull}))
        })
        .collect()
}

/// The checkout's revision: HEAD commit and commit time, when git can tell.
#[derive(Clone, Debug, Default, Serialize)]
pub struct Revision {
    pub commit: Option<String>,
    pub committed_at: Option<String>,
    #[serde(skip)]
    pub committed_epoch: Option<i64>,
}

impl Revision {
    pub fn of(root: &Path) -> Self {
        let output = Command::new("git")
            .args(["log", "-1", "--format=%H %ct"])
            .current_dir(root)
            .output();
        let Some(output) = output.ok().filter(|output| output.status.success()) else {
            return Self::default();
        };
        let text = String::from_utf8_lossy(&output.stdout);
        let mut parts = text.split_whitespace();
        let commit = parts.next().map(str::to_owned);
        let epoch = parts.next().and_then(|epoch| epoch.parse::<i64>().ok());
        Self {
            commit,
            committed_at: epoch.map(format_epoch),
            committed_epoch: epoch,
        }
    }
}

/// `YYYY-MM-DDTHH:MM:SSZ` for a Unix time.
pub fn format_epoch(epoch: i64) -> String {
    let days = epoch.div_euclid(86_400);
    let seconds = epoch.rem_euclid(86_400);
    // Howard Hinnant's civil_from_days.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        seconds / 3600,
        seconds % 3600 / 60,
        seconds % 60
    )
}

/// The Unix time of `YYYY-MM-DD[THH:MM[:SS]][Z]` (UTC), `None` otherwise.
pub fn parse_epoch(text: &str) -> Option<i64> {
    let bytes = text.as_bytes();
    let number = |range: std::ops::Range<usize>| -> Option<i64> {
        text.get(range)
            .filter(|part| part.bytes().all(|b| b.is_ascii_digit()))?
            .parse()
            .ok()
    };
    let (year, month, day) = (number(0..4)?, number(5..7)?, number(8..10)?);
    if bytes.get(4) != Some(&b'-') || bytes.get(7) != Some(&b'-') || !(1..=12).contains(&month) {
        return None;
    }
    let (hour, minute, second) = if bytes.get(10).is_some_and(|b| *b == b'T' || *b == b' ') {
        (
            number(11..13)?,
            number(14..16)?,
            number(17..19).unwrap_or(0),
        )
    } else {
        (0, 0, 0)
    };
    let year = year - i64::from(month <= 2);
    let era = year.div_euclid(400);
    let yoe = year - era * 400;
    let mp = (month + 9) % 12;
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;
    Some(days * 86_400 + hour * 3600 + minute * 60 + second)
}

/// An offline issue/PR snapshot and what is known about its currency.
#[derive(Clone, Debug, Serialize)]
pub struct Snapshot {
    pub path: String,
    /// When the snapshot was taken: its `captured_at` field, else the
    /// file's modification time.
    pub captured_at: Option<String>,
    pub captured_from: &'static str,
    pub items: usize,
    pub pull_requests: usize,
    /// Whether any item records a closed or merged state; a snapshot of
    /// open issues only cannot show finished or retired work.
    pub includes_closed: bool,
    /// Whether items carry their comments.
    pub includes_comments: bool,
    /// Captured before the checkout's HEAD commit, so later issue activity
    /// is unknown. `None` when either time is unknown.
    pub older_than_checkout: Option<bool>,
    #[serde(skip)]
    pub issues: Vec<Map<String, Value>>,
}

/// The issue evidence available to a view.
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "availability", rename_all = "snake_case")]
pub enum Issues {
    /// No snapshot was supplied: issue history is unknown.
    Missing {
        meaning: &'static str,
    },
    Snapshot(Snapshot),
}

pub const MISSING_ISSUES: &str = "no --issues-from snapshot supplied: issue and PR history is unknown \
     here; absence of issue hits is not evidence that no prior work exists";

impl Issues {
    pub fn snapshot(&self) -> Option<&Snapshot> {
        match self {
            Self::Snapshot(snapshot) => Some(snapshot),
            Self::Missing { .. } => None,
        }
    }
}

/// Reads an offline snapshot: a `gh issue list`/`gh pr list --json …` array,
/// or `{"captured_at": "…", "items": [...]}`. `head_epoch` is the
/// checkout's HEAD commit time.
pub fn read_snapshot(path: &str, head_epoch: Option<i64>) -> Result<Snapshot, String> {
    let bytes = std::fs::read(path).map_err(|error| {
        format!(
            "cannot read {path}: {}",
            crate::issues::os_error(&error, path)
        )
    })?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("issue snapshot is not valid JSON: {error}"))?;
    let (items, captured) = match value {
        Value::Array(items) => (items, None),
        Value::Object(mut object) => {
            let items = match object.remove("items") {
                Some(Value::Array(items)) => items,
                _ => return Err("an issue snapshot object needs an \"items\" array".into()),
            };
            let captured = match object.get("captured_at") {
                Some(Value::String(text)) => Some(text.clone()),
                None | Some(Value::Null) => None,
                Some(_) => return Err("captured_at must be a string".into()),
            };
            (items, captured)
        }
        _ => return Err("issue snapshot must be a JSON array or an object with items".into()),
    };
    let issues: Vec<Map<String, Value>> = items
        .into_iter()
        .map(|item| match item {
            Value::Object(item)
                if item
                    .get("number")
                    .and_then(Value::as_u64)
                    .is_some_and(|n| n > 0) =>
            {
                Ok(item)
            }
            _ => Err(
                "every snapshot item must be an object with a positive integer number".to_owned(),
            ),
        })
        .collect::<Result<_, _>>()?;
    let (captured_at, captured_from, epoch) = match captured {
        Some(text) => {
            let epoch = parse_epoch(&text)
                .ok_or_else(|| format!("captured_at {text:?} is not an ISO date"))?;
            (Some(format_epoch(epoch)), "captured_at", Some(epoch))
        }
        None => {
            let epoch = std::fs::metadata(path)
                .and_then(|metadata| metadata.modified())
                .ok()
                .and_then(|time| time.duration_since(UNIX_EPOCH).ok())
                .and_then(|duration| i64::try_from(duration.as_secs()).ok());
            (epoch.map(format_epoch), "file modification time", epoch)
        }
    };
    Ok(Snapshot {
        path: path.to_owned(),
        captured_at,
        captured_from,
        items: issues.len(),
        pull_requests: issues.iter().filter(|issue| is_pull_request(issue)).count(),
        includes_closed: issues.iter().any(|issue| {
            matches!(
                issue
                    .get("state")
                    .and_then(Value::as_str)
                    .map(str::to_uppercase)
                    .as_deref(),
                Some("CLOSED" | "MERGED")
            )
        }),
        includes_comments: issues.iter().any(|issue| issue.contains_key("comments")),
        older_than_checkout: epoch.zip(head_epoch).map(|(taken, head)| taken < head),
        issues,
    })
}

pub fn is_pull_request(issue: &Map<String, Value>) -> bool {
    issue
        .get("url")
        .and_then(Value::as_str)
        .is_some_and(|url| url.contains("/pull/"))
        || issue.contains_key("mergedAt")
        || issue.contains_key("headRefName")
}

/// An issue's text units: title, body paragraphs and comment paragraphs,
/// each with a locator.
pub fn issue_units(issue: &Map<String, Value>) -> Vec<(String, String)> {
    let mut units = Vec::new();
    if let Some(title) = issue.get("title").and_then(Value::as_str) {
        units.push(("title".to_owned(), title.to_owned()));
    }
    if let Some(body) = issue.get("body").and_then(Value::as_str) {
        for (line, text) in paragraphs(body, 1) {
            units.push((format!("body line {line}"), text));
        }
    }
    for (index, comment) in issue
        .get("comments")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .enumerate()
    {
        if let Some(body) = comment.get("body").and_then(Value::as_str) {
            for (line, text) in paragraphs(body, 1) {
                units.push((format!("comment {} line {line}", index + 1), text));
            }
        }
    }
    units
}

/// An issue's compact identity for output.
pub fn issue_header(issue: &Map<String, Value>) -> Value {
    let field = |name: &str| issue.get(name).cloned().unwrap_or(Value::Null);
    serde_json::json!({
        "number": field("number"),
        "kind": if is_pull_request(issue) { "pull_request" } else { "issue" },
        "title": field("title"),
        "state": issue.get("state").cloned().unwrap_or_else(|| Value::String("unknown".into())),
        "url": field("url"),
        "updated_at": field("updatedAt"),
        "closed_at": field("closedAt"),
    })
}

/// A note section candidate from the index.
#[derive(Clone, Debug)]
pub struct SectionHit {
    pub key: String,
    pub path: String,
}

/// The note sections and records the index ranks for `expression` (FTS5
/// rank, then key, so ties are ordered).
pub fn index_candidates(
    db: &Connection,
    expression: &str,
    limit: i64,
) -> Result<(Vec<SectionHit>, Vec<super::RecordKey>), String> {
    let error = |error: rusqlite::Error| error.to_string();
    let mut statement = db
        .prepare(
            "SELECT s.key,s.path FROM note_search JOIN note_sections s ON s.key=note_search.key
             WHERE note_search MATCH ? ORDER BY rank, s.key LIMIT ?",
        )
        .map_err(error)?;
    let sections = statement
        .query_map(rusqlite::params![expression, limit], |row| {
            Ok(SectionHit {
                key: row.get(0)?,
                path: row.get(1)?,
            })
        })
        .map_err(error)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(error)?;
    let mut statement = db
        .prepare(
            "SELECT r.kind,r.id FROM search JOIN records r ON r.key=search.id
             WHERE search MATCH ? ORDER BY rank, r.key LIMIT ?",
        )
        .map_err(error)?;
    let records = statement
        .query_map(rusqlite::params![expression, limit], |row| {
            Ok((row.get(0)?, row.get(1)?))
        })
        .map_err(error)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(error)?;
    Ok((sections, records))
}

/// The index of `root`, reused when it is bound to the current corpus and
/// notes, else rebuilt, with its freshness record.
pub fn open_index(root: &Path) -> Result<(Connection, Value), String> {
    let (db, rebuilt) = index::open(root)?;
    let digest: Option<String> = db
        .query_row("SELECT value FROM metadata WHERE key='digest'", [], |row| {
            row.get(0)
        })
        .ok();
    Ok((
        db,
        serde_json::json!({
            "path": index::PATH,
            "digest": digest,
            "rebuilt": rebuilt,
            "meaning": "a disposable projection bound to the digest of every corpus record and note; \
                        reused only while that digest matches, otherwise rebuilt before the query",
        }),
    ))
}

/// Text fields of a record that carry its prose.
pub const PROSE_FIELDS: &[&str] = &[
    "label",
    "paraphrase",
    "summary",
    "blocker",
    "meaning",
    "description",
    "definition",
    "term",
    "resolution",
    "note",
    "interpretation",
    "goal",
    "reason",
];

/// A record's prose, field by field.
pub fn record_prose(fields: &Map<String, Value>) -> String {
    PROSE_FIELDS
        .iter()
        .filter_map(|field| fields.get(*field).and_then(Value::as_str))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Lean declaration source blocks, read lazily per module file, with a
/// repository-wide declaration index built on the first miss.
#[derive(Default)]
pub struct LeanSource {
    root: PathBuf,
    files: HashMap<PathBuf, Option<String>>,
    /// Fully qualified name -> (file, 0-based line), over `TruthCore/**/*.lean`.
    index: Option<HashMap<String, Vec<(PathBuf, usize)>>>,
}

static DECLARATION_KEYWORD: LazyLock<Regex> = LazyLock::new(|| {
    pattern(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|public)\s+)*(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|axiom|instance)\s+([\w.']+)",
    )
});

/// The declared name on `line` (as written, possibly dotted).
fn declared(line: &str) -> Option<&str> {
    DECLARATION_KEYWORD
        .captures(line)
        .ok()
        .flatten()
        .and_then(|captures| captures.get(1))
        .map(|found| found.as_str())
}

/// Every declaration of a Lean source with its fully qualified name, by a
/// lexical `namespace`/`section`/`end` stack (enough to tell modules apart;
/// not Lean's full name resolution).
pub fn qualified_declarations(text: &str) -> Vec<(String, usize)> {
    let mut stack: Vec<Vec<String>> = Vec::new();
    let mut out = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let trimmed = line.trim_start();
        let mut words = trimmed.split_whitespace();
        match words.next() {
            Some("namespace") => stack.push(
                words
                    .next()
                    .unwrap_or_default()
                    .split('.')
                    .map(str::to_owned)
                    .collect(),
            ),
            Some("section") | Some("noncomputable")
                if trimmed.starts_with("section")
                    || trimmed.starts_with("noncomputable section") =>
            {
                stack.push(Vec::new())
            }
            Some("end") if line.starts_with("end") => {
                stack.pop();
            }
            _ => {
                if let Some(name) = declared(line) {
                    let mut parts: Vec<&str> = stack.iter().flatten().map(String::as_str).collect();
                    parts.push(name.strip_prefix("_root_.").unwrap_or(name));
                    out.push((parts.join("."), index));
                }
            }
        }
    }
    out
}

/// The declaration's block: its line and indented continuation, at most 40
/// lines.
fn extract(lines: &[&str], start: usize) -> String {
    let mut block = vec![lines[start]];
    for line in lines.iter().skip(start + 1).take(39) {
        if !line.is_empty() && !line.starts_with(char::is_whitespace) {
            break;
        }
        if line.trim().is_empty() && block.last().is_some_and(|last| last.trim().is_empty()) {
            break;
        }
        block.push(line);
    }
    block.join("\n").trim_end().to_owned()
}

impl LeanSource {
    pub fn new(root: &Path) -> Self {
        Self {
            root: root.to_path_buf(),
            files: HashMap::new(),
            index: None,
        }
    }

    fn file(&mut self, relative: &Path) -> Option<&str> {
        let root = self.root.clone();
        self.files
            .entry(relative.to_path_buf())
            .or_insert_with(|| std::fs::read_to_string(root.join(relative)).ok())
            .as_deref()
    }

    fn build_index(&mut self) {
        fn walk(directory: &Path, root: &Path, out: &mut Vec<PathBuf>) {
            let Ok(entries) = std::fs::read_dir(directory) else {
                return;
            };
            let mut entries: Vec<_> = entries.flatten().collect();
            entries.sort_by_key(|entry| entry.file_name());
            for entry in entries {
                let Ok(kind) = entry.file_type() else {
                    continue;
                };
                let path = entry.path();
                if kind.is_dir() && entry.file_name() != ".lake" {
                    walk(&path, root, out);
                } else if kind.is_file()
                    && path.extension().is_some_and(|ext| ext == "lean")
                    && let Ok(relative) = path.strip_prefix(root)
                {
                    out.push(relative.to_path_buf());
                }
            }
        }
        let mut paths = Vec::new();
        walk(&self.root.join("TruthCore"), &self.root, &mut paths);
        let mut index: HashMap<String, Vec<(PathBuf, usize)>> = HashMap::new();
        for path in paths {
            let Some(text) = self.file(&path).map(str::to_owned) else {
                continue;
            };
            for (name, line) in qualified_declarations(&text) {
                index.entry(name).or_default().push((path.clone(), line));
            }
        }
        self.index = Some(index);
    }

    /// The source block of the fully qualified `declaration`: first in the
    /// module its namespace names (the longest existing prefix file), else
    /// through a repository-wide index of qualified declaration names, else
    /// the unique declaration with that last component. Returns the file,
    /// 1-based line and text.
    pub fn block(&mut self, declaration: &str) -> Option<(String, usize, String)> {
        let parts: Vec<&str> = declaration.split('.').collect();
        let name = *parts.last()?;
        for end in (1..parts.len()).rev() {
            let relative = PathBuf::from(format!("{}.lean", parts[..end].join("/")));
            if !self.root.join(&relative).is_file() {
                continue;
            }
            let Some(text) = self.file(&relative) else {
                continue;
            };
            let lines: Vec<&str> = text.lines().collect();
            if let Some(start) = lines.iter().position(|line| {
                declared(line).is_some_and(|found| found.rsplit('.').next() == Some(name))
            }) {
                let block = extract(&lines, start);
                return Some((relative.to_string_lossy().into_owned(), start + 1, block));
            }
            break;
        }
        if self.index.is_none() {
            self.build_index();
        }
        let index = self.index.as_ref()?;
        let found = index
            .get(declaration)
            .and_then(|places| places.first())
            .cloned()
            .or_else(|| {
                let suffix = format!(".{name}");
                let mut matches = index
                    .iter()
                    .filter(|(qualified, _)| {
                        qualified.ends_with(&suffix) || qualified.as_str() == name
                    })
                    .flat_map(|(_, places)| places.iter());
                match (matches.next(), matches.next()) {
                    (Some(one), None) => Some(one.clone()),
                    _ => None,
                }
            })?;
        let (path, start) = found;
        let text = self.file(&path)?;
        let lines: Vec<&str> = text.lines().collect();
        Some((
            path.to_string_lossy().into_owned(),
            start + 1,
            extract(&lines, start),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_items_and_matching() {
        let query = Query::parse("D(x,y) ↔ ¬CanBeWithout(x,y) for the brute regresses");
        let items: Vec<(&str, &str)> = query
            .items
            .iter()
            .map(|item| (item.kind, item.text.as_str()))
            .collect();
        assert_eq!(
            items,
            [
                ("symbol", "D"),
                ("operator", "↔"),
                ("operator", "¬"),
                ("identifier", "CanBeWithout"),
                ("word", "brute"),
                ("word", "regresses"),
            ]
        );
        let aliases = note_aliases(
            "Write `D(x,y)` for the existing `DependsForBeing x y`, `B(x,y)` for\n`CanBeWithout x y`.",
        );
        assert_eq!(aliases.get("canbewithout").map(String::as_str), Some("B"));
        assert_eq!(
            aliases.get("dependsforbeing").map(String::as_str),
            Some("D")
        );
        let hit = query.matched("imply `D(y,x) ↔ ¬B(y,x)` for a brute regress", &aliases);
        assert_eq!(coverage(&hit), (6, 6));
        // Without the note's notation, `B(` is not CanBeWithout.
        let hit = query.matched("imply `D(y,x) ↔ ¬B(y,x)`", &BTreeMap::new());
        assert_eq!(coverage(&hit), (3, 6));
        let ascii = Query::parse("DependsForBeing <-> ¬CanBeWithout");
        let unicode = Query::parse("DependsForBeing ↔ ¬CanBeWithout");
        assert_eq!(ascii.items, unicode.items);
        let arrow = Query::parse("DependsForBeing → CanBeWithout");
        let none = BTreeMap::new();
        assert_eq!(
            coverage(&arrow.matched("DependsForBeing <-> CanBeWithout", &none)),
            (2, 3)
        );
        assert_eq!(
            coverage(&arrow.matched("DependsForBeing -> CanBeWithout", &none)),
            (3, 3)
        );
        for (spelled, canonical) in [
            ("a /\\ b", "a ∧ b"),
            ("a \\/ b", "a ∨ b"),
            ("a ⇔ b ⇒ c", "a ↔ b → c"),
        ] {
            assert_eq!(Query::parse(spelled).items, Query::parse(canonical).items);
        }
        assert!(!query.substantial(&query.matched("↔ ¬ and not", &BTreeMap::new())));
        assert!(!has_call("BAD(x)", "D"));
        assert_eq!(
            Query::parse("p iff q -> r")
                .items
                .iter()
                .map(|i| i.text.as_str())
                .collect::<Vec<_>>(),
            ["↔", "→"]
        );
    }

    #[test]
    fn references_dates_and_time() {
        assert_eq!(
            issue_references(
                "See #750, (#736) and https://github.com/o/r/pull/1445; not &#123; or a/#12"
            ),
            [750, 736, 1445]
        );
        assert_eq!(
            latest_date("2026-10-31 then (2026-11-09) and 2025-01-01").as_deref(),
            Some("2026-11-09")
        );
        let epoch = parse_epoch("2026-11-15T11:27:00Z").unwrap();
        assert_eq!(format_epoch(epoch), "2026-11-15T11:27:00Z");
        assert_eq!(
            format_epoch(parse_epoch("2024-02-29").unwrap()),
            "2024-02-29T00:00:00Z"
        );
        assert!(parse_epoch("not a date").is_none());
        assert_eq!(
            superseded_lines("a\nSuperseded by the 2026 note\nc").len(),
            1
        );
    }

    #[test]
    fn declarations_resolve_outside_their_namespace_module() {
        let root = std::env::temp_dir().join(format!("truth-lean-source-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let file = root.join("TruthCore/Greek/Physics/BookIV/Chapter8.lean");
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(
            &file,
            "namespace TruthCore.Greek.Physics\nsection\n/-- doc -/\ndef VoidReading (R : Prop) : Prop :=\n  R → ¬ R\nend\nend TruthCore.Greek.Physics\n",
        )
        .unwrap();
        std::fs::write(
            root.join("TruthCore/Greek/Physics.lean"),
            "namespace TruthCore.Greek.Physics\nend TruthCore.Greek.Physics\n",
        )
        .unwrap();
        let mut source = LeanSource::new(&root);
        let (path, line, block) = source.block("TruthCore.Greek.Physics.VoidReading").unwrap();
        assert_eq!(
            (path.as_str(), line),
            ("TruthCore/Greek/Physics/BookIV/Chapter8.lean", 4)
        );
        assert!(block.ends_with("R → ¬ R"));
        assert!(source.block("TruthCore.Greek.Physics.Missing").is_none());
        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn paragraphs_keep_lines() {
        let found = paragraphs("one\ntwo\n\nthree\n", 5);
        assert_eq!(found, [(5, "one\ntwo\n".into()), (8, "three\n".into())]);
    }
}
