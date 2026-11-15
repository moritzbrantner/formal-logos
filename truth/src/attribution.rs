//! `truth attribution-check`: a port of `scripts/attribution_check.py`
//! (`corpus.py attribution-check`, #989), the pre-push attribution
//! self-check for stating claims.
//!
//! For every claim the change adds or alters since `--base` (or whose
//! statement paraphrase or resolved passage changed), the report prints the
//! premise beside the claim's locator and the cached passage text, and the
//! gate fails unless the claim records an `attribution` sentence ("The
//! passage states X, which is the premise."). The check is offline: cached
//! text is shown when usable, missing or stale text is reported as not
//! checked. `--materialize` acquires each selected passage by running
//! `python3 scripts/source_evidence.py materialize PASSAGE` (network
//! acquisition stays Python) and fails on acquisition or integrity errors.
//!
//! The working tree is always the head. Text and problems are Python's byte
//! for byte; Python's crash on a malformed record (a missing `id`, invalid
//! JSON in a changed file) is an `attribution-check error` here.

use crate::{
    Record, check,
    identity::{is_uuid, legacy_uuid},
    pyfmt,
};
use serde::Serialize;
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::Path,
    process::Command,
};

type Obj = Map<String, Value>;
/// The selected claims with their reasons, and the edited passage ids.
type Selection = (Vec<(Obj, String)>, BTreeSet<String>);

pub const ATTRIBUTION_PREFIX: &str = "The passage states ";
pub const MIN_ATTRIBUTION_CHARS: usize = 40;
/// Fields whose change alters what a claim attributes to its source.
const ATTRIBUTED_FIELDS: &[&str] = &[
    "statement_id",
    "source_id",
    "locator",
    "interpretation",
    "attribution",
];
const SCOPE_CHECKLIST: &[&str] = &[
    "quantifier scope: does the passage say all/every/no where the premise does, or only some/this case?",
    "species/genus: does the passage speak of the whole genus the premise uses (every cause, every being), \
     or only one species (efficient causes, bodies, motion)?",
    "temporal and modal scope: does the passage assert what the premise asserts about time, beginning, \
     necessity or possibility, or something narrower?",
];
/// `source_evidence.CACHE`, relative to the checkout.
const CACHE: &str = ".cache/truth-core/sources";

/// One selected claim, as the report shows it.
#[derive(Serialize)]
pub struct Entry {
    pub claim_id: String,
    /// Why it was selected (`new claim`, `changed interpretation`, ...).
    pub reason: String,
    pub statement_id: String,
    /// The statement paraphrase, or `(unknown statement)`.
    pub premise: String,
    pub locator: String,
    pub interpretation: String,
    pub passage_id: String,
    /// The passage kind (`text_witness` when absent).
    pub passage_kind: String,
    pub passage_locator: String,
    /// The passage text shown, or `None` when it was not checked in this run.
    pub text: Option<String>,
    /// Where the text came from, or why it was not checked.
    pub text_source: String,
    /// The recorded `attribution` (Python `str()`), or `None` when missing.
    pub attribution: Option<String>,
}

/// The whole report: the selected claims and the problems that fail the gate.
#[derive(Serialize)]
pub struct Report {
    pub base: String,
    pub claims: Vec<Entry>,
    pub problems: Vec<String>,
}

/// `attribution_check.validate_attribution`: the shape of a recorded
/// attribution (`Err` is the problem message).
pub fn validate_attribution(at: &str, value: &Value) -> Result<(), String> {
    let ok = value.as_str().is_some_and(|text| {
        text.starts_with(ATTRIBUTION_PREFIX)
            && text.trim_matches(pyfmt::is_space).chars().count() >= MIN_ATTRIBUTION_CHARS
    });
    if ok {
        Ok(())
    } else {
        Err(format!(
            "{at}: attribution must be one sentence starting {} that says what the passage states \
             and that it is the premise (at least {MIN_ATTRIBUTION_CHARS} characters)",
            pyfmt::repr_str(ATTRIBUTION_PREFIX)
        ))
    }
}

/// `git ARGS` in `root`; a failure is Python's `git … failed: …` message.
fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    let joined = args.join(" ");
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|error| format!("git {joined} failed: {error}"))?;
    if !output.status.success() {
        let command: Vec<String> = std::iter::once("git")
            .chain(args.iter().copied())
            .map(pyfmt::repr_str)
            .collect();
        let status = output.status.code().unwrap_or(-1);
        return Err(format!(
            "git {joined} failed: Command '[{}]' returned non-zero exit status {status}.",
            command.join(", ")
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| format!("git {joined} failed: {error}"))
}

/// Paths changed from `base` to the working tree, including untracked files;
/// renames appear as a deletion and an addition (`--no-renames`).
fn changed_paths(root: &Path, base: &str) -> Result<Vec<String>, String> {
    let tracked = git(
        root,
        &["diff", "--name-only", "-z", "--no-renames", base, "--"],
    )?;
    let untracked = git(root, &["ls-files", "-z", "--others", "--exclude-standard"])?;
    let paths: BTreeSet<String> = tracked
        .split('\0')
        .chain(untracked.split('\0'))
        .filter(|path| !path.is_empty())
        .map(str::to_owned)
        .collect();
    Ok(paths.into_iter().collect())
}

/// The directory name of `path`'s parent (`Path(path).parent.name`).
fn parent_name(path: &str) -> &str {
    Path::new(path)
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap_or("")
}

/// The kind (singular) of a `corpus/<directory>` name.
fn kind_of(directory: &str) -> Option<&'static str> {
    crate::identity::KIND_DIRS
        .iter()
        .find(|(name, _)| *name == directory)
        .map(|(_, kind)| *kind)
}

/// `corpus_ids.as_uuid_record` for the fields this check reads: a record of
/// a revision from before the uuid migration gets its uuid5 `id` (keeping
/// `legacy_id`) and uuid5 `statement_id`, `source_id` and
/// `interpretation_of`, the claim references the comparison sees.
fn as_uuid_record(kind: &str, record: Value) -> Value {
    let Value::Object(mut out) = record else {
        return record;
    };
    let Some(id) = out.get("id").and_then(Value::as_str).map(str::to_owned) else {
        return Value::Object(out);
    };
    if is_uuid(&id) {
        return Value::Object(out);
    }
    out.insert("legacy_id".into(), Value::String(id.clone()));
    out.insert("id".into(), Value::String(legacy_uuid(kind, &id)));
    if kind == "claim" {
        for (field, target) in [
            ("statement_id", "statement"),
            ("source_id", "source"),
            ("interpretation_of", "claim"),
        ] {
            if let Some(Value::String(value)) = out.get(field)
                && !is_uuid(value)
            {
                let converted = legacy_uuid(target, value);
                out.insert(field.into(), Value::String(converted));
            }
        }
    }
    Value::Object(out)
}

fn parse_json(path: &str, text: &str) -> Result<Value, String> {
    serde_json::from_str(text).map_err(|error| format!("{path}: cannot read JSON: {error}"))
}

/// The JSON record at `revision` (`None`: the working tree), or `None`
/// when absent there.
fn read_at(root: &Path, revision: Option<&str>, path: &str) -> Result<Option<Value>, String> {
    let Some(revision) = revision else {
        let file = root.join(path);
        if !file.is_file() {
            return Ok(None);
        }
        let text = std::fs::read_to_string(&file)
            .map_err(|error| format!("{path}: cannot read JSON: {error}"))?;
        return parse_json(path, &text).map(Some);
    };
    let output = Command::new("git")
        .arg("show")
        .arg(format!("{revision}:{path}"))
        .current_dir(root)
        .output()
        .map_err(|error| format!("git show failed: {error}"))?;
    if !output.status.success() {
        return Ok(None);
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|error| format!("{revision}:{path}: cannot read JSON: {error}"))?;
    let mut record = parse_json(&format!("{revision}:{path}"), &text)?;
    // A revision from before the uuid migration is compared under the same ids.
    let directory = parent_name(path);
    if directory == "passages" {
        if let Value::Object(manifest) = &mut record {
            let passages = match manifest.remove("passages") {
                Some(Value::Array(items)) => items
                    .into_iter()
                    .map(|item| as_uuid_record("passage", item))
                    .collect(),
                _ => Vec::new(),
            };
            manifest.insert("passages".into(), Value::Array(passages));
            if let Some(Value::Object(snapshot)) = manifest.get_mut("snapshot")
                && let Some(Value::String(source)) = snapshot.get("source_id")
                && !is_uuid(source)
            {
                let converted = legacy_uuid("source", source);
                snapshot.insert("source_id".into(), Value::String(converted));
            }
        }
    } else if let Some(kind) = kind_of(directory) {
        record = as_uuid_record(kind, record);
    }
    Ok(Some(record))
}

/// The records of `directory` among `paths` at `revision`, keyed by id in
/// first-seen order (a later file with the same id replaces the record), so
/// a moved file is compared with itself rather than treated as new.
fn records_by_id(
    root: &Path,
    paths: &[String],
    directory: &str,
    revision: Option<&str>,
) -> Result<Vec<(String, Obj)>, String> {
    let prefix = format!("corpus/{directory}/");
    let mut records: Vec<(String, Obj)> = Vec::new();
    for path in paths {
        if !(path.starts_with(&prefix) && path.ends_with(".json")) {
            continue;
        }
        let Some(Value::Object(record)) = read_at(root, revision, path)? else {
            continue;
        };
        let Some(id) = record.get("id").and_then(Value::as_str).map(str::to_owned) else {
            continue;
        };
        match records.iter_mut().find(|(known, _)| *known == id) {
            Some(slot) => slot.1 = record,
            None => records.push((id, record)),
        }
    }
    Ok(records)
}

fn without_labels(value: &Value) -> Value {
    match value {
        Value::Object(map) => Value::Object(
            map.iter()
                .filter(|(key, _)| *key != "label")
                .map(|(key, item)| (key.clone(), without_labels(item)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(without_labels).collect()),
        other => other.clone(),
    }
}

/// Passages whose manifest the change adds or edits (as in the working
/// tree); a manifest unchanged since `base` apart from labels changes none.
fn changed_passage_ids(
    root: &Path,
    paths: &[String],
    base: &str,
) -> Result<BTreeSet<String>, String> {
    let mut changed = BTreeSet::new();
    for path in paths {
        if !(path.starts_with("corpus/passages/") && path.ends_with(".json")) {
            continue;
        }
        let manifest = match read_at(root, None, path)? {
            Some(manifest) if pyfmt::truthy(Some(&manifest)) => manifest,
            _ => continue,
        };
        if let Some(before) = read_at(root, Some(base), path)?
            && without_labels(&before) == without_labels(&manifest)
        {
            continue;
        }
        let entries = manifest.get("passages").and_then(Value::as_array);
        changed.extend(
            entries
                .into_iter()
                .flatten()
                .filter_map(|passage| passage.get("id"))
                .map(pyfmt::text),
        );
    }
    Ok(changed)
}

fn field<'a>(record: &'a Obj, name: &str) -> &'a Value {
    record.get(name).unwrap_or(&Value::Null)
}

fn str_field(record: &Obj, name: &str) -> String {
    pyfmt::text(field(record, name))
}

/// `attribution_check.resolve_passage`: the one passage of the claim's
/// source whose locator prefix starts the claim's locator.
fn resolve_passage<'a>(claim: &Obj, passages: &'a [Record]) -> Result<&'a Obj, String> {
    let source = field(claim, "source_id");
    let locator = claim.get("locator").and_then(Value::as_str).unwrap_or("");
    let matches: Vec<&Obj> = passages
        .iter()
        .map(|record| &record.fields)
        .filter(|passage| {
            field(passage, "source_id") == source
                && passage
                    .get("claim_locator_prefixes")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .any(|prefix| locator.starts_with(prefix))
        })
        .collect();
    match matches.as_slice() {
        [passage] => Ok(passage),
        _ => Err(format!(
            "{}: claim resolves to {} passages; run source_evidence.py check",
            str_field(claim, "id"),
            matches.len()
        )),
    }
}

/// Claims the change adds or alters, whose statement paraphrase changed, or
/// whose resolved passage changed, with the reason, sorted by claim id.
fn changed_claims(
    root: &Path,
    base: &str,
    paths: &[String],
    passages: &[Record],
) -> Result<Selection, String> {
    let before_claims: HashMap<String, Obj> = records_by_id(root, paths, "claims", Some(base))?
        .into_iter()
        .collect();
    let mut selected: BTreeMap<String, (Obj, String)> = BTreeMap::new();
    for (claim_id, after) in records_by_id(root, paths, "claims", None)? {
        let Some(before) = before_claims.get(&claim_id) else {
            selected.insert(claim_id, (after, "new claim".into()));
            continue;
        };
        let fields: Vec<&str> = ATTRIBUTED_FIELDS
            .iter()
            .copied()
            .filter(|name| before.get(*name) != after.get(*name))
            .collect();
        if !fields.is_empty() {
            let reason = format!("changed {}", fields.join(", "));
            selected.insert(claim_id, (after, reason));
        }
    }
    let before_statements: HashMap<String, Obj> =
        records_by_id(root, paths, "statements", Some(base))?
            .into_iter()
            .collect();
    let changed_statements: BTreeSet<String> = records_by_id(root, paths, "statements", None)?
        .into_iter()
        .filter(|(id, after)| {
            before_statements
                .get(id)
                .is_some_and(|before| before.get("paraphrase") != after.get("paraphrase"))
        })
        .map(|(id, _)| id)
        .collect();
    let changed_passages = changed_passage_ids(root, paths, base)?;
    if !changed_statements.is_empty() || !changed_passages.is_empty() {
        for record in check::load_json_dir(root, "claims")? {
            let claim = record.fields;
            let id = str_field(&claim, "id");
            if selected.contains_key(&id) {
                continue;
            }
            let statement = str_field(&claim, "statement_id");
            if changed_statements.contains(&statement) {
                let reason = format!("statement {statement} paraphrase changed");
                selected.insert(id, (claim, reason));
                continue;
            }
            if !changed_passages.is_empty() {
                let passage = str_field(resolve_passage(&claim, passages)?, "id");
                if changed_passages.contains(&passage) {
                    selected.insert(id, (claim, format!("passage {passage} changed")));
                }
            }
        }
    }
    Ok((selected.into_values().collect(), changed_passages))
}

/// `source_evidence.bibliographic_citation`.
fn bibliographic_citation(passage: &Obj) -> String {
    let truthy = |name: &str| pyfmt::truthy(passage.get(name));
    let venue = if truthy("journal") {
        str_field(passage, "journal")
    } else {
        str_field(passage, "publisher")
    };
    let edition = if truthy("edition") {
        format!(", {}", str_field(passage, "edition"))
    } else {
        String::new()
    };
    let identifier = if truthy("isbn") {
        format!("ISBN {}", str_field(passage, "isbn"))
    } else {
        format!("doi:{}", str_field(passage, "doi"))
    };
    let at = if truthy("pages") {
        format!("pp. {}", str_field(passage, "pages"))
    } else {
        str_field(passage, "section")
    };
    format!(
        "{}, {} ({venue}, {}{edition}; {identifier}), {at}",
        str_field(passage, "author"),
        str_field(passage, "title"),
        str_field(passage, "year"),
    )
}

fn is_bibliographic(passage: &Obj) -> bool {
    passage.get("kind").and_then(Value::as_str) == Some("bibliographic_span")
}

/// Python `Path.read_text()`: UTF-8 with universal newlines.
fn read_text(path: &Path) -> Result<String, String> {
    let text =
        std::fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    Ok(text.replace("\r\n", "\n").replace('\r', "\n"))
}

/// Runs `python3 scripts/source_evidence.py materialize PASSAGE` in `root`;
/// `Err` is its `source evidence error` message.
fn materialize(root: &Path, passage_id: &str) -> Result<(), String> {
    let output = Command::new("python3")
        .args(["scripts/source_evidence.py", "materialize", passage_id])
        .current_dir(root)
        .output()
        .map_err(|error| format!("cannot run python3: {error}"))?;
    if output.status.success() {
        return Ok(());
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    let last = stderr
        .lines()
        .rev()
        .find(|line| !line.trim().is_empty())
        .unwrap_or("source_evidence.py materialize failed");
    Err(last
        .strip_prefix("source evidence error: ")
        .unwrap_or(last)
        .to_owned())
}

/// The passage text, or `None` and why it is unavailable. `--materialize`
/// always re-materializes; without it a cached text is shown only when the
/// change leaves the passage unchanged.
fn passage_text(
    root: &Path,
    passage: &Obj,
    materialize_now: bool,
    changed: bool,
) -> (Option<String>, String) {
    if is_bibliographic(passage) {
        return (
            None,
            format!(
                "bibliographic span: read {} in the edition itself",
                bibliographic_citation(passage)
            ),
        );
    }
    let id = str_field(passage, "id");
    let relative = format!("{CACHE}/{id}.txt");
    let cached = root.join(&relative);
    let command = format!("python3 scripts/source_evidence.py materialize {id}");
    if materialize_now {
        if let Err(error) = materialize(root, &id) {
            return (None, format!("cannot materialize: {error}"));
        }
        return match read_text(&cached) {
            Ok(text) => (Some(text), format!("{relative}, materialized now")),
            Err(error) => (None, format!("cannot materialize: {error}")),
        };
    }
    if changed {
        return (
            None,
            format!(
                "the change edits this passage, so a cached text may be stale: run {command} or use --materialize"
            ),
        );
    }
    if !cached.is_file() {
        return (None, format!("not materialized: run {command}"));
    }
    match read_text(&cached) {
        Ok(text) => (
            Some(text),
            format!("{relative}, cached and not re-verified now"),
        ),
        Err(error) => (None, format!("not materialized: {error}")),
    }
}

/// Python `clip`: `text` cut to its first and last `limit / 2` characters
/// around an omission note (`limit <= 0`: never).
pub fn clip(text: &str, limit: i64) -> String {
    let length = text.chars().count();
    if limit <= 0 || length as i64 <= limit {
        return text.to_owned();
    }
    let half = (limit / 2) as usize;
    let head = pyfmt::head(text, half);
    // Python `text[-0:]` is the whole text.
    let tail = if half == 0 {
        text
    } else {
        let start = text
            .char_indices()
            .nth(length - half)
            .map_or(text.len(), |(index, _)| index);
        &text[start..]
    };
    format!(
        "{head}\n[... {} characters omitted; read the whole file ...]\n{tail}",
        length as i64 - limit
    )
}

/// `attribution_check.report` without the formatting: the working tree
/// against `base`. `Err` is an `attribution-check error`.
pub fn report(root: &Path, base: &str, materialize_now: bool) -> Result<Report, String> {
    let statements: HashMap<String, Obj> = check::load_json_dir(root, "statements")?
        .into_iter()
        .map(|record| (str_field(&record.fields, "id"), record.fields))
        .collect();
    let passages = check::passage_index(root)?;
    let paths = changed_paths(root, base)?;
    let (claims, edited) = changed_claims(root, base, &paths, &passages)?;
    let mut report = Report {
        base: base.to_owned(),
        claims: Vec::new(),
        problems: Vec::new(),
    };
    for (claim, reason) in claims {
        let claim_id = str_field(&claim, "id");
        let statement_id = str_field(&claim, "statement_id");
        let premise = statements
            .get(&statement_id)
            .and_then(|statement| statement.get("paraphrase"))
            .map_or_else(|| "(unknown statement)".to_owned(), pyfmt::text);
        let passage = resolve_passage(&claim, &passages)?;
        let passage_id = str_field(passage, "id");
        let (text, text_source) =
            passage_text(root, passage, materialize_now, edited.contains(&passage_id));
        if text.is_none() && materialize_now && !is_bibliographic(passage) {
            report.problems.push(format!(
                "{claim_id}: passage {passage_id} materialization failed ({text_source})"
            ));
        }
        let attribution = claim
            .get("attribution")
            .filter(|value| pyfmt::truthy(Some(value)));
        match attribution {
            None => report
                .problems
                .push(format!("{claim_id}: no `attribution` recorded")),
            Some(value) => {
                if let Err(problem) = validate_attribution(&claim_id, value) {
                    report.problems.push(problem);
                }
            }
        }
        let kind = passage
            .get("kind")
            .filter(|kind| pyfmt::truthy(Some(kind)))
            .map_or_else(|| "text_witness".to_owned(), pyfmt::text);
        report.claims.push(Entry {
            reason,
            statement_id,
            premise,
            locator: str_field(&claim, "locator"),
            interpretation: str_field(&claim, "interpretation"),
            passage_kind: kind,
            passage_locator: str_field(passage, "locator"),
            text,
            text_source,
            attribution: attribution.map(pyfmt::text),
            passage_id,
            claim_id,
        });
    }
    Ok(report)
}

/// The text Python prints to stdout (without the final newline).
pub fn format(report: &Report, max_chars: i64) -> String {
    let base = &report.base;
    if report.claims.is_empty() {
        return format!("attribution-check: no new or changed stating claim since {base}");
    }
    let mut lines = vec![
        format!(
            "attribution-check: {} new or changed stating claim(s) since {base}",
            report.claims.len()
        ),
        "For each claim, compare the premise with what the passage itself says:".to_owned(),
    ];
    lines.extend(SCOPE_CHECKLIST.iter().map(|item| format!("  - {item}")));
    lines.push(format!(
        "Then record `attribution`: {ATTRIBUTION_PREFIX}X, which is the premise. If the passage only \
         bears on the premise or states something narrower, replace the stating claim by a `supports` \
         relation with a gap note (#987), or state the narrower reading as its own statement."
    ));
    for entry in &report.claims {
        lines.push(String::new());
        lines.push(format!(
            "== {} ({}) -> {}",
            entry.claim_id, entry.reason, entry.statement_id
        ));
        lines.push(format!("premise: {}", entry.premise));
        lines.push(format!("claim locator: {}", entry.locator));
        lines.push(format!("claim interpretation: {}", entry.interpretation));
        lines.push(format!(
            "passage: {} ({}), {}",
            entry.passage_id, entry.passage_kind, entry.passage_locator
        ));
        match &entry.text {
            None => lines.push(format!(
                "passage text: NOT CHECKED in this run ({})",
                entry.text_source
            )),
            Some(text) => {
                lines.push(format!(
                    "passage text ({}, {} characters):",
                    entry.text_source,
                    text.chars().count()
                ));
                lines.push(clip(pyfmt::rstrip(text), max_chars));
            }
        }
        lines.push(format!(
            "attribution: {}",
            entry.attribution.as_deref().unwrap_or("MISSING")
        ));
    }
    lines.join("\n")
}

/// What Python prints to stderr when the gate fails (empty when it passes).
pub fn format_problems(problems: &[String]) -> String {
    if problems.is_empty() {
        return String::new();
    }
    let mut text = String::from("\nattribution-check FAILED:\n");
    for problem in problems {
        text.push_str(&format!("  {problem}\n"));
    }
    text
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn attribution_shape() {
        let good = json!(
            "The passage states that whatever is changed in any way is in potency, which is the premise."
        );
        assert!(validate_attribution("c.json", &good).is_ok());
        for bad in [
            json!("It is stated somewhere in the passage, I think."),
            json!("The passage states X."),
            json!(7),
        ] {
            let error = validate_attribution("c.json", &bad).unwrap_err();
            assert!(error.starts_with(
                "c.json: attribution must be one sentence starting 'The passage states '"
            ));
        }
    }

    #[test]
    fn clip_matches_python_slices() {
        assert_eq!(clip("abcdef", 0), "abcdef");
        assert_eq!(clip("abcdef", 6), "abcdef");
        assert_eq!(
            clip("abcdef", 4),
            "ab\n[... 2 characters omitted; read the whole file ...]\nef"
        );
        // `text[-0:]` is the whole text.
        assert_eq!(
            clip("abc", 1),
            "\n[... 2 characters omitted; read the whole file ...]\nabc"
        );
        assert_eq!(
            clip("äöüßé", 2),
            "ä\n[... 3 characters omitted; read the whole file ...]\né"
        );
    }

    #[test]
    fn legacy_claims_compare_under_uuid_ids() {
        let record = as_uuid_record(
            "claim",
            json!({"id": "C", "statement_id": "STMT-P", "source_id": "SRC", "locator": "l"}),
        );
        assert_eq!(record["id"], legacy_uuid("claim", "C"));
        assert_eq!(record["legacy_id"], "C");
        assert_eq!(record["statement_id"], legacy_uuid("statement", "STMT-P"));
        assert_eq!(record["source_id"], legacy_uuid("source", "SRC"));
        let migrated = json!({"id": legacy_uuid("claim", "C"), "statement_id": "STMT-P"});
        assert_eq!(as_uuid_record("claim", migrated.clone()), migrated);
    }

    #[test]
    fn bibliographic_citation_names_the_edition() {
        let passage = json!({"author": "A", "title": "T", "publisher": "P", "year": 2000,
                             "isbn": "9780000000002", "pages": "1-2"});
        assert_eq!(
            bibliographic_citation(passage.as_object().unwrap()),
            "A, T (P, 2000; ISBN 9780000000002), pp. 1-2"
        );
    }
}
