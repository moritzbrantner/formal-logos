//! `truth type-lints`: advisory metadata lints over the elaborated types that
//! `truth bind-check` caches ([`crate::bind_types`]). Recurring review findings
//! (#2103 curation pass 2) that the records alone cannot decide:
//!
//! 1. **Whole-argument `tests` without a logical premise** (#2141). A `tests`
//!    relation whose object is a whole argument that registers a logical
//!    premise ([`LOGICAL_PREMISES`], for example `ExcludedMiddle`), while the
//!    subject result's certificate type does not reach that premise's
//!    declaration. The model then certifies the nonlogical premises only.
//! 2. **Definition not in the type.** A statement's `definition_ids` link a
//!    definition whose `lean_declaration` the statement's bound Lean type
//!    does not reach. When the type reaches the declaration of another sense
//!    of the same disambiguation, the warning names that sense instead (de
//!    dicto linked for de re, an adopted potency linked where the type
//!    quantifies over a free `InPotency`).
//!
//! "Reaches" is computed by Lean (`scripts/BindTypes.lean`, `reaches`): the
//! tracked constants occurring in the elaborated type or in the values of the
//! project definitions it uses, unfolded transitively; a bound variable never
//! counts. A statement's bound type is every binder or result type whose head
//! is the statement's `lean_declaration`, in every fresh cache entry. Only
//! fresh entries are read: a stale or missing entry leaves its result
//! unchecked (reported, never guessed). Every finding is a warning: the
//! command never fails, and none of this is verification evidence.
//!
//! With a base ([`Scope::Since`]), the report is the corpus-wide findings
//! minus those the same lints find on the base records, matched by
//! [`finding_key`]. No base cache exists offline, so the base run reads
//! head's elaborated types and treats the results `bind-check --affected`
//! selects as unknown: a finding that depends on a changed certificate is
//! reported again rather than missed.

use crate::{
    Corpus,
    bind_types::{self, Inputs, Lookup},
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::Path,
};

type Obj = Map<String, Value>;

/// Lean declarations of the logical premises a whole-argument test must
/// certify: general logical principles an argument registers as separate
/// premises. Their meaning is fixed by Lean, so a model of an argument's
/// other premises does not certify them by satisfying those.
pub const LOGICAL_PREMISES: &[&str] = &[
    "TruthCore.Logic.ExcludedMiddle",
    "TruthCore.Logic.PredicativeExcludedMiddle",
];

fn text<'a>(record: &'a Obj, key: &str) -> &'a str {
    record.get(key).and_then(Value::as_str).unwrap_or_default()
}

fn list<'a>(record: &'a Obj, key: &str) -> Vec<&'a str> {
    record
        .get(key)
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect()
}

/// The constants the exporter reports under `reaches`: every definition's and
/// sense's Lean declaration and the logical premises.
pub fn tracked_constants(corpus: &Corpus) -> BTreeSet<String> {
    let mut tracked: BTreeSet<String> = LOGICAL_PREMISES.iter().map(|d| (*d).to_owned()).collect();
    for definition in corpus.records("definitions") {
        let declaration = text(definition, "lean_declaration");
        if !declaration.is_empty() {
            tracked.insert(declaration.to_owned());
        }
    }
    for disambiguation in corpus.records("disambiguations") {
        for sense in disambiguation
            .get("senses")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            if let Some(declaration) = sense.get("lean_declaration").and_then(Value::as_str)
                && !declaration.is_empty()
            {
                tracked.insert(declaration.to_owned());
            }
        }
    }
    tracked
}

/// One described type: its head constant and the tracked constants it
/// reaches (`None` when the description predates `reaches`).
#[derive(Clone)]
struct Typed {
    head: String,
    reaches: Option<BTreeSet<String>>,
}

fn typed(item: &Value) -> Typed {
    Typed {
        head: item["head"].as_str().unwrap_or_default().to_owned(),
        reaches: item["reaches"].as_array().map(|names| {
            names
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        }),
    }
}

/// The described binders and result of every result with a fresh cache
/// entry, and the results left unchecked (stale, missing or without
/// `reaches`), each with its reason.
pub struct Described {
    types: BTreeMap<String, Vec<Typed>>,
    pub unchecked: BTreeMap<String, String>,
    /// Fresh entries whose `reaches` were computed for another tracked set
    /// (definitions or senses added or removed since): read for logical
    /// premises, which are always tracked, but not for definitions.
    tracking_outdated: BTreeSet<String>,
    /// Tracked constant -> kind (`definition`, `projection`, …).
    kinds: BTreeMap<String, String>,
    /// Why nothing could be read, when the cache is unreadable.
    pub note: Option<String>,
}

impl Described {
    /// Reads the cache of `root` for every result of `corpus`. An unreadable
    /// cache leaves every result unchecked, with a note.
    pub fn load(root: &Path, corpus: &Corpus) -> Self {
        let (cache, note) = match bind_types::load(root) {
            Ok(cache) => (cache, None),
            Err(error) => (
                None,
                Some(format!("the elaborated-type cache is unreadable ({error})")),
            ),
        };
        let tracked = tracked_constants(corpus);
        let current = bind_types::tracked_digest(tracked.iter().map(String::as_str));
        let inputs = Inputs::new(root);
        let mut types = BTreeMap::new();
        let mut unchecked = BTreeMap::new();
        let mut tracking_outdated = BTreeSet::new();
        for (id, record) in corpus.records_by_id("results") {
            let lookup = match &cache {
                Some(cache) => cache.lookup(&inputs, &record.fields),
                None => Lookup::Missing,
            };
            match lookup {
                Lookup::Fresh { description, .. } => {
                    let items: Vec<Typed> = description["binders"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .chain(std::iter::once(&description["result"]))
                        .map(typed)
                        .collect();
                    if items.iter().all(|item| item.reaches.is_some()) {
                        if cache.as_ref().and_then(|cache| cache.tracked_digest_of(id))
                            != Some(current.as_str())
                        {
                            tracking_outdated.insert(id.to_owned());
                        }
                        types.insert(id.to_owned(), items);
                    } else {
                        unchecked.insert(id.to_owned(), "cached before `reaches`".into());
                    }
                }
                Lookup::Stale(reason) => {
                    unchecked.insert(id.to_owned(), format!("stale: {reason}"));
                }
                Lookup::Missing => {
                    let reason = if note.is_some() {
                        "cache unreadable"
                    } else {
                        "not in the cache"
                    };
                    unchecked.insert(id.to_owned(), reason.into());
                }
            }
        }
        let kinds = cache
            .map(|cache| {
                cache
                    .tracked_kinds
                    .iter()
                    .filter_map(|(name, kind)| Some((name.clone(), kind.as_str()?.to_owned())))
                    .collect()
            })
            .unwrap_or_default();
        Self {
            types,
            unchecked,
            tracking_outdated,
            kinds,
            note,
        }
    }

    /// Built from exporter descriptions keyed by result id and constant
    /// kinds (tests).
    pub fn from_descriptions(
        descriptions: &BTreeMap<String, Value>,
        kinds: &[(&str, &str)],
    ) -> Self {
        let types = descriptions
            .iter()
            .map(|(id, description)| {
                let items = description["binders"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .chain(std::iter::once(&description["result"]))
                    .map(typed)
                    .collect();
                (id.clone(), items)
            })
            .collect();
        Self {
            types,
            unchecked: BTreeMap::new(),
            tracking_outdated: BTreeSet::new(),
            kinds: kinds
                .iter()
                .map(|(name, kind)| ((*name).to_owned(), (*kind).to_owned()))
                .collect(),
            note: None,
        }
    }

    /// Marks results as described for another tracked set (tests).
    #[cfg(test)]
    fn outdate(mut self, results: &[&str]) -> Self {
        self.tracking_outdated
            .extend(results.iter().map(|id| (*id).to_owned()));
        self
    }

    /// The types read for the base run of [`Scope::Since`]: head's, except
    /// that the results whose certificate may have changed (`None`: every
    /// result) are unknown at base.
    fn at_base(&self, affected: Option<&BTreeSet<String>>) -> Self {
        let changed = |id: &String| affected.is_none_or(|affected| affected.contains(id));
        let mut unchecked = self.unchecked.clone();
        let types = self
            .types
            .iter()
            .filter(|(id, _)| {
                let keep = !changed(id);
                if !keep {
                    unchecked.insert((*id).clone(), "certificate inputs changed".into());
                }
                keep
            })
            .map(|(id, items)| (id.clone(), items.clone()))
            .collect();
        Self {
            types,
            unchecked,
            tracking_outdated: self.tracking_outdated.clone(),
            kinds: self.kinds.clone(),
            note: self.note.clone(),
        }
    }

    /// Everything a result's certificate type reaches (binders and result).
    fn certificate(&self, result: &str) -> Option<BTreeSet<&str>> {
        self.types.get(result).map(|items| {
            items
                .iter()
                .flat_map(|item| item.reaches.iter().flatten().map(String::as_str))
                .collect()
        })
    }
}

/// The scope of a run: everything, or the findings new since a base corpus.
pub enum Scope<'b> {
    All,
    /// The corpus-wide findings at head minus those the same lints find on
    /// the base records (head rules on base data). The base's elaborated
    /// types are not available offline, so the base run reads head's cache,
    /// except for the results whose certificate may have changed (affected,
    /// or with a new or changed record): those are unknown at base, and the
    /// findings that depend on them at head count as new.
    Since {
        base: &'b Corpus,
        /// The results whose certificate may have changed since the base, as
        /// `bind-check --affected` selects them (`scripts/affected_results.py`:
        /// the result record, its Comparator config directory, or a module
        /// its Challenge or Solution imports transitively changed); `None`
        /// when the change selects every result.
        affected_results: Option<BTreeSet<String>>,
    },
}

/// A finding's identity across base and head: lint kind plus the IDs and
/// declarations it is about, never labels.
fn finding_key(kind: &str, finding: &Value) -> String {
    let fields: &[&str] = match kind {
        "tests_missing_logical_premise" => &[
            "relation_id",
            "subject_result_id",
            "premise_statement_id",
            "lean_declaration",
        ],
        _ => &["statement_id", "definition_id", "definition_declaration"],
    };
    let mut key = kind.to_owned();
    for field in fields {
        key.push('\0');
        key.push_str(finding[*field].as_str().unwrap_or_default());
    }
    key
}

/// The lints over `corpus` with the types in `described`, within `scope`.
pub fn report(corpus: &Corpus, described: &Described, scope: &Scope) -> Value {
    let mut head = lint(corpus, described);
    let Scope::Since {
        base,
        affected_results,
    } = scope
    else {
        head["scope"] = json!("all");
        return head;
    };
    // A result whose record is new or changed counts as affected even when
    // the caller's selection missed it.
    let affected = affected_results.as_ref().map(|affected| {
        let mut affected = affected.clone();
        affected.extend(
            corpus
                .records_by_id("results")
                .filter(|(id, record)| {
                    base.get("results", id)
                        .is_none_or(|old| old.fields != record.fields)
                })
                .map(|(id, _)| id.to_owned()),
        );
        affected
    });
    let at_base = lint(base, &described.at_base(affected.as_ref()));
    for (kind, preexisting) in [
        ("tests_missing_logical_premise", "tests_preexisting"),
        ("definition_not_in_type", "definition_links_preexisting"),
    ] {
        let known: BTreeSet<String> = at_base[kind]
            .as_array()
            .into_iter()
            .flatten()
            .map(|finding| finding_key(kind, finding))
            .collect();
        let all = head[kind].as_array().cloned().unwrap_or_default();
        let total = all.len();
        let new: Vec<Value> = all
            .into_iter()
            .filter(|finding| !known.contains(&finding_key(kind, finding)))
            .collect();
        head[preexisting] = json!(total - new.len());
        head[kind] = Value::Array(new);
    }
    head["scope"] = json!("since_base");
    head
}

/// The corpus-wide lints over `corpus` with the types in `described`.
fn lint(corpus: &Corpus, described: &Described) -> Value {
    let statements: HashMap<&str, &Obj> = corpus
        .records_by_id("statements")
        .map(|(id, record)| (id, &record.fields))
        .collect();
    let label = |id: &str| -> String {
        statements
            .get(id)
            .map(|record| text(record, "label").to_owned())
            .unwrap_or_default()
    };
    let mut results_of: HashMap<&str, Vec<&str>> = HashMap::new();
    for (id, record) in corpus.records_by_id("results") {
        results_of
            .entry(text(&record.fields, "argument_id"))
            .or_default()
            .push(id);
    }

    // 1. Whole-argument tests that do not certify a registered logical premise.
    let mut tests_warnings = Vec::new();
    let mut tests_unchecked = 0usize;
    let mut tests_judged = 0usize;
    for (id, record) in corpus.records_by_id("relations") {
        let relation = &record.fields;
        if text(relation, "predicate") != "tests" || text(relation, "object_kind") != "argument" {
            continue;
        }
        let object = text(relation, "object_id");
        let Some(argument) = corpus.get("arguments", object) else {
            continue;
        };
        let subjects: Vec<&str> = match text(relation, "subject_kind") {
            "result" => vec![text(relation, "subject_id")],
            "argument" => results_of
                .get(text(relation, "subject_id"))
                .cloned()
                .unwrap_or_default(),
            _ => Vec::new(),
        };
        let logical: Vec<(&str, &str)> = list(&argument.fields, "premise_statement_ids")
            .into_iter()
            .filter_map(|premise| {
                let declaration = statements
                    .get(premise)
                    .map(|s| text(s, "lean_declaration"))?;
                LOGICAL_PREMISES
                    .contains(&declaration)
                    .then_some((premise, declaration))
            })
            .collect();
        if logical.is_empty() {
            continue;
        }
        tests_judged += 1;
        for subject in subjects {
            let Some(reached) = described.certificate(subject) else {
                tests_unchecked += 1;
                continue;
            };
            for (premise, declaration) in &logical {
                if !reached.contains(declaration) {
                    tests_warnings.push(json!({
                        "relation_id": id,
                        "subject_result_id": subject,
                        "argument_id": text(relation, "object_id"),
                        "premise_statement_id": premise,
                        "premise_label": label(premise),
                        "lean_declaration": declaration,
                    }));
                }
            }
        }
    }

    // 2. Linked definitions the statement's bound type does not reach.
    // Only entries described for the current tracked set: an older entry may
    // lack a definition added since.
    let mut bound: HashMap<&str, BTreeSet<&str>> = HashMap::new();
    for (result, items) in &described.types {
        if described.tracking_outdated.contains(result) {
            continue;
        }
        for item in items {
            if let Some(reaches) = &item.reaches {
                bound
                    .entry(item.head.as_str())
                    .or_default()
                    .extend(reaches.iter().map(String::as_str));
            }
        }
    }
    let mut sense_of: HashMap<&str, (&str, &str, &str)> = HashMap::new();
    let mut tagged: HashMap<&str, BTreeSet<&str>> = HashMap::new();
    for (id, record) in corpus.records_by_id("disambiguations") {
        for sense in record
            .fields
            .get("senses")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_object)
        {
            let declaration = text(sense, "lean_declaration");
            if !declaration.is_empty() {
                sense_of.insert(declaration, (id, text(sense, "label"), declaration));
            }
            // A parameter tag (#1784) says that a binder of that declaration
            // expresses the sense: the authored link a free parameter needs.
            for tag in sense
                .get("lean_parameters")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_object)
            {
                tagged
                    .entry(text(sense, "definition_id"))
                    .or_default()
                    .insert(text(tag, "declaration"));
            }
        }
    }
    let mut definition_warnings = Vec::new();
    let (mut links_judged, mut links_unchecked, mut links_primitive, mut links_tagged) =
        (0usize, 0usize, 0usize, 0usize);
    for (id, record) in corpus.records_by_id("statements") {
        let statement = &record.fields;
        let declaration = text(statement, "lean_declaration");
        let linked = list(statement, "definition_ids");
        if declaration.is_empty() || linked.is_empty() {
            continue;
        }
        for definition_id in linked {
            let Some(definition) = corpus.get("definitions", definition_id) else {
                continue;
            };
            let defined = text(&definition.fields, "lean_declaration");
            if defined.is_empty() {
                continue;
            }
            // Only a definition with a value fixes a meaning a type can fail
            // to carry. A primitive (a structure field, an inductive, an
            // opaque constant) is by convention taken as a free parameter,
            // and an unseen kind is not judged.
            if described.kinds.get(defined).map(String::as_str) != Some("definition") {
                links_primitive += 1;
                continue;
            }
            if tagged
                .get(definition_id)
                .is_some_and(|declarations| declarations.contains(declaration))
            {
                links_tagged += 1;
                continue;
            }
            links_judged += 1;
            let Some(reached) = bound.get(declaration) else {
                links_unchecked += 1;
                continue;
            };
            if reached.contains(defined) {
                continue;
            }
            let other_senses: Vec<&str> = sense_of
                .get(defined)
                .map(|(disambiguation, _, _)| {
                    reached
                        .iter()
                        .copied()
                        .filter(|reached| {
                            sense_of
                                .get(reached)
                                .is_some_and(|(other, _, _)| other == disambiguation)
                        })
                        .collect()
                })
                .unwrap_or_default();
            definition_warnings.push(json!({
                "statement_id": id,
                "statement_label": label(id),
                "definition_id": definition_id,
                "definition_label": text(&definition.fields, "label"),
                "definition_declaration": defined,
                "sense_label": sense_of.get(defined).map(|(_, label, _)| *label),
                "type_uses_other_senses": other_senses.iter().map(|declaration| json!({
                    "lean_declaration": declaration,
                    "sense_label": sense_of.get(declaration).map(|(_, label, _)| *label),
                })).collect::<Vec<_>>(),
            }));
        }
    }
    json!({
        "results_unchecked": described.unchecked.len(),
        "results_tracking_outdated": described.tracking_outdated.len(),
        "cache_note": described.note,
        "tests_judged": tests_judged,
        "tests_unchecked_subjects": tests_unchecked,
        "tests_missing_logical_premise": tests_warnings,
        "definition_links_judged": links_judged,
        "definition_links_primitive_or_unseen": links_primitive,
        "definition_links_parameter_tagged": links_tagged,
        "definition_links_unchecked": links_unchecked,
        "definition_not_in_type": definition_warnings,
    })
}

/// The text form of [`report`]. IDs are left for the caller's alias
/// humanization.
pub fn format(report: &Value) -> String {
    let warnings = |key: &str| report[key].as_array().cloned().unwrap_or_default();
    let (tests, definitions) = (
        warnings("tests_missing_logical_premise"),
        warnings("definition_not_in_type"),
    );
    let mut lines = vec![
        format!(
            "Type metadata lints ({}; advisory warnings, never a failure; elaborated types from \
             the bind-check cache)",
            if report["scope"] == "all" {
                "every record"
            } else {
                "findings new since the base"
            }
        ),
        format!(
            "whole-argument tests with a logical premise: {} judged, {} not certifying it, {} \
             subject result(s) unchecked",
            report["tests_judged"],
            tests.len(),
            report["tests_unchecked_subjects"]
        ),
        format!(
            "statement-definition links to defined constants: {} judged, {} not reached by the \
             type, {} unchecked (statement bound by no fresh cache entry); not judged: {} to a \
             primitive or unseen constant, {} covered by a parameter tag",
            report["definition_links_judged"],
            definitions.len(),
            report["definition_links_unchecked"],
            report["definition_links_primitive_or_unseen"],
            report["definition_links_parameter_tagged"],
        ),
    ];
    if report["scope"] == "since_base" {
        lines.push(format!(
            "not repeated: {} test finding(s) and {} definition-link finding(s) the base \
             already had",
            report["tests_preexisting"], report["definition_links_preexisting"]
        ));
    }
    if report["results_unchecked"].as_u64().unwrap_or(0) > 0 {
        lines.push(format!(
            "{} result(s) have no fresh cache entry; run `truth bind-check` (or `--affected \
             --base REV`) after `lake build` to check them",
            report["results_unchecked"]
        ));
    }
    if let Some(note) = report["cache_note"].as_str() {
        lines.push(format!("unchecked: {note}"));
    }
    if report["results_tracking_outdated"].as_u64().unwrap_or(0) > 0 {
        lines.push(format!(
            "{} fresh result(s) were described for an older set of tracked definitions and are \
             not read for definition links; rerun `truth bind-check` to refresh them",
            report["results_tracking_outdated"]
        ));
    }
    if !tests.is_empty() {
        lines.push(String::new());
        lines.push(
            "Warning: these `tests` relations target a whole argument that registers a logical \
             premise, but the subject's certificate type does not reach it. Test the exact \
             premises the model certifies, or include the logical premise in the certificate:"
                .into(),
        );
        for entry in &tests {
            lines.push(format!(
                "  relation {}: result {} tests argument {} without {} ({})",
                entry["relation_id"].as_str().unwrap_or_default(),
                entry["subject_result_id"].as_str().unwrap_or_default(),
                entry["argument_id"].as_str().unwrap_or_default(),
                entry["premise_statement_id"].as_str().unwrap_or_default(),
                entry["lean_declaration"].as_str().unwrap_or_default(),
            ));
        }
    }
    if !definitions.is_empty() {
        lines.push(String::new());
        lines.push(
            "Warning: these statements link a definition whose Lean declaration their bound \
             type does not reach. Link the definition the type actually uses, tag the \
             parameter that expresses the sense (`lean_parameters`), or bind the type to the \
             linked one. By definition:"
                .into(),
        );
        let mut grouped: BTreeMap<&str, Vec<&Value>> = BTreeMap::new();
        for entry in &definitions {
            grouped
                .entry(entry["definition_id"].as_str().unwrap_or_default())
                .or_default()
                .push(entry);
        }
        for (definition, entries) in grouped {
            let first = entries[0];
            lines.push(format!(
                "  {definition} ({}{}): {} statement(s)",
                first["definition_declaration"].as_str().unwrap_or_default(),
                first["sense_label"]
                    .as_str()
                    .map(|label| format!(", sense {label}"))
                    .unwrap_or_default(),
                entries.len(),
            ));
            for entry in entries.iter().take(GROUP_LIMIT) {
                let others: Vec<String> = entry["type_uses_other_senses"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|other| {
                        other["sense_label"]
                            .as_str()
                            .or(other["lean_declaration"].as_str())
                            .unwrap_or_default()
                            .to_owned()
                    })
                    .collect();
                let note = if others.is_empty() {
                    String::new()
                } else {
                    format!(" (the type uses {})", others.join(", "))
                };
                lines.push(format!(
                    "    {}{note}",
                    entry["statement_id"].as_str().unwrap_or_default()
                ));
            }
            if entries.len() > GROUP_LIMIT {
                lines.push(format!(
                    "    … and {} more (--json lists all)",
                    entries.len() - GROUP_LIMIT
                ));
            }
        }
    }
    lines.join("\n")
}

/// Statements listed per definition in the text report.
const GROUP_LIMIT: usize = 5;

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs, path::PathBuf};

    struct Checkout(PathBuf);

    impl Checkout {
        fn new(name: &str) -> Self {
            use std::sync::atomic::{AtomicU32, Ordering};
            static NEXT: AtomicU32 = AtomicU32::new(0);
            let path = std::env::temp_dir().join(format!(
                "truth-type-lints-{name}-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let _ = fs::remove_dir_all(&path);
            fs::create_dir_all(path.join("corpus")).unwrap();
            Self(path)
        }

        fn write(&self, kind: &str, mut record: Value) {
            // The structural loader's required fields, where a test omits them.
            let required: &[(&str, Value)] = match kind {
                "statements" => &[("paraphrase", json!("p"))],
                "arguments" => &[("meaning", json!("m")), ("inference_ids", json!(["I"]))],
                "results" => &[
                    ("challenge_module", json!("c")),
                    ("comparator_config", json!("f")),
                    ("status", json!("solution-present")),
                ],
                "definitions" => &[
                    ("term", json!("t")),
                    ("definition", json!("d")),
                    ("basis", json!("stipulative")),
                ],
                "disambiguations" => &[("term", json!("t")), ("resolution", json!("r"))],
                _ => &[],
            };
            for (key, value) in required {
                if record.get(*key).is_none() {
                    record[*key] = value.clone();
                }
            }
            let directory = self.0.join("corpus").join(kind);
            fs::create_dir_all(&directory).unwrap();
            let id = record["id"].as_str().unwrap().to_owned();
            fs::write(directory.join(format!("{id}.json")), record.to_string()).unwrap();
        }
    }

    impl Drop for Checkout {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn item(head: &str, reaches: &[&str]) -> Value {
        json!({"head": head, "prop": true, "type": head, "reaches": reaches})
    }

    /// EM is the logical premise of ARG (with P). CTRL-OK's certificate
    /// reaches EM, CTRL-BAD's does not. Statement S (declaration `T.S`)
    /// links DEF-DE-RE (`T.deRe`, sense DE_RE of DISAMB) and DEF-POT (`T.pot`);
    /// its bound type reaches `T.deDicto`, the other sense, and not `T.pot`.
    fn fixture() -> Checkout {
        let checkout = Checkout::new("fixture");
        checkout.write(
            "statements",
            json!({"id": "EM", "label": "Excluded middle",
                   "lean_declaration": "TruthCore.Logic.ExcludedMiddle"}),
        );
        checkout.write("statements", json!({"id": "P", "lean_declaration": "T.P"}));
        checkout.write("statements", json!({"id": "C", "lean_declaration": "T.C"}));
        checkout.write(
            "statements",
            json!({"id": "S", "label": "S holds", "lean_declaration": "T.S",
                   "definition_ids": ["DEF-DE-RE", "DEF-POT", "DEF-USED", "DEF-FIELD",
                                      "DEF-TAGGED"]}),
        );
        checkout.write(
            "arguments",
            json!({"id": "ARG", "premise_statement_ids": ["EM", "P"],
                   "conclusion_statement_id": "C"}),
        );
        for id in ["CTRL-OK", "CTRL-BAD", "USE-S"] {
            checkout.write(
                "results",
                json!({"id": id, "argument_id": format!("{id}-ARG"), "theorem": id,
                       "solution_module": "M"}),
            );
        }
        for (id, subject) in [("REL-OK", "CTRL-OK"), ("REL-BAD", "CTRL-BAD")] {
            checkout.write(
                "relations",
                json!({"id": id, "subject_kind": "result", "subject_id": subject,
                       "predicate": "tests", "object_kind": "argument", "object_id": "ARG"}),
            );
        }
        for (id, declaration) in [
            ("DEF-DE-RE", "T.deRe"),
            ("DEF-DE-DICTO", "T.deDicto"),
            ("DEF-POT", "T.pot"),
            ("DEF-USED", "T.used"),
            ("DEF-FIELD", "T.Frame.field"),
            ("DEF-TAGGED", "T.tagged"),
        ] {
            checkout.write(
                "definitions",
                json!({"id": id, "label": id, "lean_declaration": declaration}),
            );
        }
        checkout.write(
            "disambiguations",
            json!({"id": "DISAMB", "senses": [
                {"id": "s1", "label": "DE_RE_1", "lean_declaration": "T.deRe"},
                {"id": "s2", "label": "DE_DICTO_1", "lean_declaration": "T.deDicto"}]}),
        );
        // A parameter of T.S is tagged as expressing the sense of DEF-TAGGED.
        checkout.write(
            "disambiguations",
            json!({"id": "DISAMB-TAG", "senses": [
                {"id": "t1", "label": "TAGGED_1", "definition_id": "DEF-TAGGED",
                 "lean_parameters": [{"declaration": "T.S", "parameter": "Tagged"}]}]}),
        );
        checkout
    }

    const KINDS: &[(&str, &str)] = &[
        ("T.deRe", "definition"),
        ("T.deDicto", "definition"),
        ("T.pot", "definition"),
        ("T.used", "definition"),
        ("T.tagged", "definition"),
        ("T.Frame.field", "projection"),
    ];

    fn described() -> Described {
        Described::from_descriptions(
            &BTreeMap::from([
                (
                    "CTRL-OK".to_owned(),
                    json!({"binders": [], "result": item("T.Cert", &["TruthCore.Logic.ExcludedMiddle"])}),
                ),
                (
                    "CTRL-BAD".to_owned(),
                    json!({"binders": [item("T.P", &[])], "result": item("T.Model", &[])}),
                ),
                (
                    "USE-S".to_owned(),
                    json!({"binders": [item("T.S", &["T.deDicto", "T.used"])],
                       "result": item("T.C", &[])}),
                ),
            ]),
            KINDS,
        )
    }

    #[test]
    fn flags_uncertified_logical_premises_and_unreached_definitions() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        let report = report(&corpus, &described(), &Scope::All);
        let tests = report["tests_missing_logical_premise"].as_array().unwrap();
        assert_eq!(tests.len(), 1, "{report}");
        assert_eq!(tests[0]["relation_id"], "REL-BAD");
        assert_eq!(tests[0]["premise_statement_id"], "EM");
        assert_eq!(report["tests_judged"], 2);

        let definitions = report["definition_not_in_type"].as_array().unwrap();
        let flagged: Vec<&str> = definitions
            .iter()
            .map(|entry| entry["definition_id"].as_str().unwrap())
            .collect();
        assert_eq!(flagged, ["DEF-DE-RE", "DEF-POT"]);
        assert_eq!(
            definitions[0]["type_uses_other_senses"],
            json!([{"lean_declaration": "T.deDicto", "sense_label": "DE_DICTO_1"}])
        );
        assert_eq!(definitions[1]["type_uses_other_senses"], json!([]));
        assert_eq!(report["definition_links_judged"], 3);
        // The structure field is a primitive; the tagged parameter carries its sense.
        assert_eq!(report["definition_links_primitive_or_unseen"], 1);
        assert_eq!(report["definition_links_parameter_tagged"], 1);
        let text = format(&report);
        assert!(text.contains("relation REL-BAD: result CTRL-BAD tests argument ARG without EM"));
        assert!(
            text.contains(
                "  DEF-DE-RE (T.deRe, sense DE_RE_1): 1 statement(s)\n    S (the type uses DE_DICTO_1)"
            ),
            "{text}"
        );
        assert!(
            text.ends_with("  DEF-POT (T.pot): 1 statement(s)\n    S"),
            "{text}"
        );
    }

    #[test]
    fn unchecked_and_since_base_scopes() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        // No description at all: nothing is guessed.
        let empty = Described::from_descriptions(&BTreeMap::new(), KINDS);
        let report = report(&corpus, &empty, &Scope::All);
        assert_eq!(report["tests_missing_logical_premise"], json!([]));
        assert_eq!(report["tests_unchecked_subjects"], 2);
        assert_eq!(report["definition_not_in_type"], json!([]));
        assert_eq!(report["definition_links_unchecked"], 3);
        // A tested argument that gained its logical premise since the base:
        // the finding is new, although the relations did not change.
        let base = fixture();
        base.write(
            "arguments",
            json!({"id": "ARG", "premise_statement_ids": ["P"], "conclusion_statement_id": "C"}),
        );
        let base_corpus = Corpus::load(&base.0).unwrap();
        let gained = report_since(&corpus, &base_corpus);
        assert_eq!(gained["tests_judged"], 2);
        assert_eq!(flagged_tests(&gained), ["REL-BAD"]);
        assert_eq!(gained["tests_preexisting"], 0);
        // Its definition-link findings already existed at base.
        assert_eq!(gained["definition_not_in_type"], json!([]));
        assert_eq!(gained["definition_links_preexisting"], 2);
        // Entries described for an older tracked set are not read for
        // definition links (S is bound only by USE-S).
        let outdated = super::report(&corpus, &described().outdate(&["USE-S"]), &Scope::All);
        assert_eq!(outdated["definition_not_in_type"], json!([]));
        assert_eq!(outdated["definition_links_unchecked"], 3);
        assert_eq!(
            outdated["tests_missing_logical_premise"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
    }

    #[test]
    fn an_unreadable_cache_leaves_everything_unchecked() {
        let checkout = fixture();
        fs::create_dir_all(checkout.0.join(".cache")).unwrap();
        fs::write(checkout.0.join(bind_types::CACHE), "not json").unwrap();
        let corpus = Corpus::load(&checkout.0).unwrap();
        let described = Described::load(&checkout.0, &corpus);
        assert!(described.note.is_some());
        let report = report(&corpus, &described, &Scope::All);
        assert_eq!(report["results_unchecked"], 3);
        assert_eq!(report["tests_missing_logical_premise"], json!([]));
        assert!(format(&report).contains("unchecked: the elaborated-type cache is unreadable"));
    }

    fn report_since(corpus: &Corpus, base: &Corpus) -> Value {
        since(corpus, &described(), base, Some(&[]))
    }

    fn since(
        corpus: &Corpus,
        described: &Described,
        base: &Corpus,
        affected: Option<&[&str]>,
    ) -> Value {
        report(
            corpus,
            described,
            &Scope::Since {
                base,
                affected_results: affected
                    .map(|ids| ids.iter().map(|id| (*id).to_owned()).collect()),
            },
        )
    }

    fn flagged_tests(report: &Value) -> Vec<String> {
        report["tests_missing_logical_premise"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["relation_id"].as_str().unwrap().to_owned())
            .collect()
    }

    fn flagged_links(report: &Value) -> Vec<String> {
        report["definition_not_in_type"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["definition_id"].as_str().unwrap().to_owned())
            .collect()
    }

    /// Findings the base already had are not repeated; the text says how many.
    #[test]
    fn a_preexisting_finding_is_not_reported() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        let same = report_since(&corpus, &corpus);
        assert_eq!(same["tests_missing_logical_premise"], json!([]));
        assert_eq!(same["definition_not_in_type"], json!([]));
        assert_eq!(same["tests_preexisting"], 1);
        assert_eq!(same["definition_links_preexisting"], 2);
        // The counts stay corpus-wide.
        assert_eq!(same["tests_judged"], 2);
        let text = format(&same);
        assert!(text.contains("findings new since the base"), "{text}");
        assert!(
            text.contains("not repeated: 1 test finding(s) and 2 definition-link finding(s)"),
            "{text}"
        );
        // A label change alone does not make a finding new.
        let base = fixture();
        base.write(
            "statements",
            json!({"id": "S", "label": "S was called this",
                   "lean_declaration": "T.S",
                   "definition_ids": ["DEF-DE-RE", "DEF-POT", "DEF-USED", "DEF-FIELD",
                                      "DEF-TAGGED"]}),
        );
        let relabeled = report_since(&corpus, &Corpus::load(&base.0).unwrap());
        assert_eq!(relabeled["definition_not_in_type"], json!([]));
    }

    /// #2167 review: a relation newly designated `tests` (same endpoints),
    /// and a premise of the tested argument rebound to a logical premise,
    /// yield new findings although nothing else changed.
    #[test]
    fn a_new_tests_designation_or_rebound_premise_is_reported() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        let relation = fixture();
        relation.write(
            "relations",
            json!({"id": "REL-BAD", "subject_kind": "result", "subject_id": "CTRL-BAD",
                   "predicate": "supports", "object_kind": "argument", "object_id": "ARG"}),
        );
        let redesignated = report_since(&corpus, &Corpus::load(&relation.0).unwrap());
        assert_eq!(flagged_tests(&redesignated), ["REL-BAD"], "{redesignated}");
        let statement = fixture();
        statement.write(
            "statements",
            json!({"id": "EM", "lean_declaration": "T.EM"}),
        );
        let rebound = report_since(&corpus, &Corpus::load(&statement.0).unwrap());
        assert_eq!(flagged_tests(&rebound), ["REL-BAD"], "{rebound}");
    }

    /// #2167 review: a test whose subject's certificate changed yields a new
    /// finding although the relation and the tested argument did not change.
    #[test]
    fn a_changed_subject_certificate_is_reported() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        // CTRL-OK's refreshed certificate no longer reaches EM.
        let refreshed = Described::from_descriptions(
            &BTreeMap::from([
                (
                    "CTRL-OK".to_owned(),
                    json!({"binders": [item("T.P", &[])], "result": item("T.Cert", &[])}),
                ),
                (
                    "CTRL-BAD".to_owned(),
                    json!({"binders": [item("T.P", &[])], "result": item("T.Model", &[])}),
                ),
            ]),
            KINDS,
        );
        // Unaffected and unchanged: head's cache stands for the base too.
        let unchanged = since(&corpus, &refreshed, &corpus, Some(&[]));
        assert_eq!(flagged_tests(&unchanged), Vec::<String>::new());
        // Its Lean inputs changed (bind-check's affected selection): the new
        // defect is reported, the pre-existing one is not.
        let affected = since(&corpus, &refreshed, &corpus, Some(&["CTRL-OK"]));
        assert_eq!(flagged_tests(&affected), ["REL-OK"], "{affected}");
        assert_eq!(affected["tests_preexisting"], 1);
        // A change that selects every result reports every finding.
        let full = since(&corpus, &refreshed, &corpus, None);
        assert_eq!(flagged_tests(&full), ["REL-BAD", "REL-OK"]);
        // Its result record changed (here its theorem), even if the
        // selection missed it: reported as well.
        let base = fixture();
        base.write(
            "results",
            json!({"id": "CTRL-OK", "argument_id": "CTRL-OK-ARG", "theorem": "old",
                   "solution_module": "M"}),
        );
        let record = since(
            &corpus,
            &refreshed,
            &Corpus::load(&base.0).unwrap(),
            Some(&[]),
        );
        assert_eq!(flagged_tests(&record), ["REL-OK"]);
    }

    /// #2167 review: a definition-link finding is new when the linked
    /// definition's declaration changed, or when the statement's Lean
    /// definition stopped using the linked constant (its binding results'
    /// certificates changed), although the statement record did not change.
    #[test]
    fn a_changed_definition_link_input_is_reported() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        // DEF-USED pointed at T.deDicto, which S's type reaches; now at T.used.
        // Head's T.S reaches T.deDicto only, so the link is now unreached.
        let head_types = Described::from_descriptions(
            &BTreeMap::from([(
                "USE-S".to_owned(),
                json!({"binders": [item("T.S", &["T.deDicto"])], "result": item("T.C", &[])}),
            )]),
            KINDS,
        );
        let base = fixture();
        base.write(
            "definitions",
            json!({"id": "DEF-USED", "label": "DEF-USED", "lean_declaration": "T.deDicto"}),
        );
        let redefined = since(
            &corpus,
            &head_types,
            &Corpus::load(&base.0).unwrap(),
            Some(&[]),
        );
        assert_eq!(flagged_links(&redefined), ["DEF-USED"], "{redefined}");
        // T.S stopped using T.used: USE-S (which imports T.S's module) is
        // affected, so its old findings are unknown at base and its new one
        // is reported; the pre-existing ones on S are reported again rather
        // than missed.
        let stopped = since(&corpus, &head_types, &corpus, Some(&["USE-S"]));
        assert_eq!(
            flagged_links(&stopped),
            ["DEF-DE-RE", "DEF-POT", "DEF-USED"],
            "{stopped}"
        );
        // Without that change, the same types at base and head add nothing.
        let unchanged = since(&corpus, &head_types, &corpus, Some(&[]));
        assert_eq!(flagged_links(&unchanged), Vec::<String>::new());
    }

    #[test]
    fn tracked_constants_cover_definitions_senses_and_logical_premises() {
        let checkout = fixture();
        let corpus = Corpus::load(&checkout.0).unwrap();
        let tracked = tracked_constants(&corpus);
        for name in [
            "T.deRe",
            "T.deDicto",
            "T.pot",
            "TruthCore.Logic.ExcludedMiddle",
            "TruthCore.Logic.PredicativeExcludedMiddle",
        ] {
            assert!(tracked.contains(name), "{name}");
        }
        assert!(!tracked.contains("T.S"));
    }
}
