//! Sense-indexed terms.
//!
//! Each disambiguation gives its term a `term_label` (PRIOR) and its senses
//! an opaque uuid plus a stable display label TERM_n (PRIOR_1).
//!
//! - [`SenseLabels`]: which sense label each disambiguated term takes in a
//!   record (Python `scripts/sense_labels.py`);
//! - the sense index `truth check` validates arguments against (Python
//!   `corpus.sense_index`, `argument_term_senses`, `bridged`);
//! - the sense-mixing report, the legacy allowlist and its shrink-only
//!   ratchet (Python `scripts/sense_index.py report|allowlist|ratchet`).

use crate::{Corpus, Record as Entry, identity::Aliases};
use serde::Serialize;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

type Record = Map<String, Value>;

struct Sense<'a> {
    label: &'a str,
    term: &'a str,
}

/// Python `sense_labels_from_data`: senses by definition, with the
/// statements and arguments records refer to.
pub struct SenseLabels<'a> {
    statements: HashMap<&'a str, &'a Record>,
    arguments: HashMap<&'a str, &'a Record>,
    by_definition: HashMap<&'a str, Vec<Sense<'a>>>,
    by_id: HashMap<&'a str, &'a str>,
}

fn text<'a>(record: &'a Record, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn string<'a>(record: &'a Record, field: &str) -> Option<&'a str> {
    record.get(field).and_then(Value::as_str)
}

fn list<'a>(record: &'a Record, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

impl<'a> SenseLabels<'a> {
    pub fn new(corpus: &'a Corpus) -> Self {
        let by_id_of = |kind| {
            corpus
                .records(kind)
                .into_iter()
                .map(|record| (text(record, "id"), record))
                .collect::<HashMap<_, _>>()
        };
        let mut by_definition: HashMap<&str, Vec<Sense>> = HashMap::new();
        let mut by_id = HashMap::new();
        let mut seen = HashSet::new();
        for disambiguation in corpus.records("disambiguations") {
            let term = text(disambiguation, "term_label");
            let senses = disambiguation.get("senses").and_then(Value::as_array);
            for sense in senses.into_iter().flatten().filter_map(Value::as_object) {
                let id = text(sense, "id");
                if !seen.insert(id) {
                    continue;
                }
                let label = text(sense, "label");
                by_id.insert(id, label);
                by_definition
                    .entry(text(sense, "definition_id"))
                    .or_default()
                    .push(Sense { label, term });
            }
        }
        SenseLabels {
            statements: by_id_of("statements"),
            arguments: by_id_of("arguments"),
            by_definition,
            by_id,
        }
    }

    /// Python `record_definitions`.
    fn definitions(&self, record: &'a Record, with_argument: bool) -> Vec<&'a str> {
        let mut definitions = Vec::new();
        if record.contains_key("definition") && record.contains_key("term") {
            definitions.push(text(record, "id"));
        }
        definitions.extend(list(record, "definition_ids"));
        if let Some(statement) = self.statements.get(text(record, "statement_id")) {
            definitions.extend(list(statement, "definition_ids"));
        }
        if with_argument && let Some(argument) = self.arguments.get(text(record, "argument_id")) {
            definitions.extend(self.definitions(argument, false));
        }
        if record.contains_key("conclusion_statement_id") {
            let ids = std::iter::once(text(record, "conclusion_statement_id"))
                .chain(list(record, "premise_statement_ids"))
                .chain(list(record, "commitment_statement_ids"));
            for sid in ids {
                if let Some(statement) = self.statements.get(sid) {
                    definitions.extend(list(statement, "definition_ids"));
                }
            }
        }
        definitions
    }

    /// Python `record_sense_labels`: term -> sorted sense labels.
    pub fn labels(&self, record: &'a Record) -> BTreeMap<String, Vec<String>> {
        let mut labels: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for definition in self.definitions(record, true) {
            for sense in self.by_definition.get(definition).into_iter().flatten() {
                labels
                    .entry(sense.term.to_owned())
                    .or_default()
                    .insert(sense.label.to_owned());
            }
        }
        let mut declared: Vec<(&String, &Value)> = Vec::new();
        if let Some(Value::Object(map)) = record.get("term_senses") {
            declared.extend(map);
        }
        if let Some(argument) = self.arguments.get(text(record, "argument_id"))
            && let Some(Value::Object(map)) = argument.get("term_senses")
        {
            declared.extend(map);
        }
        for (term, sense) in declared {
            if let Some(label) = sense.as_str().and_then(|id| self.by_id.get(id)) {
                labels
                    .entry(term.clone())
                    .or_default()
                    .insert((*label).to_owned());
            }
        }
        labels
            .into_iter()
            .map(|(term, values)| (term, values.into_iter().collect()))
            .collect()
    }
}

/// Python `format_sense_labels`: `PRIOR_1, CAUSE_2`.
pub fn format_labels(labels: &BTreeMap<String, Vec<String>>) -> String {
    labels
        .values()
        .flatten()
        .cloned()
        .collect::<Vec<_>>()
        .join(", ")
}
/// One sense of the index (Python `sense_index` entry).
#[derive(Clone, PartialEq)]
pub(crate) struct IndexedSense {
    pub(crate) id: String,
    pub(crate) label: String,
    pub(crate) definition_id: String,
    pub(crate) term: String,
}

/// Python `sense_index`: senses by uuid and the senses each definition carries.
#[derive(Default)]
pub(crate) struct SenseIndex {
    pub(crate) by_id: HashMap<String, IndexedSense>,
    pub(crate) by_definition: HashMap<String, Vec<String>>,
}

pub(crate) fn sense_index<'a>(
    disambiguations: impl IntoIterator<Item = &'a Entry>,
) -> Result<SenseIndex, String> {
    let mut index = SenseIndex::default();
    let mut order: Vec<String> = Vec::new();
    let mut term_definition: HashMap<(String, String), String> = HashMap::new();
    for disambiguation in disambiguations {
        let fields = &disambiguation.fields;
        let senses = fields.get("senses").and_then(Value::as_array);
        for sense in senses.into_iter().flatten() {
            let field = |key| sense.get(key).and_then(Value::as_str).unwrap_or_default();
            let entry = IndexedSense {
                id: field("id").to_owned(),
                label: field("label").to_owned(),
                definition_id: field("definition_id").to_owned(),
                term: text(fields, "term_label").to_owned(),
            };
            let known = index.by_id.get(&entry.id);
            if let Some(known) = known
                && *known != entry
            {
                return Err(format!(
                    "{}: sense {} is already {} ({}) of {}",
                    disambiguation.path, entry.id, known.label, known.definition_id, known.term
                ));
            }
            let key = (entry.term.clone(), entry.definition_id.clone());
            let first = term_definition
                .entry(key)
                .or_insert_with(|| entry.id.clone());
            if *first != entry.id {
                return Err(format!(
                    "{}: {} already has sense {first} under {}",
                    disambiguation.path, entry.definition_id, entry.term
                ));
            }
            if known.is_none() {
                index
                    .by_definition
                    .entry(entry.definition_id.clone())
                    .or_default()
                    .push(entry.id.clone());
                order.push(entry.id.clone());
                index.by_id.insert(entry.id.clone(), entry);
            }
        }
    }
    let mut labels: HashMap<(&str, &str), &str> = HashMap::new();
    for id in &order {
        let entry = &index.by_id[id];
        let first = labels
            .entry((entry.term.as_str(), entry.label.as_str()))
            .or_insert(entry.id.as_str());
        if *first != entry.id {
            return Err(format!(
                "corpus/disambiguations: sense label {} names two senses",
                entry.label
            ));
        }
    }
    Ok(index)
}

/// Python `argument_term_senses`: term label -> sense ids used.
pub(crate) fn argument_term_senses(
    argument: &Record,
    statements: &HashMap<&str, &Record>,
    index: &SenseIndex,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut definitions: Vec<&str> = list(argument, "definition_ids");
    let ids = std::iter::once(text(argument, "conclusion_statement_id"))
        .chain(list(argument, "premise_statement_ids"))
        .chain(list(argument, "commitment_statement_ids"));
    for sid in ids {
        if let Some(statement) = statements.get(sid) {
            definitions.extend(list(statement, "definition_ids"));
        }
    }
    let mut used: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for definition in definitions {
        for id in index.by_definition.get(definition).into_iter().flatten() {
            let sense = &index.by_id[id];
            used.entry(sense.term.clone())
                .or_default()
                .insert(sense.id.clone());
        }
    }
    used
}

/// Python `bridged`: the bridges for `term` connect every sense it uses.
pub(crate) fn bridged(term: &str, used: &BTreeSet<String>, bridges: &[Value]) -> bool {
    let mut edges: HashMap<&str, Vec<&str>> = HashMap::new();
    for bridge in bridges {
        let end = |key| bridge.get(key).and_then(Value::as_str).unwrap_or_default();
        if end("term") == term {
            edges.entry(end("from")).or_default().push(end("to"));
            edges.entry(end("to")).or_default().push(end("from"));
        }
    }
    let Some(start) = used.iter().next() else {
        return true;
    };
    let mut seen: HashSet<&str> = HashSet::from([start.as_str()]);
    let mut frontier = vec![start.as_str()];
    while let Some(node) = frontier.pop() {
        for next in edges.get(node).into_iter().flatten() {
            if seen.insert(next) {
                frontier.push(next);
            }
        }
    }
    used.iter().all(|sense| seen.contains(sense.as_str()))
}

/// Python `senses_without_distinct_declaration`: (path, sense) for every
/// sense without a `lean_declaration` or sharing one within its record.
pub(crate) fn senses_without_distinct_declaration<'a>(
    disambiguations: impl IntoIterator<Item = &'a Entry>,
) -> Vec<(&'a str, &'a Record)> {
    let mut missing = Vec::new();
    for disambiguation in disambiguations {
        let senses: Vec<&Record> = disambiguation
            .fields
            .get("senses")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_object)
            .collect();
        let mut declared: HashMap<Option<&str>, usize> = HashMap::new();
        for sense in &senses {
            *declared
                .entry(string(sense, "lean_declaration"))
                .or_default() += 1;
        }
        for sense in senses {
            let declaration = string(sense, "lean_declaration");
            if declaration.is_none() || declared[&declaration] > 1 {
                missing.push((disambiguation.path.as_str(), sense));
            }
        }
    }
    missing
}

// ---------------------------------------------------------------------------
// The sense-mixing report and the legacy allowlist (Python
// `scripts/sense_index.py report|allowlist|ratchet`, `corpus.sense_mixing`).

/// The legacy allowlists (#1233), relative to the checkout.
pub const ALLOWLIST: &str = "corpus/sense-index-allowlist.json";
/// The generated migration note (`report --write`).
pub const NOTE: &str = "docs/notes/sense-index-migration.md";

/// One argument using several senses of one term without a connecting
/// sense bridge (Python `sense_mixing` entry).
#[derive(Debug, Serialize, PartialEq)]
pub struct Mixing {
    pub path: String,
    pub argument_id: String,
    pub term: String,
    /// Sorted sense uuids.
    pub sense_ids: Vec<String>,
    /// Sorted sense labels.
    pub labels: Vec<String>,
}

/// A sense that is not its own Lean type (Python
/// `senses_without_distinct_declaration` entry).
#[derive(Debug, Serialize, PartialEq)]
pub struct Undeclared {
    pub path: String,
    pub disambiguation_id: String,
    pub id: String,
    pub label: String,
    pub lean_declaration: Option<String>,
}

/// Python `sense_mixing`: arguments whose terms take several senses without
/// connecting bridges, in argument file order and term order; a premise-free
/// `sense_mixing_control` argument is skipped.
pub(crate) fn mixing_in<'a>(
    arguments: impl IntoIterator<Item = &'a Entry>,
    statements: &HashMap<&str, &Record>,
    index: &SenseIndex,
) -> Vec<Mixing> {
    let empty = Vec::new();
    let mut mixing = Vec::new();
    for argument in arguments {
        let fields = &argument.fields;
        if fields.get("sense_mixing_control") == Some(&Value::Bool(true)) {
            continue;
        }
        let bridges = fields
            .get("sense_bridges")
            .and_then(Value::as_array)
            .unwrap_or(&empty);
        for (term, senses) in argument_term_senses(fields, statements, index) {
            if senses.len() > 1 && !bridged(&term, &senses, bridges) {
                let mut labels: Vec<String> = senses
                    .iter()
                    .map(|id| index.by_id[id].label.clone())
                    .collect();
                labels.sort();
                mixing.push(Mixing {
                    path: argument.path.clone(),
                    argument_id: text(fields, "id").to_owned(),
                    term,
                    sense_ids: senses.into_iter().collect(),
                    labels,
                });
            }
        }
    }
    mixing
}

/// The sense-mixing report of a corpus.
#[derive(Debug, Serialize)]
pub struct Report {
    pub mixing: Vec<Mixing>,
    pub senses_without_lean_declaration: Vec<Undeclared>,
    /// Number of disambiguation records.
    pub disambiguations: usize,
    /// Number of senses they list.
    pub senses: usize,
}

/// The current mixing and undeclared senses (Python `sense_index.mixing()`
/// and `undeclared()`); fails on an inconsistent sense index.
pub fn report(corpus: &Corpus) -> Result<Report, String> {
    let disambiguations = corpus.entries("disambiguations");
    let index = sense_index(disambiguations.iter().copied())?;
    let statements: HashMap<&str, &Record> = corpus
        .records("statements")
        .into_iter()
        .map(|record| (text(record, "id"), record))
        .collect();
    let mixing = mixing_in(corpus.entries("arguments"), &statements, &index);
    let ids: HashMap<&str, &str> = disambiguations
        .iter()
        .map(|record| (record.path.as_str(), text(&record.fields, "id")))
        .collect();
    let undeclared = senses_without_distinct_declaration(disambiguations.iter().copied())
        .into_iter()
        .map(|(path, sense)| Undeclared {
            path: path.to_owned(),
            disambiguation_id: ids[path].to_owned(),
            id: text(sense, "id").to_owned(),
            label: text(sense, "label").to_owned(),
            lean_declaration: string(sense, "lean_declaration").map(str::to_owned),
        })
        .collect();
    let senses = disambiguations
        .iter()
        .map(|record| {
            record
                .fields
                .get("senses")
                .and_then(Value::as_array)
                .map_or(0, Vec::len)
        })
        .sum();
    Ok(Report {
        mixing,
        senses_without_lean_declaration: undeclared,
        disambiguations: disambiguations.len(),
        senses,
    })
}

impl Report {
    /// Python `allowlist_data`: `{arguments: {argument: {term: [sense ids]}},
    /// senses_without_lean_declaration: [sense ids]}`, sorted.
    pub fn allowlist(&self) -> Value {
        let mut arguments: BTreeMap<&str, BTreeMap<&str, &Vec<String>>> = BTreeMap::new();
        for entry in &self.mixing {
            arguments
                .entry(&entry.argument_id)
                .or_default()
                .insert(&entry.term, &entry.sense_ids);
        }
        let senses: BTreeSet<&str> = self
            .senses_without_lean_declaration
            .iter()
            .map(|sense| sense.id.as_str())
            .collect();
        json!({"arguments": arguments, "senses_without_lean_declaration": senses})
    }

    /// The allowlist file as `allowlist --write` writes it (Python
    /// `json.dumps(data, indent=2, ensure_ascii=False) + "\n"`).
    pub fn allowlist_text(&self) -> String {
        let mut text = serde_json::to_string_pretty(&self.allowlist()).unwrap_or_default();
        text.push('\n');
        text
    }

    /// Python `report_text`: the generated migration note.
    pub fn text(&self) -> String {
        let entries = &self.mixing;
        let arguments: BTreeSet<&str> = entries.iter().map(|e| e.argument_id.as_str()).collect();
        let single: Vec<&Mixing> = entries.iter().filter(|e| !e.term.contains('_')).collect();
        let single_arguments: BTreeSet<&str> =
            single.iter().map(|e| e.argument_id.as_str()).collect();
        let undeclared: BTreeSet<&str> = self
            .senses_without_lean_declaration
            .iter()
            .map(|sense| sense.id.as_str())
            .collect();
        let mut lines = vec![
            "# Sense-index migration".to_owned(),
            String::new(),
            "Generated by `python3 scripts/sense_index.py report --write`; do not edit by hand.".to_owned(),
            String::new(),
            "Owner direction (2026-11-07): one argument uses one sense per disambiguated term,".to_owned(),
            "and an argument valid in several senses is recorded once per sense".to_owned(),
            "(docs/corpus-model.md, \"Sense-indexed terms\"). The migration gave each of the".to_owned(),
            format!("{} disambiguations a `term_label` and uuid senses labelled TERM_n.", self.disambiguations),
            String::new(),
            format!("{} existing arguments use two or more senses of one term without a", arguments.len()),
            format!("sense bridge ({} term uses). They are not rewritten: each is listed in", entries.len()),
            format!("`{ALLOWLIST}`, so `corpus.py check` reports them as one"),
            "warning. A new argument, or an existing one that starts using a sense not".to_owned(),
            "allowlisted for it, is an error. To clear an entry, split the argument into one".to_owned(),
            "argument per sense, or list the premise relating the senses in `sense_bridges`,".to_owned(),
            "then regenerate the allowlist (`python3 scripts/sense_index.py allowlist --write`).".to_owned(),
            String::new(),
            format!("Of these, {} arguments mix senses of a single-word", single_arguments.len()),
            format!("term ({} uses, e.g. PRIOR, CAUSE, GOD, NECESSARY). The rest mix the senses", single.len()),
            "of a compound disambiguation whose `term` names several related words (for example".to_owned(),
            "\"potency and mutability\"); there the senses are often different words rather than".to_owned(),
            "rival senses of one word, and splitting the record into one disambiguation per word".to_owned(),
            "may clear the entry without splitting the argument.".to_owned(),
            String::new(),
            "Senses are distinct Lean types: each sense names its own `lean_declaration`. Of the".to_owned(),
            format!("{} senses, {} have no distinct Lean declaration (none, or", self.senses, undeclared.len()),
            "the same constant as another sense of the record); they are allowlisted in the same file".to_owned(),
            "and are not finished senses. The allowlists may only shrink (#1233):".to_owned(),
            "`python3 scripts/sense_index.py ratchet --base <merge-base>` fails on any added entry.".to_owned(),
            String::new(),
            "| Argument | Term | Senses |".to_owned(),
            "| --- | --- | --- |".to_owned(),
        ];
        let mut sorted: Vec<&Mixing> = entries.iter().collect();
        sorted.sort_by(|a, b| (&a.argument_id, &a.term).cmp(&(&b.argument_id, &b.term)));
        for entry in sorted {
            lines.push(format!(
                "| `{}` | {} | {} |",
                entry.argument_id,
                entry.term,
                entry.labels.join(", ")
            ));
        }
        lines.join("\n") + "\n"
    }
}

/// One flat allowlist entry: (argument, term, sense) or (sense,).
pub type AllowlistEntry = Vec<String>;

/// Python `allowlist_entries`: the flat entries of allowlist `data`, each
/// argument named by the uuid it resolves to among `aliases` (arguments)
/// when given. Fields of the wrong shape contribute nothing.
pub fn allowlist_entries(
    data: &Value,
    aliases: Option<&Aliases>,
) -> Result<BTreeSet<AllowlistEntry>, String> {
    let mut flat = BTreeSet::new();
    let arguments = data.get("arguments").and_then(Value::as_object);
    for (argument, terms) in arguments.into_iter().flatten() {
        let identity = match aliases {
            None => argument.clone(),
            Some(aliases) => match aliases.resolve(argument, Some(&["arguments"])) {
                Ok(id) => id,
                Err(crate::identity::Unresolved::Unknown) => argument.clone(),
                Err(crate::identity::Unresolved::Ambiguous(found)) => {
                    return Err(format!(
                        "{argument:?} names several records: {}; pass a uuid",
                        aliases.describe(&found)
                    ));
                }
            },
        };
        for (term, ids) in terms.as_object().into_iter().flatten() {
            for sense in ids
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
            {
                flat.insert(vec![identity.clone(), term.clone(), sense.to_owned()]);
            }
        }
    }
    let senses = data
        .get("senses_without_lean_declaration")
        .and_then(Value::as_array);
    for sense in senses.into_iter().flatten().filter_map(Value::as_str) {
        flat.insert(vec![sense.to_owned()]);
    }
    Ok(flat)
}

/// The outcome of [`ratchet`].
#[derive(Debug, Serialize)]
pub struct Ratchet {
    /// Head entries no longer needed (may be removed).
    pub stale: Vec<AllowlistEntry>,
    /// Head entries the base did not have (the failure).
    pub added: Vec<AllowlistEntry>,
    /// Whether the allowlist exists at the base revision.
    pub compared: bool,
}

/// Python `sense_index.ratchet`: the head allowlist (`head`, the validated
/// file or `{}`) against the current needs and against the allowlist at
/// `base`; the legacy allowlists may only shrink (#1233).
pub fn ratchet(
    root: &Path,
    corpus: &Corpus,
    report: &Report,
    head: &Value,
    base: &str,
) -> Result<Ratchet, String> {
    let aliases = corpus.aliases();
    let head = allowlist_entries(head, Some(&aliases))?;
    let needed = allowlist_entries(&report.allowlist(), None)?;
    let stale = head.difference(&needed).cloned().collect();
    let shown = std::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["show", &format!("{base}:{ALLOWLIST}")])
        .output()
        .map_err(|error| format!("git show: {error}"))?;
    if !shown.status.success() {
        return Ok(Ratchet {
            stale,
            added: Vec::new(),
            compared: false,
        });
    }
    let base_data: Value = serde_json::from_slice(&shown.stdout)
        .map_err(|error| format!("{ALLOWLIST} at {base}: {error}"))?;
    let base_entries = allowlist_entries(&base_data, Some(&aliases))?;
    Ok(Ratchet {
        stale,
        added: head.difference(&base_entries).cloned().collect(),
        compared: true,
    })
}

/// The head allowlist as `truth check` validates it (Python
/// `load_sense_allowlist`): `{}`-shaped empty lists when the file is absent.
pub fn read_allowlist(root: &Path) -> Result<Value, String> {
    crate::check::load_sense_allowlist(root)?;
    match std::fs::read_to_string(root.join(ALLOWLIST)) {
        Ok(text) => serde_json::from_str(&text).map_err(|error| format!("{ALLOWLIST}: {error}")),
        Err(_) => Ok(json!({"arguments": {}, "senses_without_lean_declaration": []})),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allowlist_entries_flatten_arguments_and_senses() {
        let data = json!({"arguments": {"A": {"PRIOR": ["s1", "s2"]}},
                          "senses_without_lean_declaration": ["s3"]});
        let entries = allowlist_entries(&data, None).unwrap();
        let expected: BTreeSet<AllowlistEntry> = [
            vec!["A".into(), "PRIOR".into(), "s1".into()],
            vec!["A".into(), "PRIOR".into(), "s2".into()],
            vec!["s3".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(entries, expected);
        assert!(allowlist_entries(&json!({}), None).unwrap().is_empty());
    }

    #[test]
    fn bridges_connect_every_used_sense() {
        let used: BTreeSet<String> = ["a", "b", "c"].map(String::from).into();
        let edge = |from: &str, to: &str| json!({"term": "T", "from": from, "to": to});
        assert!(!bridged("T", &used, &[edge("a", "b")]));
        assert!(bridged("T", &used, &[edge("a", "b"), edge("c", "b")]));
        assert!(!bridged("U", &used, &[edge("a", "b"), edge("c", "b")]));
    }
}
