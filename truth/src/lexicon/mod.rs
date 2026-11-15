//! The lexicon (#1652): every word of corpus prose traced to an entry of
//! `corpus/lexicon/`, and every use of a multi-sense technical word in a
//! record that links one of its senses.
//!
//! An entry classifies one lemma as `technical` (definition and
//! disambiguation records), `ordinary` (an authored gloss), `function` (the
//! reviewed closed-class list) or `name`. A gloss explains how the corpus uses
//! a word; it is not evidence, and lexicon status never affects proof or
//! frontier closure. The legacy backlog lives in the shrink-only allowlist
//! `corpus/lexicon-allowlist.json`; a new or changed prose field must be fully
//! traced. See `docs/lexicon.md`.

pub mod bootstrap;
pub mod tokenize;

use crate::{Corpus, identity};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::Path,
};
use tokenize::{Token, candidates, key};

pub const DIRECTORY: &str = "corpus/lexicon";
pub const ALLOWLIST: &str = "corpus/lexicon-allowlist.json";

/// The prose fields the check scans, per record kind (#1652).
pub const SCANNED: &[(&str, &[&str])] = &[
    ("statements", &["paraphrase"]),
    ("claims", &["interpretation", "attribution"]),
    ("inferences", &["meaning"]),
    ("arguments", &["meaning"]),
    ("results", &["description"]),
    ("definitions", &["definition", "note"]),
    ("disambiguations", &["resolution"]),
    ("attempts", &["summary", "blocker"]),
];

/// Kinds whose records can link senses (`definition_ids`,
/// `disambiguation_ids`), so the multi-sense rule applies to their prose.
/// Attempts have no such links and are only checked for untraced words.
const LINKING_KINDS: &[&str] = &[
    "statements",
    "claims",
    "inferences",
    "arguments",
    "results",
    "definitions",
    "disambiguations",
];

pub const CLASSES: &[&str] = &["technical", "ordinary", "function", "name"];
pub const CATEGORIES: &[&str] = &[
    "article",
    "determiner",
    "quantifier",
    "pronoun",
    "preposition",
    "conjunction",
    "auxiliary",
    "particle",
    "numeral",
];
const FIELDS: &[&str] = &[
    "id",
    "label",
    "lemma",
    "class",
    "forms",
    "category",
    "definition_ids",
    "disambiguation_ids",
    "gloss",
    "technical_separation",
    "source_ids",
    "note",
];

type Obj = Map<String, Value>;

/// One lexicon entry.
#[derive(Clone, Debug)]
pub struct Entry {
    pub id: String,
    pub label: String,
    pub lemma: String,
    pub class: String,
    pub forms: Vec<String>,
    pub definition_ids: Vec<String>,
    pub disambiguation_ids: Vec<String>,
    pub path: String,
    pub fields: Obj,
    /// The definitions and disambiguations whose link counts as linking one
    /// of this word's senses: its definitions, its disambiguations and their
    /// sense definitions.
    pub senses: HashSet<String>,
}

impl Entry {
    /// A technical entry with more than one sense: several definitions or a
    /// disambiguation.
    pub fn multi_sense(&self) -> bool {
        self.class == "technical"
            && (self.definition_ids.len() > 1 || !self.disambiguation_ids.is_empty())
    }
}

/// The disambiguations and sense tags of the corpus.
pub struct Senses {
    /// Disambiguation id -> its sense definition ids.
    pub definitions: HashMap<String, Vec<String>>,
    /// Sense label (`PRIOR_1`) or term label (`PRIOR`) -> disambiguation ids.
    pub tags: HashMap<String, Vec<String>>,
}

impl Senses {
    pub fn new(corpus: &Corpus) -> Self {
        let mut definitions = HashMap::new();
        let mut tags: HashMap<String, Vec<String>> = HashMap::new();
        for record in corpus.records("disambiguations") {
            let id = text(record, "id").to_owned();
            definitions.insert(id.clone(), strings(record, "sense_definition_ids"));
            let mut labels: Vec<String> = record
                .get("senses")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|sense| sense.get("label").and_then(Value::as_str))
                .map(str::to_owned)
                .collect();
            if let Some(term) = record.get("term_label").and_then(Value::as_str) {
                labels.push(term.to_owned());
            }
            for label in labels {
                let ids = tags.entry(label).or_default();
                if !ids.contains(&id) {
                    ids.push(id.clone());
                }
            }
        }
        Self { definitions, tags }
    }
}

/// The loaded lexicon with its lookup indexes.
pub struct Lexicon {
    pub entries: Vec<Entry>,
    /// Lowercase single word (lemma or explicit form) -> entries.
    words: HashMap<String, Vec<usize>>,
    /// First word of a multi-word lemma -> (its words, entry), longest first.
    phrases: HashMap<String, Vec<(Vec<String>, usize)>>,
    /// Problems that are reported but do not fail the check.
    pub warnings: Vec<String>,
}

fn text<'a>(record: &'a Obj, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn strings(record: &Obj, field: &str) -> Vec<String> {
    record
        .get(field)
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect()
}

fn string_list(record: &Obj, field: &str, path: &str) -> Result<Vec<String>, String> {
    let Some(value) = record.get(field) else {
        return Ok(Vec::new());
    };
    let items = value
        .as_array()
        .filter(|items| {
            items
                .iter()
                .all(|item| item.as_str().is_some_and(|s| !s.is_empty()))
        })
        .ok_or_else(|| format!("{path}: {field} must be a list of non-empty strings"))?;
    let items: Vec<String> = items
        .iter()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect();
    if items.iter().collect::<HashSet<_>>().len() != items.len() {
        return Err(format!("{path}: {field} must not repeat an item"));
    }
    Ok(items)
}

fn nonempty(record: &Obj, field: &str, path: &str) -> Result<String, String> {
    record
        .get(field)
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
        .ok_or_else(|| format!("{path}: {field} must be a non-empty string"))
}

fn is_uuid4(text: &str) -> bool {
    let bytes = text.as_bytes();
    bytes.len() == 36
        && bytes.iter().enumerate().all(|(i, &b)| match i {
            8 | 13 | 18 | 23 => b == b'-',
            14 => b == b'4',
            19 => matches!(b, b'8' | b'9' | b'a' | b'b'),
            _ => b.is_ascii_digit() || (b'a'..=b'f').contains(&b),
        })
}

/// The lowercase words of a lemma.
pub fn lemma_words(lemma: &str) -> Vec<String> {
    key(lemma).split_whitespace().map(str::to_owned).collect()
}

impl Lexicon {
    /// Reads and validates `corpus/lexicon/`; `None` when the directory does
    /// not exist (the check is then off).
    pub fn load(root: &Path, corpus: &Corpus, senses: &Senses) -> Result<Option<Self>, String> {
        let directory = root.join(DIRECTORY);
        let listing = match fs::read_dir(&directory) {
            Ok(listing) => listing,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(format!("{DIRECTORY}: {error}")),
        };
        let mut paths: Vec<_> = listing
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
            .collect();
        paths.sort();
        let mut records = Vec::new();
        for path in paths {
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_default()
                .to_owned();
            let shown = format!("{DIRECTORY}/{name}");
            let bytes = fs::read(&path).map_err(|error| format!("{shown}: {error}"))?;
            let fields: Obj = serde_json::from_slice(&bytes)
                .map_err(|error| format!("{shown}: invalid JSON object: {error}"))?;
            records.push((shown, name, fields));
        }
        Self::from_records(records, corpus, senses).map(Some)
    }

    /// Validates entries given as (shown path, file name, fields).
    pub fn from_records(
        records: Vec<(String, String, Obj)>,
        corpus: &Corpus,
        senses: &Senses,
    ) -> Result<Self, String> {
        let definitions: HashSet<&str> = corpus
            .records("definitions")
            .into_iter()
            .map(|record| text(record, "id"))
            .collect();
        let sources: HashSet<&str> = corpus
            .records("sources")
            .into_iter()
            .map(|record| text(record, "id"))
            .collect();
        let mut entries: Vec<Entry> = Vec::new();
        let mut labels: HashMap<String, String> = HashMap::new();
        let mut ids: HashSet<String> = HashSet::new();
        let mut lemmas: HashMap<(String, String), String> = HashMap::new();
        for (path, name, fields) in records {
            if let Some(field) = fields
                .keys()
                .find(|field| !FIELDS.contains(&field.as_str()))
            {
                return Err(format!("{path}: unknown lexicon field {field}"));
            }
            let id = nonempty(&fields, "id", &path)?;
            if !is_uuid4(&id) {
                return Err(format!(
                    "{path}: id must be a lowercase uuid4 (python3 scripts/new_id.py)"
                ));
            }
            if name != format!("{id}.json") {
                return Err(format!("{path}: file name must be <id>.json"));
            }
            if !ids.insert(id.clone()) {
                return Err(format!("{path}: duplicate lexicon id {id}"));
            }
            let label = nonempty(&fields, "label", &path)?;
            if label.chars().count() > 100 {
                return Err(format!("{path}: label must be at most 100 characters"));
            }
            if let Some(idlike) = identity::idlike_text(&label).first() {
                return Err(format!("{path}: label contains id-like text {idlike}"));
            }
            if let Some(first) = labels.insert(label.clone(), path.clone()) {
                return Err(format!("{path}: label {label:?} is also used by {first}"));
            }
            let class = nonempty(&fields, "class", &path)?;
            if !CLASSES.contains(&class.as_str()) {
                return Err(format!(
                    "{path}: class must be one of {}",
                    CLASSES.join(", ")
                ));
            }
            let lemma = nonempty(&fields, "lemma", &path)?;
            let normal = lemma_words(&lemma).join(" ");
            if lemma != normal
                && (class != "name"
                    || lemma.split_whitespace().collect::<Vec<_>>().join(" ") != lemma)
            {
                return Err(format!(
                    "{path}: lemma must be lowercase words separated by single spaces (a name keeps its case)"
                ));
            }
            if let Some(first) = lemmas.insert((class.clone(), normal.clone()), path.clone()) {
                return Err(format!(
                    "{path}: {class} lemma {lemma:?} is also an entry in {first}"
                ));
            }
            let forms = string_list(&fields, "forms", &path)?;
            for form in &forms {
                if *form != key(form) || form.split_whitespace().count() != 1 || *form == normal {
                    return Err(format!(
                        "{path}: form {form:?} must be one lowercase word other than the lemma"
                    ));
                }
            }
            let definition_ids = string_list(&fields, "definition_ids", &path)?;
            let disambiguation_ids = string_list(&fields, "disambiguation_ids", &path)?;
            let allowed: &[&str] = match class.as_str() {
                "technical" => &["definition_ids", "disambiguation_ids"],
                "ordinary" => &["gloss", "technical_separation"],
                "function" => &["category", "technical_separation"],
                _ => &["gloss", "source_ids"],
            };
            for field in [
                "category",
                "definition_ids",
                "disambiguation_ids",
                "gloss",
                "technical_separation",
                "source_ids",
            ] {
                if fields.contains_key(field) && !allowed.contains(&field) {
                    return Err(format!("{path}: a {class} entry has no {field}"));
                }
            }
            let mut sense_set: HashSet<String> = HashSet::new();
            match class.as_str() {
                "technical" => {
                    if definition_ids.is_empty() {
                        return Err(format!("{path}: a technical entry needs definition_ids"));
                    }
                    for id in &definition_ids {
                        if !definitions.contains(id.as_str()) {
                            return Err(format!("{path}: unknown definition id {id}"));
                        }
                    }
                    for id in &disambiguation_ids {
                        let Some(sense_ids) = senses.definitions.get(id) else {
                            return Err(format!("{path}: unknown disambiguation id {id}"));
                        };
                        if !sense_ids.iter().any(|sense| definition_ids.contains(sense)) {
                            return Err(format!(
                                "{path}: disambiguation {id} has none of the entry's definition_ids as a sense"
                            ));
                        }
                        sense_set.extend(sense_ids.iter().cloned());
                    }
                    sense_set.extend(definition_ids.iter().cloned());
                    sense_set.extend(disambiguation_ids.iter().cloned());
                }
                "ordinary" => {
                    nonempty(&fields, "gloss", &path)?;
                }
                "function" => {
                    let category = nonempty(&fields, "category", &path)?;
                    if !CATEGORIES.contains(&category.as_str()) {
                        return Err(format!(
                            "{path}: category must be one of {}",
                            CATEGORIES.join(", ")
                        ));
                    }
                }
                _ => {
                    nonempty(&fields, "gloss", &path)?;
                    for id in string_list(&fields, "source_ids", &path)? {
                        if !sources.contains(id.as_str()) {
                            return Err(format!("{path}: unknown source id {id}"));
                        }
                    }
                }
            }
            if fields.contains_key("technical_separation") {
                nonempty(&fields, "technical_separation", &path)?;
            }
            if fields.contains_key("note") {
                nonempty(&fields, "note", &path)?;
            }
            entries.push(Entry {
                id,
                label,
                lemma: normal,
                class,
                forms,
                definition_ids,
                disambiguation_ids,
                path,
                fields,
                senses: sense_set,
            });
        }
        // An ordinary or function entry for a word that also has a technical
        // entry records how its use differs (`technical_separation`).
        let technical: HashSet<&str> = entries
            .iter()
            .filter(|entry| entry.class == "technical")
            .map(|entry| entry.lemma.as_str())
            .collect();
        for entry in &entries {
            if !matches!(entry.class.as_str(), "ordinary" | "function") {
                continue;
            }
            let has = entry.fields.contains_key("technical_separation");
            let needs = technical.contains(entry.lemma.as_str());
            if needs && !has {
                return Err(format!(
                    "{}: '{}' also has a technical entry; state technical_separation",
                    entry.path, entry.lemma
                ));
            }
            if has && !needs {
                return Err(format!(
                    "{}: technical_separation given but '{}' has no technical entry",
                    entry.path, entry.lemma
                ));
            }
        }
        let mut warnings = Vec::new();
        for entry in entries.iter().filter(|entry| entry.class == "technical") {
            let covered: HashSet<&String> = entry
                .disambiguation_ids
                .iter()
                .flat_map(|id| senses.definitions[id].iter())
                .collect();
            let uncovered = entry
                .definition_ids
                .iter()
                .filter(|id| !covered.contains(id))
                .count();
            if entry.definition_ids.len() > 1 && uncovered > 0 {
                warnings.push(format!(
                    "technical entry '{}' has {uncovered} of {} definitions that no listed disambiguation covers",
                    entry.lemma,
                    entry.definition_ids.len()
                ));
            }
        }
        let mut words: HashMap<String, Vec<usize>> = HashMap::new();
        let mut phrases: HashMap<String, Vec<(Vec<String>, usize)>> = HashMap::new();
        for (index, entry) in entries.iter().enumerate() {
            let lemma = lemma_words(&entry.lemma);
            let single = (lemma.len() == 1).then(|| &lemma[0]);
            if lemma.len() > 1 {
                phrases
                    .entry(lemma[0].clone())
                    .or_default()
                    .push((lemma.clone(), index));
            }
            // Explicit forms are single words, also for a multi-word lemma
            // (`per-se` for `per se`).
            for word in single.into_iter().chain(entry.forms.iter()) {
                let list = words.entry(word.clone()).or_default();
                if !list.contains(&index) {
                    list.push(index);
                }
            }
        }
        for list in phrases.values_mut() {
            list.sort_by(|a, b| b.0.len().cmp(&a.0.len()).then_with(|| a.0.cmp(&b.0)));
        }
        Ok(Self {
            entries,
            words,
            phrases,
            warnings,
        })
    }

    /// The entries a single lowercase word resolves to: an exact lemma or
    /// explicit form first, then the first lemmatizer candidate the lexicon
    /// has. Returns the matched lemma key.
    pub fn resolve_word(&self, word: &str) -> Option<(String, Vec<usize>)> {
        if let Some(found) = self.words.get(word) {
            return Some((word.to_owned(), found.clone()));
        }
        candidates(word).into_iter().find_map(|candidate| {
            self.words
                .get(&candidate)
                .map(|found| (candidate, found.clone()))
        })
    }

    /// A word, or a hyphenated compound all of whose parts resolve.
    /// Returns (token, entries) per traced word: the word itself, or each
    /// part of a hyphenated compound, so that each part's readings are
    /// checked on their own.
    fn resolve_token(&self, word: &str) -> Option<Vec<(String, Vec<usize>)>> {
        if let Some((_, found)) = self.resolve_word(word) {
            return Some(vec![(word.to_owned(), found)]);
        }
        if !word.contains('-') {
            return None;
        }
        let mut parts = Vec::new();
        for part in word.split('-').filter(|part| !part.is_empty()) {
            parts.push((part.to_owned(), self.resolve_word(part)?.1));
        }
        (!parts.is_empty()).then_some(parts)
    }

    /// The longest multi-word lemma starting at `words[i]`, as (length, entry).
    fn phrase_at(&self, words: &[(String, bool)], i: usize) -> Option<(usize, usize)> {
        let list = self.phrases.get(&words[i].0)?;
        list.iter().find_map(|(phrase, index)| {
            let n = phrase.len();
            if i + n > words.len() || !(1..n).all(|k| words[i + k].1) {
                return None;
            }
            let inner = (1..n - 1).all(|k| words[i + k].0 == phrase[k]);
            let last = &words[i + n - 1].0;
            let tail = *last == phrase[n - 1] || candidates(last).contains(&phrase[n - 1]);
            (inner && tail).then_some((n, *index))
        })
    }
}

/// How one token was traced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Trace {
    /// Lexicon entries (indexes into [`Lexicon::entries`]).
    Entries(Vec<usize>),
    /// A sense or term tag, traced to these disambiguations.
    Tag(Vec<String>),
    /// No entry.
    Untraced,
}

/// One scanned prose field.
#[derive(Debug)]
pub struct FieldScan {
    pub kind: &'static str,
    pub id: String,
    pub path: String,
    pub field: &'static str,
    pub hash: String,
    /// (lowercase token, trace) in order.
    pub occurrences: Vec<(String, Trace)>,
    /// Untraced tokens (lowercase; a tag as written).
    pub untraced: BTreeSet<String>,
    /// Lemmas of multi-sense technical words whose senses the record links
    /// none of.
    pub unlinked: BTreeSet<String>,
}

impl FieldScan {
    pub fn key(&self) -> String {
        format!("{}/{}/{}", self.kind, self.id, self.field)
    }
}

/// `fnv1a64:` hash of a field's text: the allowlist's change detector.
pub fn hash(text: &str) -> String {
    let mut value: u64 = 0xcbf29ce484222325;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

/// Traces one text: every token's entries, tag or failure.
pub fn trace_text(lexicon: &Lexicon, senses: &Senses, text: &str) -> Vec<(String, Trace)> {
    let tokens = tokenize::tokenize(text);
    let mut out = Vec::new();
    let mut words: Vec<(String, bool)> = Vec::new();
    let flush = |words: &mut Vec<(String, bool)>, out: &mut Vec<(String, Trace)>| {
        let mut i = 0;
        while i < words.len() {
            if let Some((n, index)) = lexicon.phrase_at(words, i) {
                for (word, _) in &words[i..i + n] {
                    out.push((word.clone(), Trace::Entries(vec![index])));
                }
                i += n;
                continue;
            }
            let word = &words[i].0;
            match lexicon.resolve_token(word) {
                Some(parts) => {
                    for (part, found) in parts {
                        out.push((part, Trace::Entries(found)));
                    }
                }
                None => out.push((word.clone(), Trace::Untraced)),
            }
            i += 1;
        }
        words.clear();
    };
    for token in tokens {
        match token {
            Token::Word { text, joined } => {
                if !joined {
                    flush(&mut words, &mut out);
                }
                words.push((key(&text), joined));
            }
            Token::Tag(tag) => {
                flush(&mut words, &mut out);
                let trace = match senses.tags.get(&tag) {
                    Some(ids) => Trace::Tag(ids.clone()),
                    None => Trace::Untraced,
                };
                out.push((tag, trace));
            }
        }
    }
    flush(&mut words, &mut out);
    out
}

/// The definitions and disambiguations a record links, for the multi-sense
/// rule: its own `definition_ids`/`disambiguation_ids`, the links of the
/// statement a claim reads or the argument a result verifies, a definition
/// or disambiguation itself, and the disambiguations of sense tags in its
/// label.
fn record_links(corpus: &Corpus, senses: &Senses, kind: &str, record: &Obj) -> HashSet<String> {
    let mut links: HashSet<String> = HashSet::new();
    let mut add = |record: &Obj| {
        links.extend(strings(record, "definition_ids"));
        links.extend(strings(record, "disambiguation_ids"));
    };
    add(record);
    let parent = match kind {
        "claims" => Some(("statements", text(record, "statement_id"))),
        "results" => Some(("arguments", text(record, "argument_id"))),
        _ => None,
    };
    if let Some((parent_kind, id)) = parent
        && let Some(parent) = corpus.get(parent_kind, id)
    {
        add(&parent.fields);
    }
    let id = text(record, "id").to_owned();
    match kind {
        "definitions" => {
            links.insert(id);
        }
        "disambiguations" => {
            links.extend(strings(record, "sense_definition_ids"));
            links.insert(id);
        }
        _ => {}
    }
    for token in tokenize::tokenize(text(record, "label")) {
        if let Token::Tag(tag) = token
            && let Some(ids) = senses.tags.get(&tag)
        {
            links.extend(ids.iter().cloned());
        }
    }
    links
}

/// Scans every prose field of [`SCANNED`].
pub fn scan(corpus: &Corpus, senses: &Senses, lexicon: &Lexicon) -> Vec<FieldScan> {
    let mut scans = Vec::new();
    for (kind, fields) in SCANNED {
        for record in corpus.entries(kind) {
            let mut links: Option<HashSet<String>> = None;
            for field in *fields {
                let Some(prose) = record.fields.get(*field).and_then(Value::as_str) else {
                    continue;
                };
                let occurrences = trace_text(lexicon, senses, prose);
                let mut untraced = BTreeSet::new();
                let mut unlinked = BTreeSet::new();
                for (word, trace) in &occurrences {
                    match trace {
                        Trace::Untraced => {
                            untraced.insert(word.clone());
                        }
                        Trace::Entries(found) if LINKING_KINDS.contains(kind) => {
                            let all_technical = found
                                .iter()
                                .all(|&i| lexicon.entries[i].class == "technical");
                            if !all_technical {
                                continue;
                            }
                            for &i in found {
                                let entry = &lexicon.entries[i];
                                if !entry.multi_sense() {
                                    continue;
                                }
                                let links = links.get_or_insert_with(|| {
                                    let mut links =
                                        record_links(corpus, senses, kind, &record.fields);
                                    for field in *fields {
                                        let prose = text(&record.fields, field);
                                        for token in tokenize::tokenize(prose) {
                                            if let Token::Tag(tag) = token
                                                && let Some(ids) = senses.tags.get(&tag)
                                            {
                                                links.extend(ids.iter().cloned());
                                            }
                                        }
                                    }
                                    links
                                });
                                if entry.senses.is_disjoint(links) {
                                    unlinked.insert(entry.lemma.clone());
                                }
                            }
                        }
                        _ => {}
                    }
                }
                scans.push(FieldScan {
                    kind,
                    id: text(&record.fields, "id").to_owned(),
                    path: record.path.clone(),
                    field,
                    hash: hash(prose),
                    occurrences,
                    untraced,
                    unlinked,
                });
            }
        }
    }
    scans
}

// ---------------------------------------------------------------------------
// The shrink-only allowlist.

/// One allowlisted legacy prose field: its text hash and the untraced words
/// and unlinked multi-sense lemmas it may keep while unchanged.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Allowed {
    pub hash: String,
    pub untraced: BTreeSet<String>,
    pub unlinked: BTreeSet<String>,
}

pub type Allowlist = BTreeMap<String, Allowed>;

pub fn parse_allowlist(source: &str) -> Result<Allowlist, String> {
    let value: Value = serde_json::from_str(source)
        .map_err(|error| format!("{ALLOWLIST}: invalid JSON: {error}"))?;
    let fields = value
        .get("fields")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{ALLOWLIST}: must be an object with a fields object"))?;
    let mut allowlist = Allowlist::new();
    for (key, entry) in fields {
        let entry = entry
            .as_object()
            .ok_or_else(|| format!("{ALLOWLIST}: {key} must be an object"))?;
        let words = |field: &str| -> Result<BTreeSet<String>, String> {
            Ok(string_list(entry, field, ALLOWLIST)?.into_iter().collect())
        };
        allowlist.insert(
            key.clone(),
            Allowed {
                hash: text(entry, "hash").to_owned(),
                untraced: words("untraced")?,
                unlinked: words("unlinked")?,
            },
        );
    }
    Ok(allowlist)
}

pub fn read_allowlist(root: &Path) -> Result<Option<Allowlist>, String> {
    match fs::read_to_string(root.join(ALLOWLIST)) {
        Ok(text) => parse_allowlist(&text).map(Some),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(format!("{ALLOWLIST}: {error}")),
    }
}

/// The allowlist file: one field per line, sorted, so diffs show removals.
pub fn render_allowlist(allowlist: &Allowlist) -> String {
    let mut out = String::from("{\n  \"schema_version\": 1,\n  \"fields\": {");
    let mut first = true;
    for (key, allowed) in allowlist {
        out.push_str(if first { "\n    " } else { ",\n    " });
        first = false;
        out.push_str(&format!(
            "{}: {{\"hash\": {}, \"untraced\": {}, \"unlinked\": {}}}",
            json!(key),
            json!(allowed.hash),
            json!(allowed.untraced),
            json!(allowed.unlinked)
        ));
    }
    out.push_str(if first { "}\n}\n" } else { "\n  }\n}\n" });
    out
}

/// The allowlist the current scan needs: every field with a violation. With
/// `existing`, only what it already grants (same hash, intersected words):
/// regeneration only shrinks.
pub fn needed_allowlist(scans: &[FieldScan], existing: Option<&Allowlist>) -> Allowlist {
    let mut out = Allowlist::new();
    for scan in scans {
        if scan.untraced.is_empty() && scan.unlinked.is_empty() {
            continue;
        }
        let mut allowed = Allowed {
            hash: scan.hash.clone(),
            untraced: scan.untraced.clone(),
            unlinked: scan.unlinked.clone(),
        };
        if let Some(existing) = existing {
            let Some(granted) = existing.get(&scan.key()).filter(|g| g.hash == scan.hash) else {
                continue;
            };
            allowed.untraced = &allowed.untraced & &granted.untraced;
            allowed.unlinked = &allowed.unlinked & &granted.unlinked;
            if allowed.untraced.is_empty() && allowed.unlinked.is_empty() {
                continue;
            }
        }
        out.insert(scan.key(), allowed);
    }
    out
}

/// Entries of `head` that `base` does not grant: a new key, a changed hash or
/// an added word. The allowlist may only shrink.
pub fn ratchet(base: &Allowlist, head: &Allowlist) -> Vec<String> {
    let mut grown = Vec::new();
    for (key, allowed) in head {
        let Some(before) = base.get(key) else {
            grown.push(format!("{key}: new allowlist entry"));
            continue;
        };
        if before.hash != allowed.hash {
            grown.push(format!("{key}: allowlisted again after its prose changed"));
            continue;
        }
        let words: Vec<&String> = allowed
            .untraced
            .difference(&before.untraced)
            .chain(allowed.unlinked.difference(&before.unlinked))
            .collect();
        if !words.is_empty() {
            grown.push(format!(
                "{key}: words added: {}",
                words.into_iter().cloned().collect::<Vec<_>>().join(", ")
            ));
        }
    }
    grown
}

// ---------------------------------------------------------------------------
// The check.

/// The lexicon check's result on a passing corpus.
#[derive(Debug, Default)]
pub struct Report {
    pub entries: usize,
    pub fields: usize,
    pub backlog_fields: usize,
    pub backlog_untraced: usize,
    pub backlog_unlinked: usize,
    pub removable: usize,
    pub warnings: Vec<String>,
}

impl Report {
    /// The one summary warning `truth check` prints.
    pub fn summary(&self) -> String {
        let mut text = format!(
            "lexicon: {} entries; {} untraced words and {} unlinked multi-sense words in {} of {} prose fields are allowlisted legacy backlog ({ALLOWLIST}; `truth lexicon untraced`)",
            self.entries,
            self.backlog_untraced,
            self.backlog_unlinked,
            self.backlog_fields,
            self.fields
        );
        if self.removable > 0 {
            text.push_str(&format!(
                "; {} allowlist entries can shrink (`truth lexicon allowlist --write`)",
                self.removable
            ));
        }
        if !self.warnings.is_empty() {
            text.push_str(&format!(
                "; {} technical entries have definitions no listed disambiguation covers (`truth lexicon coverage`)",
                self.warnings.len()
            ));
        }
        text
    }
}

/// Everything the commands need: the corpus, its senses, the lexicon and
/// the scan.
pub struct Loaded {
    pub corpus: Corpus,
    pub senses: Senses,
    pub lexicon: Lexicon,
    pub scans: Vec<FieldScan>,
}

pub fn load(root: &Path) -> Result<Option<Loaded>, String> {
    let corpus =
        Corpus::load(root).map_err(|error| format!("{}: {}", error.path, error.message))?;
    let senses = Senses::new(&corpus);
    let Some(lexicon) = Lexicon::load(root, &corpus, &senses)? else {
        return Ok(None);
    };
    let scans = scan(&corpus, &senses, &lexicon);
    Ok(Some(Loaded {
        corpus,
        senses,
        lexicon,
        scans,
    }))
}

/// The new violations of `scans` that `allowlist` does not grant.
pub fn violations(scans: &[FieldScan], allowlist: &Allowlist) -> Vec<String> {
    let mut errors = Vec::new();
    for scan in scans {
        if scan.untraced.is_empty() && scan.unlinked.is_empty() {
            continue;
        }
        let granted = allowlist.get(&scan.key()).filter(|g| g.hash == scan.hash);
        let empty = BTreeSet::new();
        let (untraced, unlinked) = granted
            .map(|g| (&g.untraced, &g.unlinked))
            .unwrap_or((&empty, &empty));
        let words: Vec<&String> = scan.untraced.difference(untraced).collect();
        let lemmas: Vec<&String> = scan.unlinked.difference(unlinked).collect();
        if !words.is_empty() {
            errors.push(format!(
                "{}: {}: untraced word{} {} (add lexicon entries or forms; docs/lexicon.md)",
                scan.path,
                scan.field,
                if words.len() == 1 { "" } else { "s" },
                words
                    .iter()
                    .map(|w| format!("'{w}'"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        if !lemmas.is_empty() {
            errors.push(format!(
                "{}: {}: uses multi-sense technical word{} {} but links none of {} senses (definition_ids, disambiguation_ids or a sense tag such as PRIOR_1)",
                scan.path,
                scan.field,
                if lemmas.len() == 1 { "" } else { "s" },
                lemmas.iter().map(|w| format!("'{w}'")).collect::<Vec<_>>().join(", "),
                if lemmas.len() == 1 { "its" } else { "their" }
            ));
        }
    }
    errors
}

/// The check `truth check` runs: `Ok(None)` without a lexicon directory;
/// an error listing the first new violations; otherwise the backlog report.
pub fn check(root: &Path) -> Result<Option<Report>, String> {
    let Some(loaded) = load(root)? else {
        return Ok(None);
    };
    let allowlist = read_allowlist(root)?.unwrap_or_default();
    let errors = violations(&loaded.scans, &allowlist);
    if !errors.is_empty() {
        const SHOWN: usize = 20;
        let mut message = format!(
            "lexicon: {} new or changed prose field problem{} (a new or changed prose field must be fully traced; {ALLOWLIST} may only shrink):",
            errors.len(),
            if errors.len() == 1 { "" } else { "s" }
        );
        for error in errors.iter().take(SHOWN) {
            message.push_str("\n  ");
            message.push_str(error);
        }
        if errors.len() > SHOWN {
            message.push_str(&format!(
                "\n  … and {} more (`truth lexicon untraced`)",
                errors.len() - SHOWN
            ));
        }
        return Err(message);
    }
    let needed = needed_allowlist(&loaded.scans, Some(&allowlist));
    let removable = allowlist
        .iter()
        .filter(|(key, allowed)| needed.get(*key) != Some(allowed))
        .count();
    let mut report = Report {
        entries: loaded.lexicon.entries.len(),
        fields: loaded.scans.len(),
        removable,
        warnings: loaded.lexicon.warnings.clone(),
        ..Report::default()
    };
    for allowed in needed.values() {
        report.backlog_fields += 1;
        report.backlog_untraced += allowed.untraced.len();
        report.backlog_unlinked += allowed.unlinked.len();
    }
    Ok(Some(report))
}

// ---------------------------------------------------------------------------
// Reports for the commands.

/// Token and type coverage of the scanned prose.
pub fn coverage(loaded: &Loaded, top: usize) -> Value {
    let mut tokens = 0usize;
    let mut traced = 0usize;
    let mut tags = 0usize;
    let mut by_class: BTreeMap<&str, usize> = BTreeMap::new();
    let mut types: BTreeMap<&str, bool> = BTreeMap::new();
    let mut fields_traced = 0usize;
    for scan in &loaded.scans {
        if scan.untraced.is_empty() && scan.unlinked.is_empty() {
            fields_traced += 1;
        }
        for (word, trace) in &scan.occurrences {
            tokens += 1;
            let ok = !matches!(trace, Trace::Untraced);
            traced += usize::from(ok);
            let known = types.entry(word.as_str()).or_insert(false);
            *known |= ok;
            match trace {
                Trace::Entries(found) => {
                    let class = found
                        .iter()
                        .map(|&i| loaded.lexicon.entries[i].class.as_str())
                        .min_by_key(|class| CLASSES.iter().position(|c| c == class))
                        .unwrap_or("technical");
                    *by_class.entry(class).or_default() += 1;
                }
                Trace::Tag(_) => tags += 1,
                Trace::Untraced => {}
            }
        }
    }
    let mut entries_by_class: BTreeMap<&str, usize> = BTreeMap::new();
    for entry in &loaded.lexicon.entries {
        *entries_by_class.entry(entry.class.as_str()).or_default() += 1;
    }
    let traced_types = types.values().filter(|ok| **ok).count();
    json!({
        "entries": loaded.lexicon.entries.len(),
        "entries_by_class": entries_by_class,
        "fields": loaded.scans.len(),
        "fields_fully_traced": fields_traced,
        "tokens": tokens,
        "tokens_traced": traced,
        "tokens_by_class": by_class,
        "tokens_sense_tags": tags,
        "types": types.len(),
        "types_traced": traced_types,
        "unlinked_multi_sense_uses": loaded.scans.iter().map(|s| s.unlinked.len()).sum::<usize>(),
        "top_untraced": untraced(loaded, top),
        "entry_warnings": loaded.lexicon.warnings,
    })
}

/// Untraced words by frequency: (word, occurrences, fields), most frequent
/// first.
pub fn untraced(loaded: &Loaded, limit: usize) -> Vec<Value> {
    let mut counts: HashMap<&str, (usize, usize, &FieldScan)> = HashMap::new();
    for scan in &loaded.scans {
        let mut seen: HashSet<&str> = HashSet::new();
        for (word, trace) in &scan.occurrences {
            if *trace != Trace::Untraced {
                continue;
            }
            let entry = counts.entry(word.as_str()).or_insert((0, 0, scan));
            entry.0 += 1;
            if seen.insert(word.as_str()) {
                entry.1 += 1;
            }
        }
    }
    let mut rows: Vec<_> = counts.into_iter().collect();
    rows.sort_by(|a, b| b.1.0.cmp(&a.1.0).then_with(|| a.0.cmp(b.0)));
    rows.into_iter()
        .take(limit)
        .map(|(word, (count, fields, example))| {
            json!({"word": word, "occurrences": count, "fields": fields, "example": format!("{}: {}", example.path, example.field)})
        })
        .collect()
}

/// `show WORD`: the entries the word resolves to, their senses, and the
/// prose fields that use it.
pub fn show(loaded: &Loaded, word: &str, limit: usize) -> Value {
    let lower = key(word.trim());
    let words = lemma_words(&lower);
    let mut found: Vec<usize> = Vec::new();
    let mut lemma = lower.clone();
    if words.len() > 1 {
        found = loaded
            .lexicon
            .entries
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.lemma == words.join(" "))
            .map(|(i, _)| i)
            .collect();
    } else if let Some((matched, entries)) = loaded.lexicon.resolve_word(&lower) {
        lemma = matched;
        found = entries;
    }
    let definitions = |ids: &[String]| -> Vec<Value> {
        ids.iter()
            .map(|id| {
                let record = loaded.corpus.get("definitions", id).map(|r| &r.fields);
                json!({
                    "id": id,
                    "label": record.map(|r| text(r, "label")).unwrap_or_default(),
                    "term": record.map(|r| text(r, "term")).unwrap_or_default(),
                })
            })
            .collect()
    };
    let entries: Vec<Value> = found
        .iter()
        .map(|&i| {
            let entry = &loaded.lexicon.entries[i];
            let disambiguations: Vec<Value> = entry
                .disambiguation_ids
                .iter()
                .map(|id| {
                    let record = loaded.corpus.get("disambiguations", id).map(|r| &r.fields);
                    let senses: Vec<Value> = record
                        .and_then(|r| r.get("senses"))
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                        .map(|sense| {
                            json!({
                                "label": sense.get("label"),
                                "definition_id": sense.get("definition_id"),
                            })
                        })
                        .collect();
                    json!({
                        "id": id,
                        "label": record.map(|r| text(r, "label")).unwrap_or_default(),
                        "senses": senses,
                    })
                })
                .collect();
            json!({
                "id": entry.id,
                "label": entry.label,
                "lemma": entry.lemma,
                "class": entry.class,
                "path": entry.path,
                "forms": entry.forms,
                "category": entry.fields.get("category"),
                "gloss": entry.fields.get("gloss"),
                "technical_separation": entry.fields.get("technical_separation"),
                "definitions": definitions(&entry.definition_ids),
                "disambiguations": disambiguations,
            })
        })
        .collect();
    let mut uses = Vec::new();
    let mut count = 0usize;
    for scan in &loaded.scans {
        let hit = scan.occurrences.iter().any(|(token, trace)| match trace {
            Trace::Entries(entries) if !found.is_empty() => {
                entries.iter().any(|i| found.contains(i))
            }
            _ => *token == lower,
        });
        if hit {
            count += 1;
            if uses.len() < limit {
                let label = loaded
                    .corpus
                    .get(scan.kind, &scan.id)
                    .map(|r| text(&r.fields, "label").to_owned())
                    .unwrap_or_default();
                uses.push(json!({
                    "kind": scan.kind,
                    "id": scan.id,
                    "label": label,
                    "field": scan.field,
                    "unlinked": scan.unlinked.contains(&lemma),
                }));
            }
        }
    }
    json!({
        "word": word,
        "lemma": lemma,
        "traced": !found.is_empty(),
        "entries": entries,
        "fields_using": count,
        "uses": uses,
    })
}

#[cfg(test)]
mod tests;
