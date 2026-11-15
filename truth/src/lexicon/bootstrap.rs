//! `truth lexicon bootstrap`: the generated part of the lexicon (#1652 L1).
//!
//! It writes one `function` entry per line of the reviewed closed-class list
//! (`function_words.txt`) and one `technical` entry per short definition
//! term: definitions grouped by normalized lemma, with the disambiguations
//! that name that term or whose senses all fall in the group. It never
//! invents an ordinary gloss, never deletes an entry, keeps existing ids and
//! hand-added fields, and only adds definition and disambiguation links to
//! an existing technical entry. Rerunning it is idempotent.

use super::{Obj, Senses, lemma_words, strings, text};
use crate::Corpus;
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    io::Read,
    path::Path,
};

pub const FUNCTION_WORDS: &str = include_str!("function_words.txt");

/// The longest definition term, in words, that becomes a technical entry.
/// Longer terms are descriptive titles ("reception of a perfection"), not
/// words of prose.
pub const MAX_TERM_WORDS: usize = 3;

/// One function word of the reviewed list.
#[derive(Debug, PartialEq, Eq)]
pub struct FunctionWord {
    pub lemma: String,
    pub category: String,
    pub forms: Vec<String>,
    pub separation: Option<String>,
}

/// Parses `function_words.txt`.
pub fn function_words(text: &str) -> Result<Vec<FunctionWord>, String> {
    let mut words: Vec<FunctionWord> = Vec::new();
    let mut separations: HashMap<String, String> = HashMap::new();
    let mut category: Option<String> = None;
    for (number, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            if name != "separation" && !super::CATEGORIES.contains(&name) {
                return Err(format!(
                    "function_words.txt:{}: unknown category {name}",
                    number + 1
                ));
            }
            category = Some(name.to_owned());
            continue;
        }
        let Some(current) = category.as_deref() else {
            return Err(format!(
                "function_words.txt:{}: word before a [category]",
                number + 1
            ));
        };
        let (lemma, rest) = line.split_once(':').unwrap_or((line, ""));
        let lemma = lemma.trim().to_owned();
        if current == "separation" {
            separations.insert(lemma, rest.trim().to_owned());
            continue;
        }
        if words.iter().any(|word| word.lemma == lemma) {
            return Err(format!(
                "function_words.txt:{}: {lemma} is listed twice",
                number + 1
            ));
        }
        words.push(FunctionWord {
            lemma,
            category: current.to_owned(),
            forms: rest.split_whitespace().map(str::to_owned).collect(),
            separation: None,
        });
    }
    for (lemma, separation) in separations {
        let word = words
            .iter_mut()
            .find(|word| word.lemma == lemma)
            .ok_or_else(|| format!("function_words.txt: separation for unlisted word {lemma}"))?;
        word.separation = Some(separation);
    }
    Ok(words)
}

/// A definition or disambiguation term as a lexicon lemma, or `None` when it
/// is not a short phrase of words: parentheticals dropped, lowercase, at most
/// [`MAX_TERM_WORDS`] words of letters (with inner `-` or `'`), each at least
/// two letters long.
pub fn term_lemma(term: &str) -> Option<String> {
    let mut text = term.replace('\u{2019}', "'");
    while let Some(open) = text.rfind('(') {
        let close = text[open..].find(')')? + open;
        text.replace_range(open..=close, " ");
    }
    let words = lemma_words(&text);
    let words: Vec<String> = words
        .into_iter()
        .map(|word| word.trim_matches(|c: char| ".,;:".contains(c)).to_owned())
        .filter(|word| !word.is_empty())
        .collect();
    let ok = !words.is_empty()
        && words.len() <= MAX_TERM_WORDS
        && words.iter().all(|word| {
            word.chars().count() >= 2
                && word.chars().next().is_some_and(char::is_alphabetic)
                && word.chars().last().is_some_and(char::is_alphabetic)
                && word
                    .chars()
                    .all(|c| c.is_alphabetic() || c == '-' || c == '\'')
        });
    ok.then(|| words.join(" "))
}

/// Definitions and disambiguations per technical lemma.
pub fn technical_groups(
    corpus: &Corpus,
    senses: &Senses,
) -> BTreeMap<String, (BTreeSet<String>, BTreeSet<String>)> {
    let mut groups: BTreeMap<String, (BTreeSet<String>, BTreeSet<String>)> = BTreeMap::new();
    for record in corpus.records("definitions") {
        if let Some(lemma) = record
            .get("term")
            .and_then(Value::as_str)
            .and_then(term_lemma)
        {
            groups
                .entry(lemma)
                .or_default()
                .0
                .insert(text(record, "id").to_owned());
        }
    }
    for record in corpus.records("disambiguations") {
        let term = match record.get("term").and_then(Value::as_str) {
            Some(term) => term.to_owned(),
            None => text(record, "term_label").replace('_', " "),
        };
        if let Some(lemma) = term_lemma(&term) {
            let group = groups.entry(lemma).or_default();
            group.1.insert(text(record, "id").to_owned());
            group.0.extend(strings(record, "sense_definition_ids"));
        }
    }
    // A disambiguation whose senses all belong to one lemma's group also
    // disambiguates that lemma.
    for (id, sense_ids) in &senses.definitions {
        if sense_ids.len() < 2 {
            continue;
        }
        for group in groups.values_mut() {
            if sense_ids.iter().all(|sense| group.0.contains(sense)) {
                group.1.insert(id.clone());
            }
        }
    }
    groups
}

/// A new lowercase uuid4 from the system's random source.
pub fn uuid4() -> Result<String, String> {
    let mut bytes = [0u8; 16];
    fs::File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot read /dev/urandom for a new id: {error}"))?;
    bytes[6] = (bytes[6] & 0x0f) | 0x40;
    bytes[8] = (bytes[8] & 0x3f) | 0x80;
    let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    Ok(format!(
        "{}-{}-{}-{}-{}",
        &hex[0..8],
        &hex[8..12],
        &hex[12..16],
        &hex[16..20],
        &hex[20..32]
    ))
}

const ORDER: &[&str] = &[
    "id",
    "label",
    "lemma",
    "class",
    "category",
    "forms",
    "definition_ids",
    "disambiguation_ids",
    "gloss",
    "technical_separation",
    "source_ids",
    "note",
];

/// A lexicon record as written: fields in [`ORDER`], two-space indent.
pub fn render(fields: &Obj) -> String {
    let mut out = String::from("{");
    let mut first = true;
    for field in ORDER.iter().copied().chain(
        fields
            .keys()
            .map(String::as_str)
            .filter(|f| !ORDER.contains(f)),
    ) {
        let Some(value) = fields.get(field) else {
            continue;
        };
        out.push_str(if first { "\n  " } else { ",\n  " });
        first = false;
        let rendered = serde_json::to_string_pretty(value)
            .unwrap_or_default()
            .replace('\n', "\n  ");
        out.push_str(&format!("{}: {rendered}", json!(field)));
    }
    out.push_str("\n}\n");
    out
}

/// The bootstrap's result: files to write and counts.
#[derive(Debug, Default)]
pub struct Plan {
    pub writes: Vec<(String, String)>,
    pub created: BTreeMap<String, usize>,
    pub updated: usize,
    pub unchanged: usize,
}

fn read_existing(root: &Path) -> Result<Vec<(String, Obj)>, String> {
    let directory = root.join(super::DIRECTORY);
    let Ok(listing) = fs::read_dir(&directory) else {
        return Ok(Vec::new());
    };
    let mut paths: Vec<_> = listing.filter_map(Result::ok).map(|e| e.path()).collect();
    paths.sort();
    let mut out = Vec::new();
    for path in paths
        .into_iter()
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
    {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default();
        let relative = format!("{}/{name}", super::DIRECTORY);
        let bytes = fs::read(&path).map_err(|error| format!("{relative}: {error}"))?;
        let fields: Obj =
            serde_json::from_slice(&bytes).map_err(|error| format!("{relative}: {error}"))?;
        out.push((relative, fields));
    }
    Ok(out)
}

/// Computes the bootstrap writes against the current lexicon.
pub fn plan(root: &Path, corpus: &Corpus, senses: &Senses) -> Result<Plan, String> {
    let existing = read_existing(root)?;
    let mut by_lemma: HashMap<(String, String), (String, Obj)> = HashMap::new();
    for (path, fields) in existing {
        let lemma = lemma_words(text(&fields, "lemma")).join(" ");
        by_lemma.insert((text(&fields, "class").to_owned(), lemma), (path, fields));
    }
    let groups = technical_groups(corpus, senses);
    let words = function_words(FUNCTION_WORDS)?;
    let mut plan = Plan::default();
    let mut desired: Vec<(String, String, Obj)> = Vec::new();
    for (lemma, (definitions, disambiguations)) in &groups {
        let mut fields = Obj::new();
        fields.insert("lemma".into(), json!(lemma));
        fields.insert("class".into(), json!("technical"));
        fields.insert("label".into(), json!(format!("{lemma} (technical)")));
        fields.insert("definition_ids".into(), json!(definitions));
        if !disambiguations.is_empty() {
            fields.insert("disambiguation_ids".into(), json!(disambiguations));
        }
        desired.push(("technical".into(), lemma.clone(), fields));
    }
    for word in &words {
        let mut fields = Obj::new();
        fields.insert("lemma".into(), json!(word.lemma));
        fields.insert("class".into(), json!("function"));
        fields.insert(
            "label".into(),
            json!(format!("{} (function word)", word.lemma)),
        );
        fields.insert("category".into(), json!(word.category));
        if !word.forms.is_empty() {
            fields.insert("forms".into(), json!(word.forms));
        }
        let technical = groups.contains_key(&word.lemma)
            || by_lemma.contains_key(&("technical".to_owned(), word.lemma.clone()));
        match (&word.separation, technical) {
            (Some(separation), true) => {
                fields.insert("technical_separation".into(), json!(separation));
            }
            (None, true) => {
                return Err(format!(
                    "function word '{}' also has a technical entry; add a [separation] line to truth/src/lexicon/function_words.txt",
                    word.lemma
                ));
            }
            _ => {}
        }
        desired.push(("function".into(), word.lemma.clone(), fields));
    }
    for (class, lemma, fields) in desired {
        match by_lemma.get(&(class.clone(), lemma.clone())) {
            Some((path, current)) => {
                let mut merged = current.clone();
                for (field, value) in &fields {
                    let union = matches!(field.as_str(), "definition_ids" | "disambiguation_ids");
                    if union {
                        let mut set: BTreeSet<String> =
                            strings(current, field).into_iter().collect();
                        set.extend(
                            value
                                .as_array()
                                .into_iter()
                                .flatten()
                                .filter_map(Value::as_str)
                                .map(str::to_owned),
                        );
                        merged.insert(field.clone(), json!(set));
                    } else if class == "function" || !current.contains_key(field) {
                        merged.insert(field.clone(), value.clone());
                    }
                }
                if merged == *current {
                    plan.unchanged += 1;
                } else {
                    plan.updated += 1;
                    plan.writes.push((path.clone(), render(&merged)));
                }
            }
            None => {
                let id = uuid4()?;
                let mut record = fields;
                record.insert("id".into(), json!(id));
                *plan.created.entry(class).or_default() += 1;
                plan.writes
                    .push((format!("{}/{id}.json", super::DIRECTORY), render(&record)));
            }
        }
    }
    Ok(plan)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_lemmas() {
        assert_eq!(term_lemma("being (univocal)").as_deref(), Some("being"));
        assert_eq!(term_lemma("Ground (Dasgupta)").as_deref(), Some("ground"));
        assert_eq!(term_lemma("per se").as_deref(), Some("per se"));
        assert_eq!(
            term_lemma("Gibbard’s plans").as_deref(),
            Some("gibbard's plans")
        );
        assert_eq!(term_lemma("is F"), None);
        assert_eq!(term_lemma("man/human"), None);
        assert_eq!(term_lemma("one over many things here"), None);
        assert_eq!(
            term_lemma("existence naturalism (N1)").as_deref(),
            Some("existence naturalism")
        );
    }

    #[test]
    fn the_shipped_function_list_parses() {
        let words = function_words(FUNCTION_WORDS).unwrap();
        assert!(
            words
                .iter()
                .any(|w| w.lemma == "the" && w.category == "article")
        );
        let be = words.iter().find(|w| w.lemma == "be").unwrap();
        assert!(be.forms.contains(&"is".to_owned()));
        assert!(
            !be.forms.contains(&"being".to_owned()),
            "being is a technical word"
        );
        for word in &words {
            assert_eq!(word.lemma, word.lemma.to_lowercase());
        }
    }

    #[test]
    fn function_list_errors() {
        assert!(function_words("the").is_err());
        assert!(function_words("[nonsense]\nthe").is_err());
        assert!(function_words("[article]\nthe\nthe").is_err());
        assert!(function_words("[article]\nthe\n[separation]\nfoo: bar").is_err());
    }

    #[test]
    fn uuid4_shape() {
        let id = uuid4().unwrap();
        assert_eq!(id.len(), 36);
        assert_eq!(&id[14..15], "4");
    }
}
