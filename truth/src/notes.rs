//! Free-form research notes (`docs/notes/**/*.md`) as discovery material
//! (#952, #954 slice B8).
//!
//! A note is not a corpus record: it has no ID, status or authority. This
//! module splits a note into heading sections (GitHub anchors) and finds the
//! records a section mentions **explicitly**:
//!
//! - an exact record ID (a uuid) or legacy ID (`STMT-…`, `JOINT-…`), as one
//!   whole token of ID characters;
//! - an exact record label written as a whole inline code span containing a
//!   space (`` `Act is PRIOR_1 to potency` ``); single-word code spans are
//!   usually Lean or shell identifiers and are not read as labels;
//! - a corpus record path (`corpus/statements/x.json`, also inside a link).
//!
//! Nothing else links a note to a record: no word overlap, no similarity and
//! no inferred implication. A token shaped like an ID (a uuid, or a reserved
//! prefix such as `STMT-`) or a corpus path that names no record is reported
//! as unresolved, never linked. `truth index` stores these links; `dossier`,
//! `context` and `related` list the sections that mention their records.

use crate::Record;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::Path,
};

/// The note directory, relative to the checkout.
pub const DIRECTORY: &str = "docs/notes";
/// Notes larger than this are not indexed (a bound on broad indexing).
pub const MAX_BYTES: u64 = 1 << 20;
/// Legacy-ID prefixes that mark a token as an intended record reference, so
/// an unknown one is reported as unresolved.
const RESERVED: &[&str] = &[
    "STMT-", "DEF-", "DISAMB-", "INF-", "REL-", "ATTEMPT-", "MODEL-", "CONFIG-",
];
/// What every listing of note links says about itself.
pub const BOUNDARY: &str = "free-form notes linked only by explicit ID, label or path mentions; \
     a mention is not an entailment, a status or source evidence";

/// One heading section of a note. The preamble before the first heading has
/// an empty anchor and heading and level 0.
#[derive(Clone, Debug, PartialEq)]
pub struct Section {
    pub anchor: String,
    pub heading: String,
    pub level: u8,
    /// 1-based line of the heading (1 for the preamble).
    pub line: usize,
    pub body: String,
}

/// A parsed note: its path, title (first level-1 heading, else the file
/// stem) and sections in file order.
#[derive(Clone, Debug)]
pub struct Note {
    pub path: String,
    pub title: String,
    pub sections: Vec<Section>,
}

impl Note {
    /// `path#anchor`, or the bare path for the preamble (a heading whose
    /// anchor is empty keeps its `#`, so it never collides with it).
    pub fn key(&self, section: &Section) -> String {
        if section.level == 0 {
            self.path.clone()
        } else {
            format!("{}#{}", self.path, section.anchor)
        }
    }
}

/// How a mention names a record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum How {
    Id,
    LegacyId,
    Label,
    Path,
}

impl How {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Id => "id",
            Self::LegacyId => "legacy_id",
            Self::Label => "label",
            Self::Path => "path",
        }
    }
}

/// A candidate mention in a section: its text and 1-based line.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mention {
    pub text: String,
    pub line: usize,
    /// A label candidate (a whole code span) rather than an ID or path token.
    pub label: bool,
    pub path: bool,
}

/// One resolved link from a section to a record.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Link {
    pub kind: String,
    pub id: String,
    pub mention: String,
    pub how: How,
    pub line: usize,
}

/// A mention shaped like a record reference that names no record.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Unresolved {
    pub mention: String,
    pub how: How,
    pub line: usize,
}

/// Exact id / legacy id / label / path lookup over records.
#[derive(Default)]
pub struct Lookup {
    ids: HashMap<String, BTreeSet<String>>,
    legacy: HashMap<String, BTreeSet<(String, String)>>,
    labels: HashMap<String, BTreeSet<(String, String)>>,
    paths: HashMap<String, BTreeSet<(String, String)>>,
}

impl Lookup {
    /// Adds one record of `kind` read from `path`. An index passage
    /// projection keeps its legacy id and label under `passage`.
    pub fn add(&mut self, kind: &str, path: &str, record: &Map<String, Value>) {
        let Some(id) = record.get("id").and_then(Value::as_str) else {
            return;
        };
        let record = match record.get("passage") {
            Some(Value::Object(passage)) if kind == "passages" => passage,
            _ => record,
        };
        let pair = (kind.to_owned(), id.to_owned());
        self.ids
            .entry(id.to_owned())
            .or_default()
            .insert(kind.to_owned());
        for (field, map) in [("legacy_id", &mut self.legacy), ("label", &mut self.labels)] {
            if let Some(value) = record
                .get(field)
                .and_then(Value::as_str)
                .filter(|value| !value.is_empty())
            {
                map.entry(value.to_owned())
                    .or_default()
                    .insert(pair.clone());
            }
        }
        self.paths.entry(path.to_owned()).or_default().insert(pair);
    }

    /// The lookup over every record of a loaded corpus.
    pub fn of_corpus(corpus: &crate::Corpus) -> Self {
        let mut lookup = Self::default();
        for &kind in crate::KINDS {
            for Record { path, fields } in corpus.entries(kind) {
                lookup.add(kind, path, fields);
            }
        }
        lookup
    }

    /// The (kind, id) pairs `mention` names, and how.
    fn resolve(&self, mention: &Mention) -> Option<(How, Vec<(String, String)>)> {
        let text = mention.text.as_str();
        let found = if mention.path {
            (How::Path, self.paths.get(text).cloned())
        } else if mention.label {
            (How::Label, self.labels.get(text).cloned())
        } else if let Some(kinds) = self.ids.get(text) {
            let pairs = kinds
                .iter()
                .map(|kind| (kind.clone(), text.to_owned()))
                .collect();
            (How::Id, Some(pairs))
        } else {
            (How::LegacyId, self.legacy.get(text).cloned())
        };
        found
            .1
            .filter(|pairs| !pairs.is_empty())
            .map(|pairs| (found.0, pairs.into_iter().collect()))
    }

    /// Resolved links and unresolved reference-shaped mentions of `section`.
    pub fn links(&self, section: &Section) -> (Vec<Link>, Vec<Unresolved>) {
        let mut links = BTreeMap::new();
        let mut unresolved = BTreeMap::new();
        for mention in mentions(section) {
            match self.resolve(&mention) {
                Some((how, pairs)) => {
                    for (kind, id) in pairs {
                        links
                            .entry((kind, id, mention.text.clone(), how))
                            .or_insert(mention.line);
                    }
                }
                None if mention.path || (!mention.label && reference_shaped(&mention.text)) => {
                    let how = if mention.path {
                        How::Path
                    } else if crate::identity::is_uuid(&mention.text) {
                        How::Id
                    } else {
                        How::LegacyId
                    };
                    unresolved
                        .entry((mention.text.clone(), how))
                        .or_insert(mention.line);
                }
                None => {}
            }
        }
        let mut links: Vec<Link> = links
            .into_iter()
            .map(|((kind, id, mention, how), line)| Link {
                kind,
                id,
                mention,
                how,
                line,
            })
            .collect();
        links.sort_by(|a, b| (a.line, &a.kind, &a.id).cmp(&(b.line, &b.kind, &b.id)));
        let mut unresolved: Vec<Unresolved> = unresolved
            .into_iter()
            .map(|((mention, how), line)| Unresolved { mention, how, line })
            .collect();
        unresolved.sort_by(|a, b| (a.line, &a.mention).cmp(&(b.line, &b.mention)));
        (links, unresolved)
    }
}

fn reference_shaped(token: &str) -> bool {
    crate::identity::is_uuid(token)
        || RESERVED
            .iter()
            .any(|prefix| token.len() > prefix.len() && token.starts_with(prefix))
}

/// Every `docs/notes/**/*.md` path of at most [`MAX_BYTES`], relative to
/// `root`, sorted part by part. Symlinks are not followed; a missing
/// directory has no notes.
pub fn inputs(root: &Path) -> Result<Vec<String>, String> {
    fn walk(
        directory: &Path,
        parts: &mut Vec<String>,
        out: &mut Vec<Vec<String>>,
    ) -> Result<(), String> {
        let entries =
            fs::read_dir(directory).map_err(|error| format!("{}: {error}", directory.display()))?;
        for entry in entries {
            let entry = entry.map_err(|error| error.to_string())?;
            let name = entry
                .file_name()
                .into_string()
                .map_err(|name| format!("non-UTF-8 note path {name:?}"))?;
            let kind = entry.file_type().map_err(|error| error.to_string())?;
            parts.push(name);
            if kind.is_dir() {
                walk(&entry.path(), parts, out)?;
            } else if kind.is_file()
                && parts.last().is_some_and(|name| name.ends_with(".md"))
                && entry
                    .metadata()
                    .is_ok_and(|metadata| metadata.len() <= MAX_BYTES)
            {
                out.push(parts.clone());
            }
            parts.pop();
        }
        Ok(())
    }
    let directory = root.join(DIRECTORY);
    if !directory.is_dir() {
        return Ok(Vec::new());
    }
    let mut found = Vec::new();
    let mut parts: Vec<String> = DIRECTORY.split('/').map(str::to_owned).collect();
    walk(&directory, &mut parts, &mut found)?;
    found.sort();
    Ok(found.into_iter().map(|parts| parts.join("/")).collect())
}

/// Every note with its bytes, in [`inputs`] order.
pub fn read_all(root: &Path) -> Result<Vec<(String, Vec<u8>)>, String> {
    inputs(root)?
        .into_iter()
        .map(|path| {
            fs::read(root.join(&path))
                .map(|bytes| (path.clone(), bytes))
                .map_err(|error| format!("{path}: {error}"))
        })
        .collect()
}

/// An ATX heading: its level and text, outside fenced code.
fn heading(line: &str) -> Option<(u8, String)> {
    let indent = line.len() - line.trim_start_matches(' ').len();
    if indent > 3 {
        return None;
    }
    let rest = &line[indent..];
    let level = rest.len() - rest.trim_start_matches('#').len();
    if !(1..=6).contains(&level) {
        return None;
    }
    let text = &rest[level..];
    if !(text.is_empty() || text.starts_with([' ', '\t'])) {
        return None;
    }
    let text = text.trim();
    // A closing run of hashes counts only after a space (`# C#` keeps it).
    let text = match text.trim_end_matches('#') {
        "" => "",
        stripped if stripped.ends_with([' ', '\t']) => stripped.trim_end(),
        _ => text,
    };
    Some((level as u8, text.to_owned()))
}

/// GitHub's heading anchor: lower case, letters, digits, `-` and `_` kept,
/// spaces to `-`, everything else dropped.
pub fn slug(heading: &str) -> String {
    heading
        .chars()
        .filter_map(|c| {
            if c == ' ' {
                Some('-')
            } else if c.is_alphanumeric() || c == '-' || c == '_' {
                Some(c)
            } else {
                None
            }
        })
        .flat_map(char::to_lowercase)
        .collect()
}

fn fence(line: &str) -> Option<(char, usize)> {
    let trimmed = line.trim_start();
    if line.len() - trimmed.len() > 3 {
        return None;
    }
    let marker = trimmed.chars().next()?;
    if marker != '`' && marker != '~' {
        return None;
    }
    let count = trimmed.len() - trimmed.trim_start_matches(marker).len();
    (count >= 3).then_some((marker, count))
}

/// Splits a note into its title and heading sections.
pub fn parse(path: &str, text: &str) -> Note {
    let mut sections = vec![Section {
        anchor: String::new(),
        heading: String::new(),
        level: 0,
        line: 1,
        body: String::new(),
    }];
    let mut used: BTreeMap<String, usize> = BTreeMap::new();
    let mut open: Option<(char, usize)> = None;
    let mut title = None;
    for (index, line) in text.lines().enumerate() {
        if let Some((marker, count)) = open {
            if fence(line).is_some_and(|(m, c)| m == marker && c >= count) {
                open = None;
            }
        } else if let Some(found) = fence(line) {
            open = Some(found);
        } else if let Some((level, heading)) = heading(line) {
            // github-slugger: a taken anchor gets the next `-N` suffix that is
            // itself free, and every assigned anchor is reserved.
            let base = slug(&heading);
            let mut anchor = base.clone();
            while used.contains_key(&anchor) {
                let count = used.get_mut(&base).expect("base is reserved");
                *count += 1;
                anchor = format!("{base}-{count}");
            }
            used.insert(anchor.clone(), 0);
            if level == 1 && title.is_none() {
                title = Some(heading.clone());
            }
            sections.push(Section {
                anchor,
                heading,
                level,
                line: index + 1,
                body: String::new(),
            });
            continue;
        }
        let body = &mut sections.last_mut().expect("a section").body;
        body.push_str(line);
        body.push('\n');
    }
    if sections[0].body.trim().is_empty() {
        sections.remove(0);
    }
    let stem = path
        .rsplit('/')
        .next()
        .unwrap_or(path)
        .trim_end_matches(".md");
    Note {
        path: path.to_owned(),
        title: title.unwrap_or_else(|| stem.to_owned()),
        sections,
    }
}

fn id_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.')
}

/// Candidate mentions of a section: ID tokens (whole runs of ID characters
/// containing a hyphen, trailing `.`/`-` trimmed), whole inline code spans
/// with a space (label candidates), and `corpus/…json` paths. Line numbers
/// count the heading line.
pub fn mentions(section: &Section) -> Vec<Mention> {
    let mut out = Vec::new();
    let mut open: Option<(char, usize)> = None;
    let add_tokens = |text: &str, line: usize, out: &mut Vec<Mention>| {
        for token in text.split(|c: char| !id_char(c)) {
            let token = token.trim_matches(|c| c == '.' || c == '-');
            // A file name (`STMT-X.json`) names its record by its stem.
            let token = token.strip_suffix(".json").unwrap_or(token);
            if token.contains('-') {
                out.push(Mention {
                    text: token.to_owned(),
                    line,
                    label: false,
                    path: false,
                });
            }
        }
        let mut rest = text;
        while let Some(start) = rest.find("corpus/") {
            let tail = &rest[start..];
            let end = tail
                .find(|c: char| !(id_char(c) || c == '/'))
                .unwrap_or(tail.len());
            let candidate = &tail[..end];
            if let Some(stop) = candidate.find(".json") {
                out.push(Mention {
                    text: candidate[..stop + 5].to_owned(),
                    line,
                    label: false,
                    path: true,
                });
            }
            rest = &tail["corpus/".len()..];
        }
    };
    let offset = usize::from(section.level > 0);
    if section.level > 0 {
        add_tokens(&section.heading, section.line, &mut out);
        spans(&section.heading, section.line, &mut out);
    }
    for (index, line) in section.body.lines().enumerate() {
        let number = section.line + offset + index;
        if let Some((marker, count)) = open {
            if fence(line).is_some_and(|(m, c)| m == marker && c >= count) {
                open = None;
            }
        } else if let Some(found) = fence(line) {
            open = Some(found);
        } else {
            spans(line, number, &mut out);
        }
        add_tokens(line, number, &mut out);
    }
    out
}

/// Inline code spans of one backtick with a space inside: label candidates.
fn spans(line: &str, number: usize, out: &mut Vec<Mention>) {
    let mut parts = line.split('`');
    parts.next();
    while let (Some(inside), Some(_)) = (parts.next(), parts.clone().next()) {
        parts.next();
        let inside = inside.trim();
        if inside.contains(' ') {
            out.push(Mention {
                text: inside.to_owned(),
                line: number,
                label: true,
                path: false,
            });
        }
    }
}

/// One mention of a selected record by a note section, as JSON.
pub fn mention_json(note: &Note, section: &Section, link: &Link) -> Value {
    json!({
        "path": note.path,
        "section": note.key(section),
        "heading": section.heading,
        "line": link.line,
        "kind": link.kind,
        "id": link.id,
        "mention": link.mention,
        "how": link.how.as_str(),
    })
}

/// The note sections of `root` that explicitly mention one of `ids`, in
/// note path and line order. Reads the notes directly (no index).
pub fn mentioning(
    root: &Path,
    lookup: &Lookup,
    ids: &BTreeSet<&str>,
) -> Result<Vec<Value>, String> {
    let mut out = Vec::new();
    for (path, bytes) in read_all(root)? {
        let note = parse(&path, &String::from_utf8_lossy(&bytes));
        for section in &note.sections {
            for link in lookup.links(section).0 {
                if ids.contains(link.id.as_str()) {
                    out.push(mention_json(&note, section, &link));
                }
            }
        }
    }
    Ok(out)
}

/// The text block `dossier`, `context` and `related` append: one line per
/// mentioning section line (its mentions and the kinds they name), at most
/// `limit` lines.
pub fn format_mentions(found: &[Value], limit: usize) -> String {
    let mut lines: Vec<(String, BTreeSet<String>, BTreeSet<String>)> = Vec::new();
    for entry in found {
        let place = format!(
            "{} line {}",
            entry["section"].as_str().unwrap_or_default(),
            entry["line"]
        );
        if lines.last().is_none_or(|(last, _, _)| *last != place) {
            lines.push((place, BTreeSet::new(), BTreeSet::new()));
        }
        let (_, mentions, kinds) = lines.last_mut().expect("a line");
        mentions.insert(entry["mention"].as_str().unwrap_or_default().to_owned());
        kinds.insert(entry["kind"].as_str().unwrap_or_default().to_owned());
    }
    let mut text = format!("\n{HEADER} ({BOUNDARY}):\n");
    if lines.is_empty() {
        text.push_str("- none\n");
    }
    for (place, mentions, kinds) in lines.iter().take(limit) {
        let mentions: Vec<&str> = mentions.iter().map(String::as_str).collect();
        let kinds: Vec<&str> = kinds.iter().map(String::as_str).collect();
        text.push_str(&format!(
            "- {place}: {} ({})\n",
            mentions.join(", "),
            kinds.join(", ")
        ));
    }
    if lines.len() > limit {
        text.push_str(&format!(
            "- … {} more (--json lists all)\n",
            lines.len() - limit
        ));
    }
    text
}

/// The first line of the appended block; parity tests cut the text there.
pub const HEADER: &str = "Notes mentioning the target records";

#[cfg(test)]
mod tests {
    use super::*;

    const TEXT: &str = "Intro STMT-A and `two words`.\n\n# Title here\n\nSee `S` and STMT-A.\n\
        ```sh\n# not a heading\ntruth context RES-X\n```\n## Same\nbody corpus/statements/s.json.\n\
        ## Same\nSTMT-MISSING and 0123abcd-0000-0000-0000-000000000000 and NO-SUCH-WORD\n";

    fn lookup() -> Lookup {
        let mut lookup = Lookup::default();
        let record = |value: Value| value.as_object().unwrap().clone();
        lookup.add(
            "statements",
            "corpus/statements/s.json",
            &record(
                json!({"id": "11111111-2222-3333-4444-555555555555", "legacy_id": "STMT-A",
                           "label": "two words"}),
            ),
        );
        lookup.add(
            "arguments",
            "corpus/arguments/x.json",
            &record(json!({"id": "RES-X"})),
        );
        lookup.add(
            "results",
            "corpus/results/x.json",
            &record(json!({"id": "RES-X", "label": "S"})),
        );
        lookup
    }

    #[test]
    fn sections_anchors_and_fences() {
        let note = parse("docs/notes/n.md", TEXT);
        assert_eq!(note.title, "Title here");
        let anchors: Vec<_> = note.sections.iter().map(|s| s.anchor.as_str()).collect();
        assert_eq!(anchors, ["", "title-here", "same", "same-1"]);
        assert_eq!(note.key(&note.sections[2]), "docs/notes/n.md#same");
        assert_eq!(note.sections[1].line, 3);
        assert!(note.sections[1].body.contains("# not a heading"));
        assert_eq!(
            slug("Follow-up (2026-11-03): the law"),
            "follow-up-2026-11-03-the-law"
        );
        assert_eq!(parse("docs/notes/x.md", "no heading").title, "x");
        let note = parse("docs/notes/d.md", "# R\n## R\n## R-1\n## R\n");
        let anchors: Vec<_> = note.sections.iter().map(|s| s.anchor.as_str()).collect();
        assert_eq!(anchors, ["r", "r-1", "r-1-1", "r-2"]);
        let note = parse("docs/notes/p.md", "Intro\n# ???\nBody\n");
        let keys: Vec<_> = note.sections.iter().map(|s| note.key(s)).collect();
        assert_eq!(keys, ["docs/notes/p.md", "docs/notes/p.md#"]);
    }

    #[test]
    fn only_explicit_mentions_link() {
        let note = parse("docs/notes/n.md", TEXT);
        let lookup = lookup();
        let (links, unresolved) = lookup.links(&note.sections[0]);
        let found: Vec<_> = links
            .iter()
            .map(|l| (l.how, l.mention.as_str(), l.line))
            .collect();
        assert_eq!(
            found,
            [(How::LegacyId, "STMT-A", 1), (How::Label, "two words", 1)]
        );
        assert!(unresolved.is_empty());
        // `S` is a single-word code span: not a label mention. RES-X in a
        // fenced command is an explicit ID of an argument and a result.
        let (links, _) = lookup.links(&note.sections[1]);
        let found: Vec<_> = links
            .iter()
            .map(|l| (l.kind.as_str(), l.mention.as_str(), l.line))
            .collect();
        assert_eq!(
            found,
            [
                ("statements", "STMT-A", 5),
                ("arguments", "RES-X", 8),
                ("results", "RES-X", 8)
            ]
        );
        let (links, _) = lookup.links(&note.sections[2]);
        assert_eq!((links[0].how, links[0].line), (How::Path, 11));
        let (links, unresolved) = lookup.links(&note.sections[3]);
        assert!(links.is_empty());
        let found: Vec<_> = unresolved
            .iter()
            .map(|u| (u.how, u.mention.as_str()))
            .collect();
        // NO-SUCH-WORD has no reserved prefix: ordinary hyphenated prose.
        assert_eq!(
            found,
            [
                (How::Id, "0123abcd-0000-0000-0000-000000000000"),
                (How::LegacyId, "STMT-MISSING")
            ]
        );
    }

    #[test]
    fn mentions_block_lists_and_bounds() {
        let entry = |line: usize, kind: &str| {
            json!({"section": "docs/notes/n.md#a", "line": line, "kind": kind, "id": "S",
                   "mention": "STMT-S", "how": "legacy_id"})
        };
        let text = format_mentions(
            &[
                entry(3, "arguments"),
                entry(3, "results"),
                entry(9, "results"),
            ],
            1,
        );
        assert!(text.starts_with(&format!("\n{HEADER} (")));
        assert!(
            text.contains("- docs/notes/n.md#a line 3: STMT-S (arguments, results)\n- … 1 more")
        );
        assert!(format_mentions(&[], 5).ends_with("- none\n"));
    }
}
