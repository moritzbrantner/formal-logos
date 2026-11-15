//! The formal status of every definition record (#1652 L3).
//!
//! Owner direction (2026-11-16): "A lot of truth should be settled by Lean,
//! because this is formally verified. What we can't describe in Lean, or
//! haven't yet, should be described in prose in the glossary or the lexicon."
//!
//! Lean decides the status. `scripts/DefinitionStatus.lean` reports, for each
//! `lean_declaration` of a `DEF-…` record, what kind of constant it is and,
//! for a definition, the head and project constants of its body (the
//! one-step unfolding). [`classify`] turns those facts into a formal status:
//!
//! - `defined`: a definition with a body (including `abbrev` and
//!   `instance`), a structure, class or inductive type, a constructor;
//! - `primitive`: an `opaque` or `axiom` constant, a structure field (a
//!   projection: an uninterpreted component of a frame or signature), or a
//!   definition whose body applies one of its own parameters to arguments
//!   without project vocabulary (it renames the parameter);
//! - `constraint`: a constant whose type is a proposition (a theorem, a
//!   `Prop` axiom or field): it constrains other constants instead of
//!   defining one;
//! - `unresolved`: no constant of that name in the `TruthCore` environment
//!   (a section `variable` is not a constant).
//!
//! The facts are cached in the generated `corpus/definition-status.json`, one
//! entry per declaration with an input identity: the SHA-256 of the
//! declaration's source file (or, for an unresolved name, of every Lean file
//! that mentions it; for a library constant, of the toolchain and manifest),
//! plus the exporter's own hash. `truth check` and `truth lexicon` read the
//! cache without running Lean and treat an entry whose identity no longer
//! matches as not computed. `truth definitions refresh` runs Lean.
//!
//! Prose covers what Lean does not: a definition whose computed status is
//! not `defined` carries a `formal_gap` block (meaning, examples or why
//! they are unavailable, exclusions, open obligations). Missing blocks are
//! warnings with a shrink-only allowlist, errors once the config is strict.
//! Nothing here changes proof, source or frontier closure.

use crate::{Corpus, bind_check, lexicon};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
};

pub const TOOL: &str = "scripts/DefinitionStatus.lean";
pub const CACHE: &str = "corpus/definition-status.json";
pub const ALLOWLIST: &str = "corpus/definition-prose-allowlist.json";
pub const CONFIG: &str = "corpus/definition-status-config.json";
/// The module the exporter imports: every library module, not the Challenges.
pub const ROOT_MODULE: &str = "TruthCore";
/// Inputs that fix a library (Lean core, Mathlib) constant.
const LIBRARY_INPUTS: &[&str] = &["lean-toolchain", "lake-manifest.json"];
const GAP_FIELDS: &[&str] = &[
    "kind",
    "meaning",
    "examples",
    "examples_unavailable",
    "exclusions",
    "open_obligations",
];

type Obj = Map<String, Value>;

/// What Lean settles about one declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Status {
    Defined,
    Primitive,
    Constraint,
    Unresolved,
}

impl Status {
    pub const ALL: [Status; 4] = [
        Status::Defined,
        Status::Primitive,
        Status::Constraint,
        Status::Unresolved,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Status::Defined => "defined",
            Status::Primitive => "primitive",
            Status::Constraint => "constraint",
            Status::Unresolved => "unresolved",
        }
    }

    pub fn parse(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|status| status.name() == text)
    }

    /// Whether the definition record must carry a `formal_gap` block.
    pub fn needs_prose(self) -> bool {
        self != Status::Defined
    }
}

fn text<'a>(value: &'a Value, field: &str) -> &'a str {
    value.get(field).and_then(Value::as_str).unwrap_or_default()
}

/// The formal status of one exporter entry and the reason, in words.
pub fn classify(lean: &Value) -> (Status, String) {
    if lean.get("found") != Some(&Value::Bool(true)) {
        return (
            Status::Unresolved,
            "no constant of this name in the TruthCore environment (a section variable, a Challenge-only or a misspelled name)".into(),
        );
    }
    let kind = text(lean, "kind");
    if lean.get("proof") == Some(&Value::Bool(true)) {
        return (
            Status::Constraint,
            format!(
                "a {kind} whose type is a proposition: it constrains other constants instead of defining one"
            ),
        );
    }
    match kind {
        "opaque" | "axiom" => (
            Status::Primitive,
            format!("an {kind} constant without a body"),
        ),
        "projection" => (
            Status::Primitive,
            format!(
                "a field of the structure {}: an uninterpreted component, constrained only by the other fields and by the hypotheses that use it",
                text(lean, "structure")
            ),
        ),
        _ if lean.get("parameter_wrapper") == Some(&Value::Bool(true)) => (
            Status::Primitive,
            format!(
                "a {kind} whose body applies one of its own parameters to arguments without project vocabulary: the parameter carries the meaning"
            ),
        ),
        "definition" | "abbrev" | "instance" => (Status::Defined, format!("a {kind} with a body")),
        "structure" | "class" | "inductive" => (
            Status::Defined,
            format!("a {kind} type: its constructors and fields settle what it is"),
        ),
        "constructor" | "recursor" | "quotient" => {
            (Status::Defined, format!("a {kind} of an inductive type"))
        }
        other => (
            Status::Unresolved,
            format!("an unknown constant kind {other:?} (update truth/src/definition_status.rs)"),
        ),
    }
}

// ---------------------------------------------------------------------------
// The exporter and its cache.

/// The exporter input: every distinct `lean_declaration`, sorted.
pub fn declarations(corpus: &Corpus) -> Vec<String> {
    corpus
        .records("definitions")
        .into_iter()
        .filter_map(|record| record.get("lean_declaration").and_then(Value::as_str))
        .filter(|name| !name.is_empty())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

pub fn tool_input(corpus: &Corpus) -> String {
    json!({"root_module": ROOT_MODULE, "declarations": declarations(corpus)}).to_string()
}

/// Runs `scripts/DefinitionStatus.lean` (after `lake build`).
pub fn run_tool(root: &Path, input: &str) -> Result<Vec<Value>, String> {
    bind_check::run_exporter(root, TOOL, input, "definitions refresh")
}

/// One cached declaration: its input identity and the exporter's facts
/// (without the `declaration` key).
#[derive(Clone, Debug, PartialEq)]
pub struct Entry {
    pub identity: String,
    pub lean: Value,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Cache {
    pub tool_sha256: String,
    pub entries: BTreeMap<String, Entry>,
}

pub fn parse_cache(source: &str) -> Result<Cache, String> {
    let value: Value =
        serde_json::from_str(source).map_err(|error| format!("{CACHE}: invalid JSON: {error}"))?;
    let tool_sha256 = value
        .get("tool_sha256")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{CACHE}: tool_sha256 must be a string"))?
        .to_owned();
    let mut entries = BTreeMap::new();
    for (declaration, entry) in value
        .get("entries")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{CACHE}: entries must be an object"))?
    {
        let identity = entry
            .get("identity")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{CACHE}: {declaration}: identity must be a string"))?;
        let lean = entry
            .get("lean")
            .filter(|lean| lean.is_object())
            .ok_or_else(|| format!("{CACHE}: {declaration}: lean must be an object"))?;
        entries.insert(
            declaration.clone(),
            Entry {
                identity: identity.to_owned(),
                lean: lean.clone(),
            },
        );
    }
    Ok(Cache {
        tool_sha256,
        entries,
    })
}

pub fn read_cache(root: &Path) -> Result<Option<Cache>, String> {
    match fs::read_to_string(root.join(CACHE)) {
        Ok(source) => parse_cache(&source).map(Some),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(format!("{CACHE}: {error}")),
    }
}

/// The cache file: one declaration per line, sorted, so diffs stay local.
pub fn render_cache(cache: &Cache) -> String {
    let mut out = format!(
        "{{\n  \"schema_version\": 1,\n  \"note\": \"Generated by `truth definitions refresh --write` from {TOOL} after `lake build`; do not edit (docs/corpus-model.md, Formal status of definitions).\",\n  \"tool_sha256\": {},\n  \"entries\": {{",
        json!(cache.tool_sha256)
    );
    let mut first = true;
    for (declaration, entry) in &cache.entries {
        out.push_str(if first { "\n    " } else { ",\n    " });
        first = false;
        out.push_str(&format!(
            "{}: {{\"identity\": {}, \"lean\": {}}}",
            json!(declaration),
            json!(entry.identity),
            entry.lean
        ));
    }
    out.push_str(if first { "}\n}\n" } else { "\n  }\n}\n" });
    out
}

/// Offline input identities of cache entries (see the module docs).
pub struct Sources {
    root: PathBuf,
    hashes: HashMap<String, String>,
    lean_files: Option<Vec<(String, String)>>,
}

fn is_ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '!' || c == '?'
}

fn mentions(text: &str, word: &str) -> bool {
    text.match_indices(word).any(|(at, _)| {
        !text[..at].chars().next_back().is_some_and(is_ident)
            && !text[at + word.len()..].chars().next().is_some_and(is_ident)
    })
}

impl Sources {
    pub fn new(root: &Path) -> Self {
        Self {
            root: root.to_owned(),
            hashes: HashMap::new(),
            lean_files: None,
        }
    }

    pub fn tool_sha256(&mut self) -> String {
        self.file(TOOL)
    }

    fn file(&mut self, path: &str) -> String {
        if let Some(hash) = self.hashes.get(path) {
            return hash.clone();
        }
        let hash = match fs::read(self.root.join(path)) {
            Ok(bytes) => bind_check::sha256_hex(&bytes),
            Err(_) => "missing".into(),
        };
        self.hashes.insert(path.to_owned(), hash.clone());
        hash
    }

    fn lean_files(&mut self) -> &[(String, String)] {
        if self.lean_files.is_none() {
            let mut files = Vec::new();
            let mut pending = vec![self.root.join(ROOT_MODULE)];
            while let Some(directory) = pending.pop() {
                let Ok(read) = fs::read_dir(&directory) else {
                    continue;
                };
                for item in read.flatten() {
                    let path = item.path();
                    if path.is_dir() {
                        pending.push(path);
                    } else if path.extension().is_some_and(|e| e == "lean")
                        && let (Ok(text), Ok(relative)) =
                            (fs::read_to_string(&path), path.strip_prefix(&self.root))
                    {
                        files.push((relative.to_string_lossy().replace('\\', "/"), text));
                    }
                }
            }
            files.sort();
            self.lean_files = Some(files);
        }
        self.lean_files.as_deref().unwrap_or_default()
    }

    /// The input identity of `declaration` whose exporter facts are `lean`.
    pub fn identity(&mut self, declaration: &str, lean: &Value) -> String {
        if lean.get("found") == Some(&Value::Bool(true)) {
            let module = text(lean, "module");
            if module == ROOT_MODULE || module.starts_with(&format!("{ROOT_MODULE}.")) {
                let path = format!("{}.lean", module.replace('.', "/"));
                let hash = self.file(&path);
                return format!("source:{path}:{hash}");
            }
            let joined: String = LIBRARY_INPUTS
                .iter()
                .map(|path| format!("{path} {}\n", self.file(path)))
                .collect();
            return format!("library:{}", bind_check::sha256_hex(joined.as_bytes()));
        }
        let tail = declaration
            .rsplit('.')
            .next()
            .unwrap_or(declaration)
            .trim_matches(['«', '»']);
        let joined: String = self
            .lean_files()
            .iter()
            .filter(|(_, text)| mentions(text, tail))
            .map(|(path, text)| format!("{path} {}\n", bind_check::sha256_hex(text.as_bytes())))
            .collect();
        format!("search:{}", bind_check::sha256_hex(joined.as_bytes()))
    }
}

/// The cache for the exporter output `described`.
pub fn build_cache(root: &Path, described: &[Value]) -> Result<Cache, String> {
    let mut sources = Sources::new(root);
    let mut entries = BTreeMap::new();
    for item in described {
        let declaration = item
            .get("declaration")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{TOOL} printed an entry without a declaration: {item}"))?;
        let mut lean = item.clone();
        if let Some(object) = lean.as_object_mut() {
            object.remove("declaration");
        }
        entries.insert(
            declaration.to_owned(),
            Entry {
                identity: sources.identity(declaration, &lean),
                lean,
            },
        );
    }
    Ok(Cache {
        tool_sha256: sources.tool_sha256(),
        entries,
    })
}

/// How `computed` (a fresh Lean run) differs from `committed`: entries
/// whose committed identity matches but whose facts differ (`wrong`), and
/// entries missing or stale in the committed cache (`stale`), and committed
/// entries no definition names any more (`extra`).
#[derive(Debug, Default)]
pub struct Comparison {
    pub wrong: Vec<String>,
    pub stale: Vec<String>,
    pub extra: Vec<String>,
}

pub fn compare(committed: Option<&Cache>, computed: &Cache) -> Comparison {
    let empty = Cache::default();
    let committed = committed.unwrap_or(&empty);
    let same_tool = committed.tool_sha256 == computed.tool_sha256;
    let mut comparison = Comparison::default();
    for (declaration, entry) in &computed.entries {
        match committed.entries.get(declaration) {
            Some(old) if same_tool && old.identity == entry.identity => {
                if old.lean != entry.lean {
                    comparison.wrong.push(declaration.clone());
                }
            }
            _ => comparison.stale.push(declaration.clone()),
        }
    }
    comparison.extra = committed
        .entries
        .keys()
        .filter(|declaration| !computed.entries.contains_key(*declaration))
        .cloned()
        .collect();
    comparison
}

// ---------------------------------------------------------------------------
// The status of each definition record.

#[derive(Clone, Debug)]
pub enum State {
    /// The record names no `lean_declaration`: its prose is its meaning.
    NoLean,
    /// No fresh cache entry: the status is unknown until a refresh.
    Uncomputed,
    Computed {
        status: Status,
        reason: String,
        lean: Value,
    },
}

#[derive(Clone, Debug)]
pub struct Definition {
    pub id: String,
    pub path: String,
    pub label: String,
    pub declaration: Option<String>,
    pub state: State,
    /// The validated `formal_gap` block, if any.
    pub gap: Option<Value>,
    /// The change detector of the allowlist.
    pub hash: String,
}

/// `fnv1a64` over the fields a prose meaning answers to.
pub fn record_hash(record: &Obj) -> String {
    let field = |name: &str| record.get(name).and_then(Value::as_str).unwrap_or_default();
    lexicon::hash(&format!(
        "{}\0{}\0{}\0{}",
        field("term"),
        field("definition"),
        field("note"),
        field("lean_declaration")
    ))
}

fn nonempty_strings(value: Option<&Value>) -> Option<Vec<&str>> {
    value?
        .as_array()?
        .iter()
        .map(|item| item.as_str().filter(|s| !s.trim().is_empty()))
        .collect()
}

/// Validates a `formal_gap` block (always an error when malformed).
pub fn validate_gap(path: &str, gap: &Value) -> Result<(), String> {
    let object = gap
        .as_object()
        .ok_or_else(|| format!("{path}: formal_gap must be an object"))?;
    if let Some(field) = object
        .keys()
        .find(|field| !GAP_FIELDS.contains(&field.as_str()))
    {
        return Err(format!("{path}: formal_gap: unknown field {field}"));
    }
    match object
        .get("kind")
        .and_then(Value::as_str)
        .and_then(Status::parse)
    {
        Some(status) if status.needs_prose() => {}
        _ => {
            return Err(format!(
                "{path}: formal_gap.kind must be primitive, constraint or unresolved"
            ));
        }
    }
    if !object
        .get("meaning")
        .and_then(Value::as_str)
        .is_some_and(|meaning| !meaning.trim().is_empty())
    {
        return Err(format!(
            "{path}: formal_gap.meaning must state the intended interpretation in ordinary language"
        ));
    }
    let examples = match object.get("examples") {
        None => Vec::new(),
        some => nonempty_strings(some).ok_or_else(|| {
            format!("{path}: formal_gap.examples must be a list of non-empty strings")
        })?,
    };
    let unavailable = object
        .get("examples_unavailable")
        .map(|value| value.as_str().filter(|s| !s.trim().is_empty()));
    if unavailable == Some(None) {
        return Err(format!(
            "{path}: formal_gap.examples_unavailable must be a non-empty string"
        ));
    }
    if examples.is_empty() && unavailable.is_none() {
        return Err(format!(
            "{path}: formal_gap needs examples or examples_unavailable saying why none is available"
        ));
    }
    if !nonempty_strings(object.get("exclusions")).is_some_and(|items| !items.is_empty()) {
        return Err(format!(
            "{path}: formal_gap.exclusions must list at least one case or neighbouring notion the term excludes"
        ));
    }
    if nonempty_strings(object.get("open_obligations")).is_none() {
        return Err(format!(
            "{path}: formal_gap.open_obligations must be a list of non-empty strings (empty when none is open)"
        ));
    }
    Ok(())
}

/// The status of every definition record, in file order. A malformed
/// `formal_gap` is an error.
pub fn definitions(
    root: &Path,
    corpus: &Corpus,
    cache: Option<&Cache>,
) -> Result<Vec<Definition>, String> {
    let mut sources = Sources::new(root);
    let tool_fresh = cache.is_some_and(|cache| cache.tool_sha256 == sources.tool_sha256());
    let mut out = Vec::new();
    for record in corpus.entries("definitions") {
        let fields = &record.fields;
        let gap = fields.get("formal_gap").cloned();
        if let Some(gap) = &gap {
            validate_gap(&record.path, gap)?;
        }
        let declaration = fields
            .get("lean_declaration")
            .and_then(Value::as_str)
            .filter(|name| !name.is_empty())
            .map(str::to_owned);
        let state = match (&declaration, cache) {
            (None, _) => State::NoLean,
            (Some(declaration), Some(cache)) if tool_fresh => {
                match cache.entries.get(declaration) {
                    Some(entry) if sources.identity(declaration, &entry.lean) == entry.identity => {
                        let (status, reason) = classify(&entry.lean);
                        State::Computed {
                            status,
                            reason,
                            lean: entry.lean.clone(),
                        }
                    }
                    _ => State::Uncomputed,
                }
            }
            _ => State::Uncomputed,
        };
        out.push(Definition {
            id: fields
                .get("id")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_owned(),
            path: record.path.clone(),
            label: fields
                .get("label")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_owned(),
            declaration,
            state,
            gap,
            hash: record_hash(fields),
        });
    }
    Ok(out)
}

/// The machine-readable formal status of one definition (for `lexicon show`).
pub fn describe(definition: &Definition, record: Option<&Obj>) -> Value {
    let field = |name: &str| {
        record
            .and_then(|r| r.get(name))
            .cloned()
            .unwrap_or(Value::Null)
    };
    let mut out = json!({
        "id": definition.id,
        "lean_declaration": definition.declaration,
    });
    let object = out.as_object_mut().expect("object");
    match &definition.state {
        State::NoLean => {
            object.insert("status".into(), json!("no_lean_declaration"));
        }
        State::Uncomputed => {
            object.insert("status".into(), json!("not_computed"));
        }
        State::Computed {
            status,
            reason,
            lean,
        } => {
            object.insert("status".into(), json!(status.name()));
            object.insert(
                "kind".into(),
                lean.get("kind").cloned().unwrap_or(Value::Null),
            );
            object.insert("reason".into(), json!(reason));
            for key in ["module", "structure", "head", "constants"] {
                if let Some(value) = lean.get(key) {
                    object.insert(key.into(), value.clone());
                }
            }
        }
    }
    let settled = matches!(
        definition.state,
        State::Computed {
            status: Status::Defined,
            ..
        }
    );
    if !settled {
        object.insert(
            "prose".into(),
            match &definition.gap {
                Some(gap) => json!({"source": "formal_gap", "formal_gap": gap}),
                None => json!({
                    "source": "definition",
                    "definition": field("definition"),
                    "note": field("note"),
                    "reason": match &definition.state {
                        State::NoLean => "the record names no Lean declaration",
                        State::Uncomputed => "the Lean status is not computed (stale or missing cache entry)",
                        _ => "no formal_gap block yet (backlog)",
                    },
                }),
            },
        );
    }
    out
}

// ---------------------------------------------------------------------------
// Allowlist, config and the check.

/// Definition id -> record hash: the legacy records that may lack a
/// `formal_gap` block while unchanged.
pub type Allowlist = BTreeMap<String, String>;

pub fn parse_allowlist(source: &str) -> Result<Allowlist, String> {
    let value: Value = serde_json::from_str(source)
        .map_err(|error| format!("{ALLOWLIST}: invalid JSON: {error}"))?;
    value
        .get("definitions")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{ALLOWLIST}: must be an object with a definitions object"))?
        .iter()
        .map(|(id, hash)| {
            hash.as_str()
                .map(|hash| (id.clone(), hash.to_owned()))
                .ok_or_else(|| format!("{ALLOWLIST}: {id} must map to a hash string"))
        })
        .collect()
}

pub fn read_allowlist(root: &Path) -> Result<Option<Allowlist>, String> {
    match fs::read_to_string(root.join(ALLOWLIST)) {
        Ok(source) => parse_allowlist(&source).map(Some),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(format!("{ALLOWLIST}: {error}")),
    }
}

pub fn render_allowlist(allowlist: &Allowlist) -> String {
    let mut out = String::from("{\n  \"schema_version\": 1,\n  \"definitions\": {");
    let mut first = true;
    for (id, hash) in allowlist {
        out.push_str(if first { "\n    " } else { ",\n    " });
        first = false;
        out.push_str(&format!("{}: {}", json!(id), json!(hash)));
    }
    out.push_str(if first { "}\n}\n" } else { "\n  }\n}\n" });
    out
}

fn lacks_prose(definition: &Definition) -> bool {
    definition.gap.is_none()
        && matches!(&definition.state, State::Computed { status, .. } if status.needs_prose())
}

/// The allowlist the corpus needs: every definition Lean leaves primitive,
/// constraint or unresolved without a `formal_gap` block. With `existing`,
/// only what it already grants (same hash): regeneration only shrinks.
/// A definition whose status is not computed keeps its existing grant.
pub fn needed_allowlist(definitions: &[Definition], existing: Option<&Allowlist>) -> Allowlist {
    definitions
        .iter()
        .filter(|definition| {
            lacks_prose(definition)
                || (matches!(definition.state, State::Uncomputed) && definition.gap.is_none())
        })
        .filter(|definition| match existing {
            None => lacks_prose(definition),
            Some(existing) => existing.get(&definition.id) == Some(&definition.hash),
        })
        .map(|definition| (definition.id.clone(), definition.hash.clone()))
        .collect()
}

/// Entries of `head` that `base` does not grant.
pub fn ratchet(base: &Allowlist, head: &Allowlist) -> Vec<String> {
    head.iter()
        .filter_map(|(id, hash)| match base.get(id) {
            None => Some(format!("{id}: new allowlist entry")),
            Some(before) if before != hash => {
                Some(format!("{id}: allowlisted again after the record changed"))
            }
            _ => None,
        })
        .collect()
}

/// The warn-now/strict-later switch, as for the lexicon.
pub fn read_strict(root: &Path) -> Result<bool, String> {
    let source = match fs::read_to_string(root.join(CONFIG)) {
        Ok(source) => source,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(format!("{CONFIG}: {error}")),
    };
    let value: Obj = serde_json::from_str(&source)
        .map_err(|error| format!("{CONFIG}: invalid JSON object: {error}"))?;
    if let Some(field) = value
        .keys()
        .find(|field| !["schema_version", "strict", "note"].contains(&field.as_str()))
    {
        return Err(format!("{CONFIG}: unknown field {field}"));
    }
    value
        .get("strict")
        .and_then(Value::as_bool)
        .ok_or_else(|| format!("{CONFIG}: strict must be true or false"))
}

/// The findings for new or changed records: a missing block outside the
/// allowlist, or a block that disagrees with Lean.
pub fn findings(definitions: &[Definition], allowlist: &Allowlist) -> Vec<String> {
    let mut out = Vec::new();
    for definition in definitions {
        let State::Computed { status, reason, .. } = &definition.state else {
            continue;
        };
        let declaration = definition.declaration.as_deref().unwrap_or_default();
        match (&definition.gap, status.needs_prose()) {
            (None, true) => {
                if allowlist.get(&definition.id) != Some(&definition.hash) {
                    out.push(format!(
                        "{}: Lean reports {declaration} {} ({reason}); add a formal_gap prose meaning (docs/corpus-model.md, Formal status of definitions)",
                        definition.path,
                        status.name()
                    ));
                }
            }
            (Some(gap), true) => {
                let kind = gap.get("kind").and_then(Value::as_str).unwrap_or_default();
                if kind != status.name() {
                    out.push(format!(
                        "{}: formal_gap.kind is {kind}, but Lean reports {declaration} {} ({reason})",
                        definition.path,
                        status.name()
                    ));
                }
            }
            (Some(_), false) => out.push(format!(
                "{}: formal_gap is present, but Lean settles {declaration} ({reason}); remove the block or point lean_declaration at the primitive",
                definition.path
            )),
            (None, false) => {}
        }
    }
    out
}

#[derive(Debug, Default)]
pub struct Report {
    pub definitions: usize,
    pub by_status: BTreeMap<&'static str, usize>,
    pub by_kind: BTreeMap<String, usize>,
    pub with_prose: usize,
    pub backlog: usize,
    pub removable: usize,
    pub findings: Vec<String>,
    pub strict: bool,
    pub cache_present: bool,
}

impl Report {
    pub fn summary(&self) -> String {
        let count = |key: &str| self.by_status.get(key).copied().unwrap_or(0);
        let mut text = format!(
            "definitions: formal status of {} records ({CACHE}): {} settled by Lean, {} primitive, {} constraint, {} unresolved, {} without a Lean declaration",
            self.definitions,
            count("defined"),
            count("primitive"),
            count("constraint"),
            count("unresolved"),
            count("no_lean_declaration"),
        );
        if count("not_computed") > 0 {
            text.push_str(&format!(
                ", {} not computed ({}; `truth definitions refresh --write` after `lake build`)",
                count("not_computed"),
                if self.cache_present {
                    "stale or missing cache entries"
                } else {
                    "no cache"
                }
            ));
        }
        text.push_str(&format!(
            "; {} of the primitive, constraint and unresolved carry formal_gap prose, {} are allowlisted backlog ({ALLOWLIST}; `truth definitions status`)",
            self.with_prose, self.backlog
        ));
        if !self.findings.is_empty() {
            text.push_str(&format!(
                "; {} new or changed definition problems ({}, listed above)",
                self.findings.len(),
                if self.strict {
                    "errors"
                } else {
                    "warnings in warn mode"
                }
            ));
        }
        if self.removable > 0 {
            text.push_str(&format!(
                "; {} allowlist entries can shrink (`truth definitions allowlist --write`)",
                self.removable
            ));
        }
        text
    }
}

pub fn report(
    definitions: &[Definition],
    allowlist: &Allowlist,
    strict: bool,
    cache_present: bool,
) -> Report {
    let mut report = Report {
        definitions: definitions.len(),
        strict,
        cache_present,
        findings: findings(definitions, allowlist),
        ..Report::default()
    };
    for definition in definitions {
        let key = match &definition.state {
            State::NoLean => "no_lean_declaration",
            State::Uncomputed => "not_computed",
            State::Computed { status, lean, .. } => {
                *report
                    .by_kind
                    .entry(text(lean, "kind").to_owned())
                    .or_default() += 1;
                if status.needs_prose() {
                    if definition.gap.is_some() {
                        report.with_prose += 1;
                    } else if allowlist.get(&definition.id) == Some(&definition.hash) {
                        report.backlog += 1;
                    }
                }
                status.name()
            }
        };
        *report.by_status.entry(key).or_default() += 1;
    }
    let needed = needed_allowlist(definitions, Some(allowlist));
    report.removable = allowlist.len() - needed.len().min(allowlist.len());
    report
}

/// Everything the commands need.
pub struct Loaded {
    pub cache: Option<Cache>,
    pub definitions: Vec<Definition>,
    pub allowlist: Allowlist,
    pub strict: bool,
}

pub fn load(root: &Path, corpus: &Corpus) -> Result<Loaded, String> {
    let cache = read_cache(root)?;
    let definitions = definitions(root, corpus, cache.as_ref())?;
    Ok(Loaded {
        cache,
        definitions,
        allowlist: read_allowlist(root)?.unwrap_or_default(),
        strict: read_strict(root)?,
    })
}

/// The check `truth check` runs: an error for a malformed block or, when
/// strict, for findings; otherwise the report. Without the cache file the
/// blocks are still validated but nothing is reported (`Ok(None)`), as the
/// lexicon check does without `corpus/lexicon/`.
pub fn check(root: &Path) -> Result<Option<Report>, String> {
    let corpus =
        Corpus::load(root).map_err(|error| format!("{}: {}", error.path, error.message))?;
    let loaded = load(root, &corpus)?;
    if loaded.cache.is_none() {
        return Ok(None);
    }
    let report = report(&loaded.definitions, &loaded.allowlist, loaded.strict, true);
    if loaded.strict && !report.findings.is_empty() {
        let mut message = format!(
            "definitions: {} new or changed definition problems (a definition Lean leaves primitive, constraint or unresolved needs a formal_gap block; {ALLOWLIST} may only shrink):",
            report.findings.len()
        );
        for finding in report.findings.iter().take(20) {
            message.push_str("\n  ");
            message.push_str(finding);
        }
        return Err(message);
    }
    Ok(Some(report))
}

// ---------------------------------------------------------------------------
// Lexicon coverage by formal status.

/// The coverage buckets of a technical token, weakest first.
pub const BUCKETS: &[&str] = &[
    "lean_gap_without_prose",
    "not_computed",
    "technical_without_definition",
    "definition_without_lean",
    "lean_gap_with_prose",
    "lean_defined",
];

fn bucket(definition: &Definition) -> &'static str {
    match &definition.state {
        State::NoLean => "definition_without_lean",
        State::Uncomputed => "not_computed",
        State::Computed {
            status: Status::Defined,
            ..
        } => "lean_defined",
        State::Computed { .. } if definition.gap.is_some() => "lean_gap_with_prose",
        State::Computed { .. } => "lean_gap_without_prose",
    }
}

/// Technical-token coverage split by what settles the meaning. A token
/// counts in the weakest bucket over the definitions its entries reach (the
/// entries' definitions and the senses of their disambiguations, or a
/// tag's disambiguation senses). Ordinary, function and name tokens are
/// `prose_only`.
pub fn coverage_split(loaded: &lexicon::Loaded, definitions: &[Definition]) -> Value {
    let by_id: HashMap<&str, &Definition> = definitions
        .iter()
        .map(|definition| (definition.id.as_str(), definition))
        .collect();
    let weakest = |ids: &mut dyn Iterator<Item = &String>| -> &'static str {
        ids.filter_map(|id| by_id.get(id.as_str()))
            .map(|definition| bucket(definition))
            .min_by_key(|name| BUCKETS.iter().position(|b| b == name))
            .unwrap_or("technical_without_definition")
    };
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut lemmas: BTreeMap<&'static str, BTreeMap<String, usize>> = BTreeMap::new();
    for scan in &loaded.scans {
        for (word, trace) in &scan.occurrences {
            let key = match trace {
                lexicon::Trace::Untraced => "untraced",
                lexicon::Trace::Tag(ids) => {
                    let mut senses = ids
                        .iter()
                        .flat_map(|id| loaded.senses.definitions.get(id).into_iter().flatten());
                    weakest(&mut senses)
                }
                lexicon::Trace::Entries(found) => {
                    let technical: Vec<&lexicon::Entry> = found
                        .iter()
                        .map(|&i| &loaded.lexicon.entries[i])
                        .filter(|entry| entry.class == "technical")
                        .collect();
                    if technical.is_empty() {
                        "prose_only"
                    } else {
                        let mut ids = technical.iter().flat_map(|entry| {
                            entry.definition_ids.iter().chain(
                                entry.disambiguation_ids.iter().flat_map(|id| {
                                    loaded.senses.definitions.get(id).into_iter().flatten()
                                }),
                            )
                        });
                        weakest(&mut ids)
                    }
                }
            };
            *counts.entry(key).or_default() += 1;
            if key == "lean_gap_without_prose" {
                *lemmas
                    .entry(key)
                    .or_default()
                    .entry(word.clone())
                    .or_default() += 1;
            }
        }
    }
    let technical: usize = BUCKETS
        .iter()
        .map(|b| counts.get(b).copied().unwrap_or(0))
        .sum();
    let mut backlog: Vec<(String, usize)> = lemmas
        .remove("lean_gap_without_prose")
        .unwrap_or_default()
        .into_iter()
        .collect();
    backlog.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    backlog.truncate(15);
    json!({
        "technical_tokens": technical,
        "buckets": BUCKETS.iter().map(|b| (b.to_string(), json!(counts.get(b).copied().unwrap_or(0)))).collect::<Map<_, _>>(),
        "prose_only": counts.get("prose_only").copied().unwrap_or(0),
        "untraced": counts.get("untraced").copied().unwrap_or(0),
        "top_without_prose": backlog.into_iter().map(|(word, n)| json!({"word": word, "occurrences": n})).collect::<Vec<_>>(),
    })
}

#[cfg(test)]
mod tests;
