//! The elaborated-type cache (#960): `truth bind-check` records what
//! `scripts/BindTypes.lean` printed for each result theorem, and `truth
//! context` shows it next to the frozen source text when it is still fresh.
//!
//! The cache (`.cache/bind-types.json`, or `$TRUTH_BIND_TYPES_CACHE`) holds,
//! per result, the theorem, its Solution module, a slim copy of the exporter
//! description (binder names, heads and pretty-printed types, the result type
//! and theory-bundle conjuncts) and an input digest. The digest is the SHA-256
//! of the sorted `path NUL sha256` lines of the inputs that determine the
//! description: the Lean toolchain, Lake manifest and configuration, the
//! exporter, the Solution module and every repository module in its source
//! import closure, and the `.olean.hash` that Lake wrote for each of those
//! modules. An entry is fresh exactly when its recorded theorem and module
//! still match the result record and the digest recomputed now equals the
//! recorded one. `context` only reads the cache; it never runs Lean or Lake.
//!
//! The per-hypothesis binding is recomputed from the cached description and
//! the current corpus records with the same rules as `bind-check`
//! ([`bind_check::bind_entries`]), without expression contracts or sense
//! checks. Nothing here is verification evidence: the cache describes the
//! `.olean` files the exporter read, as `bind-check` itself does.

use crate::{
    Corpus,
    bind_check::{self, BIND_TOOL, Contracts, Request, sha256_hex},
    context::{Lean, module_path},
};
use serde::Serialize;
use serde_json::{Map, Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
    fs,
    path::{Path, PathBuf},
};

/// The cache, relative to the repository root.
pub const CACHE: &str = ".cache/bind-types.json";
/// Overrides the cache path (relative paths are below the repository root).
pub const CACHE_ENV: &str = "TRUTH_BIND_TYPES_CACHE";
const SCHEMA: &str = "truth-bind-types-v1";
/// Inputs every description depends on, besides the module closure.
const GLOBAL_INPUTS: &[&str] = &[
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "lakefile.lean",
    BIND_TOOL,
];
const BUILD: &str = ".lake/build/lib/lean";

type Obj = Map<String, Value>;

/// The cache path for `root`.
pub fn cache_path(root: &Path) -> PathBuf {
    match std::env::var_os(CACHE_ENV) {
        Some(path) if !path.is_empty() => root.join(path),
        _ => root.join(CACHE),
    }
}

/// Input digests, with every file hashed at most once.
pub struct Inputs<'a> {
    root: &'a Path,
    lean: Lean<'a>,
    files: RefCell<BTreeMap<String, String>>,
}

impl<'a> Inputs<'a> {
    pub fn new(root: &'a Path) -> Self {
        Self {
            root,
            lean: Lean::new(root),
            files: RefCell::new(BTreeMap::new()),
        }
    }

    /// The SHA-256 of one file below the root, or `missing`.
    fn file(&self, path: &str) -> String {
        if let Some(found) = self.files.borrow().get(path) {
            return found.clone();
        }
        let found = fs::read(self.root.join(path))
            .map_or_else(|_| "missing".to_owned(), |bytes| sha256_hex(&bytes));
        self.files
            .borrow_mut()
            .insert(path.to_owned(), found.clone());
        found
    }

    /// The input paths of a Solution module's description, sorted.
    fn paths(&self, solution: &str) -> Vec<String> {
        let mut modules = vec![solution.to_owned()];
        modules.extend(self.lean.closure(solution).into_iter().map(|(m, _)| m));
        let mut paths: Vec<String> = GLOBAL_INPUTS.iter().map(|p| (*p).to_owned()).collect();
        for module in modules {
            let source = module_path(&module).to_string_lossy().into_owned();
            paths.push(format!(
                "{BUILD}/{}",
                source.replace(".lean", ".olean.hash")
            ));
            paths.push(source);
        }
        paths.sort();
        paths.dedup();
        paths
    }

    /// The input digest of a Solution module's description.
    pub fn digest(&self, solution: &str) -> String {
        let mut lines = String::new();
        for path in self.paths(solution) {
            lines.push_str(&format!("{path}\0{}\n", self.file(&path)));
        }
        format!("sha256:{}", sha256_hex(lines.as_bytes()))
    }

    /// The first input of `solution` whose hash differs from `recorded`.
    fn changed(&self, solution: &str, recorded: &Obj) -> Option<String> {
        self.paths(solution)
            .into_iter()
            .find(|path| recorded.get(path).and_then(Value::as_str) != Some(&self.file(path)))
    }
}

/// The exporter description without what `context` does not show
/// (wrappers, core heads, senses, expression contracts).
fn slim(described: &Value) -> Value {
    fn item(value: &Value) -> Value {
        let mut out = Obj::new();
        for key in ["name", "prop", "head", "type"] {
            if let Some(field) = value.get(key) {
                out.insert(key.into(), field.clone());
            }
        }
        match value.get("bundle") {
            Some(Value::Array(items)) => {
                out.insert("bundle".into(), items.iter().map(item).collect());
            }
            Some(other) if !other.is_null() => {
                out.insert("bundle".into(), other.clone());
            }
            _ => {}
        }
        Value::Object(out)
    }
    json!({
        "theorem": described["theorem"],
        "binders": described["binders"].as_array().map_or_else(Vec::new, |b| b.iter().map(item).collect()),
        "result": item(&described["result"]),
    })
}

/// Records the exporter `described` output for every result it describes
/// (merged with the entries of an existing cache), as `bind-check` does after
/// running Lean. Returns the cache path and the number of entries written.
pub fn write(
    root: &Path,
    corpus: &Corpus,
    described: &[Value],
) -> Result<(PathBuf, usize), String> {
    let path = cache_path(root);
    let inputs = Inputs::new(root);
    let (mut entries, mut hashes) = match load(root) {
        Ok(Some(cache)) => (cache.entries, cache.inputs),
        _ => (Obj::new(), Obj::new()),
    };
    let lookup: HashMap<&str, &Value> = described
        .iter()
        .filter(|entry| entry.get("error").is_none())
        .filter_map(|entry| Some((entry.get("theorem")?.as_str()?, entry)))
        .collect();
    let mut written = 0;
    for (id, record) in corpus.records_by_id("results") {
        let fields = &record.fields;
        let theorem = fields
            .get("theorem")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let solution = fields
            .get("solution_module")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let Some(description) = lookup.get(theorem) else {
            continue;
        };
        if solution.is_empty() {
            continue;
        }
        entries.insert(
            id.to_owned(),
            json!({"theorem": theorem, "solution_module": solution,
                   "input_digest": inputs.digest(solution), "description": slim(description)}),
        );
        written += 1;
    }
    for (file, hash) in inputs.files.borrow().iter() {
        hashes.insert(file.clone(), json!(hash));
    }
    let cache = json!({
        "schema": SCHEMA,
        "note": "written by `truth bind-check` after running scripts/BindTypes.lean; read by `truth context`; not verification evidence",
        "inputs": hashes,
        "results": entries,
    });
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    let temporary = path.with_extension(format!("json.{}.tmp", std::process::id()));
    fs::write(&temporary, serde_json::to_vec(&cache).unwrap_or_default())
        .and_then(|()| fs::rename(&temporary, &path))
        .map_err(|error| {
            let _ = fs::remove_file(&temporary);
            format!("{}: {error}", path.display())
        })?;
    Ok((path, written))
}

/// A loaded cache.
pub struct Cache {
    entries: Obj,
    inputs: Obj,
}

/// The cache of `root`: `None` when absent, an error when unreadable.
pub fn load(root: &Path) -> Result<Option<Cache>, String> {
    let path = cache_path(root);
    let bytes = match fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.to_string()),
    };
    let value: Value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    if value.get("schema") != Some(&json!(SCHEMA)) {
        return Err(format!("not a {SCHEMA} cache"));
    }
    let object = |key: &str| value.get(key).and_then(Value::as_object).cloned();
    Ok(Some(Cache {
        entries: object("results").ok_or("no results object")?,
        inputs: object("inputs").unwrap_or_default(),
    }))
}

/// One result's cache lookup.
#[derive(Debug)]
pub enum Lookup {
    Fresh { description: Value, digest: String },
    Stale(String),
    Missing,
}

impl Cache {
    pub fn lookup(&self, inputs: &Inputs, result: &Obj) -> Lookup {
        let id = result.get("id").and_then(Value::as_str).unwrap_or_default();
        let Some(entry) = self.entries.get(id) else {
            return Lookup::Missing;
        };
        for key in ["theorem", "solution_module"] {
            if entry.get(key) != result.get(key) {
                return Lookup::Stale(format!("its {key} changed"));
            }
        }
        let solution = entry["solution_module"].as_str().unwrap_or_default();
        let digest = inputs.digest(solution);
        if entry.get("input_digest").and_then(Value::as_str) != Some(digest.as_str()) {
            return Lookup::Stale(match inputs.changed(solution, &self.inputs) {
                Some(path) => format!("{path} changed"),
                None => "its Lean inputs changed".into(),
            });
        }
        Lookup::Fresh {
            description: entry["description"].clone(),
            digest,
        }
    }
}

/// A non-Prop binder (vocabulary or type parameter).
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Parameter {
    pub name: String,
    #[serde(rename = "type")]
    pub lean_type: String,
}

/// A hypothesis (or theory-bundle conjunct `h.N`) and the statement it binds.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Hypothesis {
    pub name: String,
    pub head: Value,
    #[serde(rename = "type")]
    pub lean_type: String,
    /// `None`: unbound.
    pub statement_id: Option<String>,
}

/// The elaborated theorem type of one result, from a fresh cache entry.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Elaborated {
    pub input_digest: String,
    /// The signature as Lean pretty-printed it with full names; every binder
    /// is shown as `( )` because the exporter does not record binder kinds.
    pub statement: String,
    pub parameters: Vec<Parameter>,
    pub hypotheses: Vec<Hypothesis>,
    pub conclusion: Hypothesis,
    /// Premises no hypothesis binds.
    pub missing_premises: Vec<String>,
    /// `bound`, `pinned` or `mismatch` of the type binding alone (no
    /// contracts or senses), recomputed from the current records.
    pub binding: String,
    pub advisory: bool,
}

fn string(value: &Value) -> String {
    value.as_str().unwrap_or_default().to_owned()
}

/// The elaborated view of `result` from its cached `description`.
pub fn elaborate(corpus: &Corpus, result: &Obj, description: &Value, digest: &str) -> Elaborated {
    let argument = corpus
        .get(
            "arguments",
            result
                .get("argument_id")
                .and_then(Value::as_str)
                .unwrap_or_default(),
        )
        .map(|argument| argument.fields.clone())
        .unwrap_or_default();
    let request = Request {
        record: result.clone(),
        argument,
        schema: false,
    };
    let binding = bind_check::bind_entries(
        corpus,
        &Contracts::none(),
        std::slice::from_ref(description),
        std::slice::from_ref(&request),
    )
    .into_iter()
    .next()
    .unwrap_or(Value::Null);
    let bound: HashMap<String, String> = binding["premises"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| (string(&entry["hypothesis"]), string(&entry["statement_id"])))
        .collect();
    let mut parameters = Vec::new();
    let mut hypotheses = Vec::new();
    let mut signature = Vec::new();
    for binder in description["binders"].as_array().into_iter().flatten() {
        let name = string(&binder["name"]);
        let lean_type = string(&binder["type"]);
        signature.push(format!("({name} : {lean_type})"));
        if binder["prop"] != json!(true) {
            parameters.push(Parameter { name, lean_type });
            continue;
        }
        match &binder["bundle"] {
            Value::Array(conjuncts) => {
                for (number, conjunct) in conjuncts.iter().enumerate() {
                    let name = format!("{name}.{}", number + 1);
                    hypotheses.push(Hypothesis {
                        statement_id: bound.get(&name).cloned(),
                        name,
                        head: conjunct["head"].clone(),
                        lean_type: string(&conjunct["type"]),
                    });
                }
            }
            _ => hypotheses.push(Hypothesis {
                statement_id: bound.get(&name).cloned(),
                name,
                head: binder["head"].clone(),
                lean_type,
            }),
        }
    }
    let outcome = &description["result"];
    let conclusion_failed = binding["problems"]
        .as_array()
        .into_iter()
        .flatten()
        .any(|problem| string(&problem["kind"]).starts_with("conclusion-"));
    let missing_premises = binding["problems"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|problem| problem["kind"] == "missing-premise")
        .map(|problem| string(&problem["statement_id"]))
        .collect();
    let result_type = string(&outcome["type"]);
    Elaborated {
        input_digest: digest.to_owned(),
        statement: format!(
            "theorem {} {} : {result_type}",
            string(&description["theorem"]),
            signature.join(" ")
        ),
        parameters,
        hypotheses,
        conclusion: Hypothesis {
            name: "⊢".into(),
            head: outcome["head"].clone(),
            lean_type: result_type,
            statement_id: (!conclusion_failed)
                .then(|| string(&binding["conclusion"]["statement_id"]))
                .filter(|id| !id.is_empty()),
        },
        missing_premises,
        binding: string(&binding["status"]),
        advisory: true,
    }
}

/// The cache state `context` reports in one line.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Summary {
    pub cache: String,
    pub fresh: usize,
    pub stale: usize,
    pub missing: usize,
    /// The one-line notice when some result has no fresh entry.
    pub notice: Option<String>,
}

/// Looks up every result of a pack: the summary and, per result id, its
/// elaborated view when fresh.
pub fn attach(
    root: &Path,
    corpus: &Corpus,
    result_ids: &[&str],
) -> (Summary, BTreeMap<String, Elaborated>) {
    let display = cache_path(root)
        .strip_prefix(root)
        .map_or_else(|_| cache_path(root), Path::to_owned)
        .display()
        .to_string();
    let mut summary = Summary {
        cache: display.clone(),
        fresh: 0,
        stale: 0,
        missing: 0,
        notice: None,
    };
    let mut found = BTreeMap::new();
    if result_ids.is_empty() {
        return (summary, found);
    }
    let rerun = "rerun `truth bind-check` after `lake build`; source text only";
    let cache = match load(root) {
        Ok(Some(cache)) => cache,
        Ok(None) => {
            summary.missing = result_ids.len();
            summary.notice = Some(format!(
                "elaborated types: no bind-check cache at {display} ({rerun})"
            ));
            return (summary, found);
        }
        Err(error) => {
            summary.missing = result_ids.len();
            summary.notice = Some(format!(
                "elaborated types: unreadable cache {display}: {error} ({rerun})"
            ));
            return (summary, found);
        }
    };
    let inputs = Inputs::new(root);
    let mut first_stale = None;
    for id in result_ids {
        let Some(result) = corpus.get("results", id) else {
            continue;
        };
        match cache.lookup(&inputs, &result.fields) {
            Lookup::Fresh {
                description,
                digest,
            } => {
                summary.fresh += 1;
                found.insert(
                    (*id).to_owned(),
                    elaborate(corpus, &result.fields, &description, &digest),
                );
            }
            Lookup::Stale(reason) => {
                summary.stale += 1;
                first_stale.get_or_insert(format!("{id}: {reason}"));
            }
            Lookup::Missing => summary.missing += 1,
        }
    }
    if summary.stale + summary.missing > 0 {
        let detail =
            first_stale.map_or_else(String::new, |reason| format!("; first stale {reason}"));
        summary.notice = Some(format!(
            "elaborated types: {} stale and {} missing of {} results in {display}{detail} ({rerun} for those)",
            summary.stale,
            summary.missing,
            result_ids.len()
        ));
    }
    (summary, found)
}

#[cfg(test)]
mod tests;
