//! Python `scripts/proposition_structure.py`: the derived presentation of
//! elaborated Lean expressions behind `corpus.py structure` and
//! `structure-report`.
//!
//! Rust only orchestrates: it locates the project modules, builds them with
//! Lake, runs the `scripts/PropositionStructure.lean` exporter (or reads its
//! saved output) and assembles the same reports, byte for byte, as Python.
//! The exporter's elaboration stays the authority; nothing here reimplements
//! it, and the presentation is never proof support or semantic equivalence.

use crate::{bind_check::sha256_hex, identity::legacy_uuid, pyfmt, pyjson::Ordered};
use fancy_regex::Regex;
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::OnceLock,
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

pub const SCHEMA_VERSION: i128 = 1;
/// The default `structure-report --output`.
pub const DEFAULT_OUTPUT: &str = ".cache/proposition-structure.json";
pub const CORPUS_KINDS: [&str; 8] = [
    "statements",
    "definitions",
    "disambiguations",
    "arguments",
    "results",
    "relations",
    "claims",
    "inferences",
];
const FIRST_SLICE: [&str; 8] = [
    "STMT-CAUSE-PRINCIPLE-BROAD",
    "STMT-CAUSE-PRINCIPLE-DISTINCT",
    "STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES",
    "STMT-CLASSICAL-ATTRIBUTES-SUFFICE",
    "STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE",
    "STMT-MAXIME-ENS-IS-GOD",
    "STMT-FIRST-UNMOVED-MOVER-IS-MAXIME-ENS",
    "STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT",
];
/// The declaration `structure-report` unfolds besides the slice's own.
pub const REPORT_UNFOLD: &str = "TruthCore.Case.Catholicism.ClassicalAttributesSuffice";
const NOTES: [&str; 4] = [
    "Derived presentation of elaborated Lean expressions, not proof support or semantic equivalence.",
    "Unfolding is explicit, one project declaration at a time. Named library boundaries remain named.",
    "A primitive parameter or field is intentional vocabulary; an unsupported node is an extraction limitation. Neither supplies an independent-atom semantics.",
    "Disjunction preserves alternatives and selects no branch. Structural presentation discharges no root premise.",
];
/// Inputs outside `TruthCore/` and the corpus that every report binds.
const FIXED_INPUTS: [&str; 7] = [
    "lean-toolchain",
    "lake-manifest.json",
    "scripts/PropositionStructure.lean",
    "scripts/proposition_structure.py",
    "scripts/corpus.py",
    "scripts/worker_env.py",
    "lakefile.toml",
];
const BUILD_TIMEOUT: Duration = Duration::from_secs(600);
const EXTRACT_TIMEOUT: Duration = Duration::from_secs(180);
const TIMED_OUT: &str = "structure extraction timed out; inspect the built modules and retry";

/// `FIRST_SLICE`: the statements of the explorer's structure artifact.
pub fn first_slice() -> Vec<String> {
    FIRST_SLICE
        .iter()
        .map(|legacy| legacy_uuid("statement", legacy))
        .collect()
}

/// The records of [`CORPUS_KINDS`] as Python's `load_dir` returns them:
/// path and key-ordered record, in path order.
pub struct Records(BTreeMap<&'static str, Vec<(PathBuf, Ordered)>>);

impl Records {
    /// Python `load_dir` for every kind of [`CORPUS_KINDS`].
    pub fn load(root: &Path) -> Result<Self, String> {
        let mut kinds = BTreeMap::new();
        for kind in CORPUS_KINDS {
            let mut records = Vec::new();
            for path in glob(&root.join("corpus").join(kind), ".json") {
                let relative = path
                    .strip_prefix(root)
                    .unwrap_or(&path)
                    .display()
                    .to_string();
                let text = fs::read_to_string(&path)
                    .map_err(|error| format!("{relative}: cannot read JSON: {error}"))?;
                let record = parse(&text)
                    .map_err(|error| format!("{relative}: cannot read JSON: {error}"))?;
                if !matches!(record, Ordered::Object(_)) {
                    return Err(format!(
                        "{relative}: top-level JSON value must be an object"
                    ));
                }
                records.push((path, record));
            }
            kinds.insert(kind, records);
        }
        Ok(Records(kinds))
    }

    fn of(&self, kind: &str) -> impl Iterator<Item = &Ordered> {
        self.0
            .get(kind)
            .into_iter()
            .flatten()
            .map(|(_, record)| record)
    }

    fn paths(&self) -> impl Iterator<Item = &PathBuf> {
        self.0.values().flatten().map(|(path, _)| path)
    }

    /// The `lean_declaration` of each statement in `ids` (structure-report's
    /// unfold list), in load order.
    pub fn statement_declarations(&self, ids: &[String]) -> Vec<String> {
        self.of("statements")
            .filter(|s| str_of(s, "id").is_some_and(|id| ids.iter().any(|x| x == id)))
            .filter_map(|s| str_of(s, "lean_declaration").map(str::to_owned))
            .collect()
    }
}

/// Where the exporter output comes from.
pub enum Extractor<'a> {
    /// Build the modules with Lake and run `scripts/PropositionStructure.lean`.
    Lean,
    /// A saved exporter stdout (`--extractor-json`): no Lean runs.
    Saved(&'a str),
}

/// Python `json.loads` without serde_json's 128-container nesting limit:
/// each exporter expression level nests three containers and the exporter
/// allows 100 levels. Recursion is bounded only by the stack, so callers run
/// on a thread with a large stack ([`STACK_SIZE`]).
pub fn parse(text: &str) -> Result<Ordered, String> {
    use serde::Deserialize;
    let mut deserializer = serde_json::Deserializer::from_str(text);
    deserializer.disable_recursion_limit();
    let value = Ordered::deserialize(&mut deserializer).map_err(|error| error.to_string())?;
    deserializer.end().map_err(|error| error.to_string())?;
    Ok(value)
}

/// The stack the structure commands run on: deep expression trees are
/// parsed, cloned, printed and dropped recursively.
pub const STACK_SIZE: usize = 512 * 1024 * 1024;

fn str_of<'a>(value: &'a Ordered, key: &str) -> Option<&'a str> {
    match value.get(key) {
        Some(Ordered::String(text)) => Some(text),
        _ => None,
    }
}

/// Python `str(KeyError(key))`, for a missing required key.
fn key_error(key: &str) -> String {
    pyfmt::repr_str(key)
}

fn required<'a>(value: &'a Ordered, key: &str) -> Result<&'a Ordered, String> {
    value.get(key).ok_or_else(|| key_error(key))
}

fn strings(value: Option<&Ordered>) -> Vec<&str> {
    match value {
        Some(Ordered::Array(items)) => items
            .iter()
            .filter_map(|item| match item {
                Ordered::String(text) => Some(text.as_str()),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn object(entries: Vec<(&str, Ordered)>) -> Ordered {
    Ordered::Object(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect(),
    )
}

fn string(text: impl Into<String>) -> Ordered {
    Ordered::String(text.into())
}

fn string_list<I: IntoIterator<Item = S>, S: Into<String>>(items: I) -> Ordered {
    Ordered::Array(items.into_iter().map(string).collect())
}

/// Python `dict(d, key=value)`: replaces the value in place, or appends it.
fn with_key(record: &Ordered, key: &str, value: Ordered) -> Ordered {
    let mut record = record.clone();
    if let Ordered::Object(entries) = &mut record {
        match entries.iter_mut().find(|(name, _)| name == key) {
            Some(entry) => entry.1 = value,
            None => entries.push((key.to_owned(), value)),
        }
    }
    record
}

/// Python `OSError` text: `[Errno 2] No such file or directory: '/path'`.
pub fn os_error(error: &std::io::Error, path: &Path) -> String {
    let text = error.to_string();
    let text = text
        .rsplit_once(" (os error ")
        .map_or(text.as_str(), |(head, _)| head);
    match error.raw_os_error() {
        Some(code) => format!(
            "[Errno {code}] {text}: {}",
            pyfmt::repr_str(&path.display().to_string())
        ),
        None => text.to_owned(),
    }
}

/// The entries directly in `directory` whose name ends with `suffix`
/// (pathlib `glob("*<suffix>")`), sorted as Python sorts paths.
fn glob(directory: &Path, suffix: &str) -> Vec<PathBuf> {
    let mut found: Vec<PathBuf> = fs::read_dir(directory)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|entry| {
            entry
                .file_name()
                .to_str()
                .is_some_and(|name| name.ends_with(suffix))
        })
        .map(|entry| entry.path())
        .collect();
    found.sort();
    found
}

/// pathlib `rglob("*<suffix>")` (without following directory symlinks),
/// sorted as Python sorts paths (component-wise).
fn rglob(directory: &Path, suffix: &str) -> Vec<PathBuf> {
    fn walk(directory: &Path, suffix: &str, found: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(directory).into_iter().flatten().flatten() {
            let path = entry.path();
            if entry
                .file_name()
                .to_str()
                .is_some_and(|name| name.ends_with(suffix))
            {
                found.push(path.clone());
            }
            if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
                walk(&path, suffix, found);
            }
        }
    }
    let mut found = Vec::new();
    walk(directory, suffix, &mut found);
    found.sort();
    found
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn digest(path: &Path) -> Result<String, String> {
    fs::read(path)
        .map(|bytes| sha256_hex(&bytes))
        .map_err(|error| os_error(&error, path))
}

fn read_text(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|error| os_error(&error, path))
}

fn regex(cell: &'static OnceLock<Regex>, pattern: &str) -> &'static Regex {
    cell.get_or_init(|| Regex::new(pattern).expect("valid pattern"))
}

fn capture<'t>(pattern: &Regex, text: &'t str) -> Option<&'t str> {
    pattern
        .captures(text)
        .ok()
        .flatten()
        .and_then(|found| found.get(1))
        .map(|found| found.as_str())
}

/// The declarations each project source file introduces, as Python's
/// `module_for` scanner names them; scanned once for every lookup.
pub struct Sources {
    root: PathBuf,
    files: Vec<(PathBuf, Vec<String>)>,
}

impl Sources {
    pub fn scan(root: &Path) -> Result<Self, String> {
        static NAMESPACE: OnceLock<Regex> = OnceLock::new();
        static END: OnceLock<Regex> = OnceLock::new();
        static HEADER: OnceLock<Regex> = OnceLock::new();
        let namespace = regex(&NAMESPACE, r"^namespace\s+(\S+)");
        let end = regex(&END, r"^end\s+(\S+)");
        let header = regex(
            &HEADER,
            r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|class|opaque|axiom|instance)\s+([^\s(:{\[]+)",
        );
        let mut files = Vec::new();
        for path in rglob(&root.join("TruthCore"), ".lean") {
            let text = read_text(&path)?;
            let mut names = Vec::new();
            let mut namespaces: Vec<&str> = Vec::new();
            let mut depth: usize = 0;
            for line in pyfmt::splitlines(&text) {
                let was_comment = depth > 0;
                let opened = line.matches("/-").count();
                let closed = line.matches("-/").count();
                depth = (depth + opened).saturating_sub(closed);
                if was_comment || depth > 0 {
                    continue;
                }
                let line = line.trim_matches(pyfmt::is_space);
                if let Some(name) = capture(namespace, line) {
                    namespaces.push(name);
                    continue;
                }
                if let Some(name) = capture(end, line)
                    && namespaces.last() == Some(&name)
                {
                    namespaces.pop();
                    continue;
                }
                if let Some(local) = capture(header, line) {
                    names.push(match local.strip_prefix("_root_.") {
                        Some(name) => name.to_owned(),
                        None => namespaces
                            .iter()
                            .copied()
                            .chain([local])
                            .collect::<Vec<_>>()
                            .join("."),
                    });
                }
            }
            files.push((path, names));
        }
        Ok(Sources {
            root: root.to_owned(),
            files,
        })
    }

    /// Python `module_for`: the source module of the longest declared name
    /// that is `declaration` or a prefix of it; Lean still resolves it.
    pub fn module_for(&self, declaration: &str) -> Result<String, String> {
        let mut candidates: Vec<(usize, &PathBuf)> = Vec::new();
        for (path, names) in &self.files {
            for name in names {
                if declaration == name
                    || declaration
                        .strip_prefix(name.as_str())
                        .is_some_and(|rest| rest.starts_with('.'))
                {
                    candidates.push((name.chars().count(), path));
                }
            }
        }
        let Some(best) = candidates.iter().map(|(length, _)| *length).max() else {
            return Err(format!("cannot locate project module for {declaration}"));
        };
        let paths: BTreeSet<String> = candidates
            .iter()
            .filter(|(length, _)| *length == best)
            .map(|(_, path)| path.display().to_string())
            .collect();
        if paths.len() != 1 {
            let shown: Vec<String> = paths.iter().map(|p| pyfmt::repr_str(p)).collect();
            return Err(format!(
                "ambiguous source module for {declaration}: [{}]",
                shown.join(", ")
            ));
        }
        let path = PathBuf::from(paths.into_iter().next().expect("one path"));
        let module = relative(&self.root, &path.with_extension(""));
        Ok(module.replace('/', "."))
    }
}

/// Python `project_sources`: the project modules `modules` import,
/// transitively, as source paths.
fn project_sources(root: &Path, modules: &[String]) -> Result<BTreeSet<PathBuf>, String> {
    static IMPORT: OnceLock<Regex> = OnceLock::new();
    let import = regex(&IMPORT, r"(?m)^(?:public\s+)?import\s+(\S+)");
    let mut pending: Vec<String> = modules.to_vec();
    let mut found = BTreeSet::new();
    while let Some(module) = pending.pop() {
        let path = root.join(module.replace('.', "/") + ".lean");
        if found.contains(&module) || !path.is_file() || !module.starts_with("TruthCore.") {
            continue;
        }
        let text = read_text(&path)?;
        found.insert(module);
        for captures in import.captures_iter(&text).flatten() {
            if let Some(name) = captures.get(1) {
                pending.push(name.as_str().to_owned());
            }
        }
    }
    Ok(found
        .iter()
        .map(|module| root.join(module.replace('.', "/") + ".lean"))
        .collect())
}

/// Python `input_manifest`: every project Lean source, the imported
/// modules, the fixed tool inputs and the loaded corpus records, hashed.
fn input_manifest(
    root: &Path,
    modules: &[String],
    records: &Records,
) -> Result<Vec<(String, String)>, String> {
    let mut paths: BTreeSet<PathBuf> = rglob(&root.join("TruthCore"), ".lean")
        .into_iter()
        .collect();
    paths.extend(project_sources(root, modules)?);
    paths.extend(FIXED_INPUTS.iter().map(|path| root.join(path)));
    paths.extend(records.paths().cloned());
    paths
        .into_iter()
        .filter(|path| path.is_file())
        .map(|path| Ok((relative(root, &path), digest(&path)?)))
        .collect()
}

fn manifest_value(manifest: &[(String, String)]) -> Ordered {
    Ordered::Array(
        manifest
            .iter()
            .map(|(path, sha)| object(vec![("path", string(path)), ("sha256", string(sha))]))
            .collect(),
    )
}

/// Python `json.dumps(value, sort_keys=True)` (ASCII, default separators).
fn dumps_sorted(value: &Ordered, out: &mut String) {
    match value {
        Ordered::String(text) => out.push_str(&pyfmt::json_str(text, true)),
        Ordered::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                dumps_sorted(item, out);
            }
            out.push(']');
        }
        Ordered::Object(entries) => {
            let mut entries: Vec<&(String, Ordered)> = entries.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            out.push('{');
            for (index, (key, item)) in entries.into_iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&pyfmt::json_str(key, true));
                out.push_str(": ");
                dumps_sorted(item, out);
            }
            out.push('}');
        }
        scalar => out.push_str(&scalar.dumps(None)),
    }
}

/// The `input_digest`: sha256 of the sorted-key JSON of request and inputs.
fn input_digest(request: &Ordered, inputs: &Ordered) -> String {
    let mut text = String::new();
    dumps_sorted(
        &object(vec![
            ("request", request.clone()),
            ("inputs", inputs.clone()),
        ]),
        &mut text,
    );
    sha256_hex(text.as_bytes())
}

/// Python `repr()` of a JSON-loaded value, for a message.
fn repr(value: &Ordered) -> String {
    match value {
        Ordered::Null => "None".into(),
        Ordered::Bool(true) => "True".into(),
        Ordered::Bool(false) => "False".into(),
        Ordered::String(text) => pyfmt::repr_str(text),
        Ordered::Float(number) if number.is_nan() => "nan".into(),
        Ordered::Float(number) if number.is_infinite() => {
            if *number > 0.0 { "inf" } else { "-inf" }.into()
        }
        Ordered::Array(items) => format!(
            "[{}]",
            items.iter().map(repr).collect::<Vec<_>>().join(", ")
        ),
        Ordered::Object(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, item)| format!("{}: {}", pyfmt::repr_str(key), repr(item)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        scalar => scalar.dumps(None),
    }
}

/// A finished subprocess: exit success, stdout and stderr.
struct Finished {
    success: bool,
    stdout: String,
    stderr: String,
}

/// Runs `program args` in `root`, killing it after `timeout`
/// (`subprocess.run(..., timeout=...)`); `Ok(None)` on a timeout.
fn run_bounded(
    root: &Path,
    program: &str,
    args: &[String],
    timeout: Duration,
) -> Result<Option<Finished>, String> {
    let mut child = Command::new(program)
        .args(args)
        .current_dir(root)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| os_error(&error, Path::new(program)))?;
    let pipe = |mut reader: Box<dyn Read + Send>| {
        thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = reader.read_to_end(&mut bytes);
            String::from_utf8_lossy(&bytes).into_owned()
        })
    };
    let stdout = pipe(Box::new(child.stdout.take().expect("piped stdout")));
    let stderr = pipe(Box::new(child.stderr.take().expect("piped stderr")));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|error| error.to_string())? {
            break Some(status);
        }
        if start.elapsed() >= timeout {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        thread::sleep(Duration::from_millis(50));
    };
    let stdout = stdout.join().unwrap_or_default();
    let stderr = stderr.join().unwrap_or_default();
    Ok(status.map(|status| Finished {
        success: status.success(),
        stdout,
        stderr,
    }))
}

fn detail(finished: &Finished) -> &str {
    let stderr = finished.stderr.trim_matches(pyfmt::is_space);
    if stderr.is_empty() {
        finished.stdout.trim_matches(pyfmt::is_space)
    } else {
        stderr
    }
}

/// Python `run_extractor`, with `Ok(None)` for a timeout: Lake builds the
/// modules (it owns freshness), then the exporter describes the request.
fn run_extractor(
    root: &Path,
    request: &Ordered,
    extractor: &Extractor,
) -> Result<Option<Vec<Ordered>>, String> {
    let stdout = match extractor {
        Extractor::Saved(text) => text.to_string(),
        Extractor::Lean => {
            let modules: Vec<String> = strings(request.get("modules"))
                .into_iter()
                .map(str::to_owned)
                .collect();
            let worker = |tail: Vec<String>| -> Vec<String> {
                ["scripts/worker_env.py", "--", "lake"]
                    .iter()
                    .map(|part| part.to_string())
                    .chain(tail)
                    .collect()
            };
            let build = worker(["build".to_owned()].into_iter().chain(modules).collect());
            let Some(built) = run_bounded(root, "python3", &build, BUILD_TIMEOUT)? else {
                return Ok(None);
            };
            if !built.success {
                return Err(format!("structure module build failed: {}", detail(&built)));
            }
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0, |elapsed| elapsed.as_nanos());
            let input = std::env::temp_dir().join(format!(
                "truth-structure-{}-{nanos}.json",
                std::process::id()
            ));
            fs::write(&input, request.dumps(None)).map_err(|error| os_error(&error, &input))?;
            let run = worker(vec![
                "env".into(),
                "lean".into(),
                "--run".into(),
                "scripts/PropositionStructure.lean".into(),
                input.display().to_string(),
            ]);
            let completed = run_bounded(root, "python3", &run, EXTRACT_TIMEOUT);
            let _ = fs::remove_file(&input);
            let Some(completed) = completed? else {
                return Ok(None);
            };
            if !completed.success {
                return Err(format!(
                    "structure extraction failed: {}",
                    detail(&completed)
                ));
            }
            completed.stdout
        }
    };
    let output = parse(&stdout).map_err(|_| {
        format!(
            "structure extractor returned invalid JSON: {}",
            pyfmt::head(&stdout, 500)
        )
    })?;
    let valid = match &output {
        Ordered::Array(rows) => rows.iter().all(|row| {
            matches!(row, Ordered::Object(_))
                && row.get("declaration").is_some()
                && row.get("error").is_none()
        }),
        _ => false,
    };
    match output {
        Ordered::Array(rows) if valid => Ok(Some(rows)),
        output => Err(format!(
            "structure extractor returned invalid declarations: {}",
            repr(&output)
        )),
    }
}

/// Python `nodes`: every expression node (an object with `id` and `kind`),
/// in pre-order.
fn nodes<'a>(value: &'a Ordered, found: &mut Vec<&'a Ordered>) {
    match value {
        Ordered::Object(entries) => {
            if value.get("id").is_some() && value.get("kind").is_some() {
                found.push(value);
            }
            for (_, child) in entries {
                nodes(child, found);
            }
        }
        Ordered::Array(items) => {
            for child in items {
                nodes(child, found);
            }
        }
        _ => {}
    }
}

/// Scopes every node `id` and `binding` with `prefix`.
fn scope_nodes(value: &mut Ordered, prefix: &str) {
    match value {
        Ordered::Object(entries) => {
            let is_node = entries.iter().any(|(key, _)| key == "id")
                && entries.iter().any(|(key, _)| key == "kind");
            for (key, child) in entries.iter_mut() {
                match child {
                    Ordered::String(text)
                        if is_node && (key == "id" || (key == "binding" && !text.is_empty())) =>
                    {
                        *text = format!("{prefix}{text}");
                    }
                    _ => scope_nodes(child, prefix),
                }
            }
        }
        Ordered::Array(items) => items
            .iter_mut()
            .for_each(|child| scope_nodes(child, prefix)),
        _ => {}
    }
}

/// Python `semantic_links`: the linked or referenced definitions and their
/// disambiguations, each with the expression nodes that name it.
fn semantic_links(
    statement: &Ordered,
    declarations: &Ordered,
    definitions: &[&Ordered],
    disambiguations: &[&Ordered],
) -> Result<(Vec<Ordered>, Vec<Ordered>), String> {
    let mut expression_nodes = Vec::new();
    nodes(declarations, &mut expression_nodes);
    let names: BTreeSet<&str> = expression_nodes
        .iter()
        .filter_map(|node| str_of(node, "declaration").filter(|name| !name.is_empty()))
        .collect();
    let linked = strings(statement.get("definition_ids"));
    let mut chosen = Vec::new();
    for definition in definitions {
        let id = required(definition, "id")?;
        let declaration = str_of(definition, "lean_declaration");
        let listed = matches!(id, Ordered::String(id) if linked.contains(&id.as_str()));
        if !listed && !declaration.is_some_and(|name| names.contains(name)) {
            continue;
        }
        let ids: Vec<String> = match declaration.filter(|name| !name.is_empty()) {
            Some(name) => expression_nodes
                .iter()
                .filter(|node| str_of(node, "declaration") == Some(name))
                .filter_map(|node| str_of(node, "id").map(str::to_owned))
                .collect(),
            None => Vec::new(),
        };
        chosen.push(with_key(definition, "expression_ids", string_list(ids)));
    }
    let chosen_ids: Vec<&str> = chosen.iter().filter_map(|d| str_of(d, "id")).collect();
    let linked = strings(statement.get("disambiguation_ids"));
    let mut senses = Vec::new();
    for disambiguation in disambiguations {
        let id = required(disambiguation, "id")?;
        let sense_ids = strings(disambiguation.get("sense_definition_ids"));
        let listed = matches!(id, Ordered::String(id) if linked.contains(&id.as_str()));
        if !listed && !sense_ids.iter().any(|sense| chosen_ids.contains(sense)) {
            continue;
        }
        let ids: BTreeSet<&str> = chosen
            .iter()
            .filter(|d| str_of(d, "id").is_some_and(|id| sense_ids.contains(&id)))
            .flat_map(|d| strings(d.get("expression_ids")))
            .collect();
        senses.push(with_key(disambiguation, "expression_ids", string_list(ids)));
    }
    Ok((chosen, senses))
}

/// Python `build_reports`: the structure artifact for `statement_ids`,
/// unfolding exactly the project definitions in `unfold`. `closed` is the
/// frontier's `closed_statements`.
pub fn build_reports(
    root: &Path,
    records: &Records,
    statement_ids: &[String],
    unfold: &[String],
    closed: &Map<String, Value>,
    extractor: &Extractor,
) -> Result<Ordered, String> {
    let mut statements: Vec<&Ordered> = Vec::new();
    let mut statement_index: HashMap<&str, usize> = HashMap::new();
    for record in records.of("statements") {
        let id = match required(record, "id")? {
            Ordered::String(id) => id.as_str(),
            _ => continue,
        };
        match statement_index.get(id) {
            Some(&index) => statements[index] = record,
            None => {
                statement_index.insert(id, statements.len());
                statements.push(record);
            }
        }
    }
    let definitions: Vec<&Ordered> = records.of("definitions").collect();
    let mut selected = Vec::new();
    for sid in statement_ids {
        let Some(&index) = statement_index.get(sid.as_str()) else {
            return Err(format!("unknown statement: {sid}"));
        };
        let statement = statements[index];
        if !truthy(statement.get("lean_declaration")) {
            return Err(format!(
                "{sid} has no Lean declaration; extraction unavailable (binding remains authoritative)"
            ));
        }
        selected.push((sid.as_str(), statement));
    }
    let requested: BTreeSet<String> = unfold.iter().cloned().collect();
    let mut names: BTreeSet<String> = selected
        .iter()
        .filter_map(|(_, s)| str_of(s, "lean_declaration").map(str::to_owned))
        .collect();
    names.extend(requested.iter().cloned());
    let linked: BTreeSet<&str> = selected
        .iter()
        .flat_map(|(_, s)| strings(s.get("definition_ids")))
        .collect();
    for definition in &definitions {
        if str_of(definition, "id").is_some_and(|id| linked.contains(id))
            && let Some(name) = str_of(definition, "lean_declaration")
            && name.starts_with("TruthCore.")
        {
            names.insert(name.to_owned());
        }
    }
    if requested.iter().any(|name| !name.starts_with("TruthCore.")) {
        return Err("only project-owned TruthCore definitions may be unfolded".into());
    }
    let sources = Sources::scan(root)?;
    let modules: Vec<String> = names
        .iter()
        .map(|name| sources.module_for(name))
        .collect::<Result<BTreeSet<_>, _>>()?
        .into_iter()
        .collect();
    let request = object(vec![
        ("modules", string_list(modules.iter().cloned())),
        ("declarations", string_list(names.iter().cloned())),
        ("unfold", string_list(requested.iter().cloned())),
    ]);
    let manifest = input_manifest(root, &modules, records)?;
    let inputs = manifest_value(&manifest);
    let request_hash = input_digest(&request, &inputs);
    let Some(raw) = run_extractor(root, &request, extractor)? else {
        return Err(TIMED_OUT.into());
    };
    // Refuse a report if inputs were edited while Lean was running.
    if manifest != input_manifest(root, &modules, records)? {
        return Err("structure inputs changed during extraction; retry".into());
    }
    let head = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(root)
        .output()
        .map_err(|error| os_error(&error, Path::new("git")))?;
    if !head.status.success() {
        return Err(format!(
            "Command '['git', 'rev-parse', 'HEAD']' returned non-zero exit status {}.",
            head.status.code().unwrap_or(-1)
        ));
    }
    let head = String::from_utf8_lossy(&head.stdout)
        .trim_matches(pyfmt::is_space)
        .to_owned();
    let mut built = Vec::new();
    for module in &modules {
        let path = root
            .join(".lake/build/lib/lean")
            .join(module.replace('.', "/") + ".olean");
        if path.is_file() {
            built.push((relative(root, &path), digest(&path)?));
        }
    }
    let built = manifest_value(&built);
    let arguments: Vec<&Ordered> = records.of("arguments").collect();
    let results: Vec<&Ordered> = records.of("results").collect();
    let disambiguations: Vec<&Ordered> = records.of("disambiguations").collect();
    let mut reports = Vec::new();
    for (sid, statement) in selected {
        let root_name = str_of(statement, "lean_declaration").unwrap_or_default();
        let Some(root_description) = raw
            .iter()
            .find(|row| str_of(row, "declaration") == Some(root_name))
        else {
            return Err(format!(
                "extractor omitted requested declaration {root_name}"
            ));
        };
        let own = strings(statement.get("definition_ids"));
        let linked_names: BTreeSet<&str> = definitions
            .iter()
            .filter(|d| str_of(d, "id").is_some_and(|id| own.contains(&id)))
            .filter_map(|d| str_of(d, "lean_declaration"))
            .collect();
        let mut described = Vec::new();
        nodes(root_description, &mut described);
        let mut referenced: BTreeSet<&str> = described
            .iter()
            .filter_map(|node| str_of(node, "declaration"))
            .collect();
        if let Some(Ordered::Array(references)) = root_description.get("references") {
            referenced.extend(references.iter().filter_map(|r| str_of(r, "declaration")));
        }
        let mut chosen = vec![root_description.clone()];
        chosen.extend(
            raw.iter()
                .filter(|row| {
                    str_of(row, "declaration").is_some_and(|name| {
                        name != root_name
                            && (linked_names.contains(name) || referenced.contains(name))
                    })
                })
                .cloned(),
        );
        let mut scoped = Ordered::Array(chosen);
        let prefix = format!("{sid}@{}:", &request_hash[..16]);
        scope_nodes(&mut scoped, &prefix);
        let related_args: Vec<&Ordered> = arguments
            .iter()
            .copied()
            .filter(|a| {
                strings(a.get("premise_statement_ids")).contains(&sid)
                    || str_of(a, "conclusion_statement_id") == Some(sid)
            })
            .collect();
        let argument_ids: BTreeSet<&str> = related_args
            .iter()
            .filter_map(|a| str_of(a, "id"))
            .collect();
        let (linked_definitions, linked_senses) =
            semantic_links(statement, &scoped, &definitions, &disambiguations)?;
        let related_names: BTreeSet<&str> = linked_definitions
            .iter()
            .filter_map(|d| str_of(d, "lean_declaration").filter(|name| !name.is_empty()))
            .collect();
        let mut related = Vec::new();
        for s in &statements {
            let Some(declaration) = str_of(s, "lean_declaration") else {
                continue;
            };
            if !related_names.contains(declaration) {
                continue;
            }
            let id = str_of(s, "id").unwrap_or_default();
            let status = closed
                .get(id)
                .and_then(|value| serde_json::from_value::<Ordered>(value.clone()).ok())
                .unwrap_or_else(|| string("open"));
            related.push(object(vec![
                ("statement_id", string(id)),
                ("lean_declaration", string(declaration)),
                ("paraphrase", required(s, "paraphrase")?.clone()),
                ("frontier_status", status),
            ]));
        }
        let mut supporting = Vec::new();
        for result in &results {
            match required(result, "argument_id")? {
                Ordered::String(id) if argument_ids.contains(id.as_str()) => {
                    supporting.push((*result).clone())
                }
                _ => {}
            }
        }
        reports.push(object(vec![
            ("statement_id", string(sid)),
            ("lean_declaration", string(root_name)),
            (
                "revision",
                object(vec![
                    ("head", string(&head)),
                    ("input_digest", string(&request_hash)),
                    ("inputs", inputs.clone()),
                    ("request", request.clone()),
                    ("built_inputs", built.clone()),
                ]),
            ),
            ("declarations", scoped),
            (
                "semantic_links",
                object(vec![
                    ("definitions", Ordered::Array(linked_definitions)),
                    ("disambiguations", Ordered::Array(linked_senses)),
                ]),
            ),
            (
                "support",
                object(vec![
                    (
                        "arguments",
                        Ordered::Array(related_args.into_iter().cloned().collect()),
                    ),
                    ("results", Ordered::Array(supporting)),
                    ("related_statements", Ordered::Array(related)),
                ]),
            ),
            ("coverage_notes", string_list(NOTES)),
        ]));
    }
    Ok(object(vec![
        ("schema_version", Ordered::Int(SCHEMA_VERSION)),
        ("reports", Ordered::Array(reports)),
    ]))
}

/// Python `bool(value)` for a JSON value.
fn truthy(value: Option<&Ordered>) -> bool {
    match value {
        None | Some(Ordered::Null) | Some(Ordered::Bool(false)) => false,
        Some(Ordered::Int(number)) => *number != 0,
        Some(Ordered::Float(number)) => *number != 0.0,
        Some(Ordered::String(text)) => !text.is_empty(),
        Some(Ordered::Array(items)) => !items.is_empty(),
        Some(Ordered::Object(entries)) => !entries.is_empty(),
        Some(Ordered::Bool(true)) => true,
    }
}

fn inventory(paths: Vec<PathBuf>, root: &Path) -> BTreeSet<String> {
    paths.iter().map(|path| relative(root, path)).collect()
}

/// Python `check_artifact`: the artifact's recorded inputs (inventories,
/// file hashes and digest) still match the checkout. No Lean runs.
pub fn check_artifact(root: &Path, artifact: &Ordered) -> Result<(), String> {
    let schema = match artifact.get("schema_version") {
        Some(Ordered::Int(number)) => *number == SCHEMA_VERSION,
        Some(Ordered::Float(number)) => *number == SCHEMA_VERSION as f64,
        Some(Ordered::Bool(value)) => *value,
        _ => false,
    };
    if !schema || !truthy(artifact.get("reports")) {
        return Err("invalid structure artifact schema".into());
    }
    let Some(Ordered::Array(reports)) = artifact.get("reports") else {
        return Err("invalid structure artifact schema".into());
    };
    for report in reports {
        let revision = required(report, "revision")?;
        let inputs = required(revision, "inputs")?;
        let items: Vec<&Ordered> = match inputs {
            Ordered::Array(items) => items.iter().collect(),
            _ => Vec::new(),
        };
        let mut paths = Vec::new();
        for item in &items {
            match required(item, "path")? {
                Ordered::String(path) => paths.push(path.as_str()),
                _ => return Err("invalid structure artifact input path".into()),
            }
        }
        let saved_corpus: BTreeSet<String> = paths
            .iter()
            .filter(|path| path.starts_with("corpus/"))
            .map(|path| path.to_string())
            .collect();
        if !saved_corpus.is_empty() {
            let current = CORPUS_KINDS
                .iter()
                .flat_map(|kind| glob(&root.join("corpus").join(kind), ".json"))
                .collect();
            if saved_corpus != inventory(current, root) {
                return Err("stale structure artifact corpus inventory".into());
            }
        }
        let saved_lean: BTreeSet<String> = paths
            .iter()
            .filter(|path| path.starts_with("TruthCore/") && path.ends_with(".lean"))
            .map(|path| path.to_string())
            .collect();
        if !saved_lean.is_empty()
            && saved_lean != inventory(rglob(&root.join("TruthCore"), ".lean"), root)
        {
            return Err("stale structure artifact Lean source inventory".into());
        }
        for (item, path) in items.iter().zip(&paths) {
            let file = root.join(path);
            let current = if file.is_file() {
                fs::read(&file).ok().map(|bytes| sha256_hex(&bytes))
            } else {
                None
            };
            let saved = required(item, "sha256")?;
            if !matches!((current, saved), (Some(sha), Ordered::String(saved)) if &sha == saved) {
                return Err(format!("stale structure artifact input: {path}"));
            }
        }
        let request = required(revision, "request")?;
        let expected = input_digest(request, inputs);
        if !matches!(required(revision, "input_digest")?, Ordered::String(saved) if *saved == expected)
        {
            return Err("invalid structure artifact input digest".into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp(name: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "truth-structure-{name}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos())
        ));
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn longest_module_prefix_supports_structure_fields() {
        let root = temp("prefix");
        fs::create_dir_all(root.join("TruthCore/Case")).unwrap();
        fs::write(
            root.join("TruthCore/Case/Root.lean"),
            "namespace TruthCore.Case.Root\n/- def Hidden -/\nstructure S where\n  p : Prop\nend TruthCore.Case.Root",
        )
        .unwrap();
        let sources = Sources::scan(&root).unwrap();
        assert_eq!(
            sources.module_for("TruthCore.Case.Root.S.p").unwrap(),
            "TruthCore.Case.Root"
        );
        assert!(sources.module_for("TruthCore.Case.Root.Hidden").is_err());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn digest_binds_sources_but_not_head() {
        let root = temp("digest");
        fs::write(root.join("source.lean"), "P a b").unwrap();
        let inputs = Ordered::parse(&format!(
            r#"[{{"path": "source.lean", "sha256": "{}"}}]"#,
            sha256_hex(b"P a b")
        ))
        .unwrap();
        let request = Ordered::parse(r#"{"declarations": ["TruthCore.P"]}"#).unwrap();
        // Python: hashlib.sha256(json.dumps({...}, sort_keys=True).encode())
        let digest = input_digest(&request, &inputs);
        let artifact = object(vec![
            ("schema_version", Ordered::Int(1)),
            (
                "reports",
                Ordered::Array(vec![object(vec![(
                    "revision",
                    object(vec![
                        ("head", string("other")),
                        ("inputs", inputs),
                        ("request", request),
                        ("input_digest", string(&digest)),
                    ]),
                )])]),
            ),
        ]);
        check_artifact(&root, &artifact).unwrap();
        fs::write(root.join("source.lean"), "P b a").unwrap();
        assert_eq!(
            check_artifact(&root, &artifact).unwrap_err(),
            "stale structure artifact input: source.lean"
        );
        fs::remove_dir_all(&root).unwrap();
        for bad in [r#"{}"#, r#"{"schema_version": 1, "reports": []}"#] {
            assert_eq!(
                check_artifact(Path::new("."), &Ordered::parse(bad).unwrap()).unwrap_err(),
                "invalid structure artifact schema"
            );
        }
    }

    #[test]
    fn semantic_links_are_not_formula_replacements() {
        let expression = Ordered::parse(
            r#"[{"type": {"id": "root", "kind": "application", "declaration": "TruthCore.P", "children": [
                {"role": "argument.0", "node": {"id": "arg", "kind": "variable", "text": "x", "binding": "binder"}}]}}]"#,
        )
        .unwrap();
        let definitions: Vec<Ordered> = [
            r#"{"id": "DEF-P", "lean_declaration": "TruthCore.P", "definition": "P"}"#,
            r#"{"id": "DEF-Q", "lean_declaration": "TruthCore.Q"}"#,
            r#"{"id": "DEF-NO-LEAN"}"#,
        ]
        .iter()
        .map(|text| Ordered::parse(text).unwrap())
        .collect();
        let senses =
            [
                Ordered::parse(r#"{"id": "DISAMB-P", "sense_definition_ids": ["DEF-P", "DEF-Q"]}"#)
                    .unwrap(),
            ];
        let (defs, disambs) = semantic_links(
            &Ordered::Object(vec![]),
            &expression,
            &definitions.iter().collect::<Vec<_>>(),
            &senses.iter().collect::<Vec<_>>(),
        )
        .unwrap();
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].get("expression_ids"), Some(&string_list(["root"])));
        assert_eq!(disambs.len(), 1);
        let mut found = Vec::new();
        nodes(&expression, &mut found);
        let ids: Vec<_> = found.iter().filter_map(|n| str_of(n, "id")).collect();
        assert_eq!(ids, ["root", "arg"]);
        let mut scoped = expression.clone();
        scope_nodes(&mut scoped, "S@x:");
        assert!(scoped.dumps(None).contains(r#""binding": "S@x:binder""#));
    }

    #[test]
    fn deep_exporter_trees_parse_beyond_serde_default_depth() {
        // 400 expression levels, three containers each: far beyond 128.
        let mut tree = String::from(r#"{"id": "leaf", "kind": "sort", "children": []}"#);
        for level in 0..400 {
            tree = format!(
                r#"{{"id": "n{level}", "kind": "app", "children": [{{"role": "arg", "node": {tree}}}]}}"#
            );
        }
        let text = format!(r#"[{{"declaration": "TruthCore.Deep", "type": {tree}}}]"#);
        assert!(
            Ordered::parse(&text).is_err(),
            "serde default limit applies"
        );
        let check = std::thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let rows = run_extractor(Path::new("."), &Ordered::Null, &Extractor::Saved(&text))
                    .unwrap()
                    .unwrap();
                let mut found = Vec::new();
                nodes(&rows[0], &mut found);
                assert_eq!(found.len(), 401);
                assert_eq!(parse(&rows[0].dumps(None)).unwrap(), rows[0]);
            })
            .unwrap();
        check.join().unwrap();
    }

    #[test]
    fn python_reprs_and_sorted_dumps() {
        let value =
            Ordered::parse(r#"[{"declaration": "X", "error": "boom", "n": null, "t": true}]"#)
                .unwrap();
        assert_eq!(
            repr(&value),
            "[{'declaration': 'X', 'error': 'boom', 'n': None, 't': True}]"
        );
        let mut text = String::new();
        dumps_sorted(
            &Ordered::parse(r#"{"b": "é", "a": [1, 2.5]}"#).unwrap(),
            &mut text,
        );
        assert_eq!(text, "{\"a\": [1, 2.5], \"b\": \"\\u00e9\"}");
    }
}
