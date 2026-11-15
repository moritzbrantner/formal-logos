//! Golden snapshots of the Python oracle (#954 slice R1), replayed against
//! the Rust CLI alone: no `corpus.py`, no Lean.
//!
//! `scripts/truth_parity/record_goldens.py` writes
//! `tests/golden/<module>/<test>.json` from the Python side of each fixture
//! parity comparison (format and normalizations: `scripts/truth_parity/golden.py`).
//! Each case is a fixture checkout (files, optionally a Git history),
//! directories outside it, a `truth` command line and the output Python
//! gave; this test rebuilds the checkout in a temporary directory, runs the
//! binary and compares. Covering a new parity module is one `golden!` line
//! below; `every_golden_directory_is_replayed` fails until it is added.

use serde_json::{Map, Value};
use std::{
    collections::BTreeMap,
    env, fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
};

const BINARY: &str = env!("CARGO_BIN_EXE_truth");
const PRODUCER: &str = truth::structure::PRODUCER_SHA256;
/// Fixed identity and dates for the replayed fixture commits.
const GIT_ENV: [(&str, &str); 7] = [
    ("GIT_AUTHOR_NAME", "golden"),
    ("GIT_AUTHOR_EMAIL", "golden@example.invalid"),
    ("GIT_COMMITTER_NAME", "golden"),
    ("GIT_COMMITTER_EMAIL", "golden@example.invalid"),
    ("GIT_AUTHOR_DATE", "2026-01-01T00:00:00Z"),
    ("GIT_COMMITTER_DATE", "2026-01-01T00:00:00Z"),
    ("GIT_CONFIG_NOSYSTEM", "1"),
];

macro_rules! golden {
    ($($module:ident),* $(,)?) => {
        const MODULES: &[&str] = &[$(stringify!($module)),*];
        $(#[test]
        fn $module() {
            replay_module(stringify!($module));
        })*
    };
}

golden!(
    attribution,
    bind_check,
    bridge_experiments,
    check,
    configuration_report,
    configurations,
    frontier,
    index,
    issues,
    navigation,
    proof_use,
    proposition_structure,
    research,
    revisions,
    senses,
    strength,
    thickness,
);

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn golden_root() -> PathBuf {
    manifest().join("tests").join("golden")
}

fn repository() -> PathBuf {
    manifest().parent().expect("repository root").to_path_buf()
}

#[test]
fn every_golden_directory_is_replayed() {
    let mut directories: Vec<String> = fs::read_dir(golden_root())
        .expect("tests/golden")
        .map(|entry| entry.expect("entry"))
        .filter(|entry| entry.path().is_dir())
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect();
    directories.sort();
    let mut known: Vec<String> = MODULES.iter().map(|name| (*name).to_owned()).collect();
    known.sort();
    assert_eq!(
        directories, known,
        "add a golden!(...) entry for each tests/golden/<module>"
    );
}

fn replay_module(module: &str) {
    let directory = golden_root().join(module);
    let mut files: Vec<PathBuf> = fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .map(|entry| entry.expect("entry").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "json")
        })
        .collect();
    files.sort();
    assert!(
        !files.is_empty(),
        "no golden files in {}",
        directory.display()
    );
    let mut failures = Vec::new();
    let mut count = 0;
    for file in files {
        let text = fs::read_to_string(&file).expect("golden file");
        let document: Value = serde_json::from_str(&text).expect("golden JSON");
        let base = document["base"].as_object().expect("base tree");
        let shared = document["shared"].as_array().cloned().unwrap_or_default();
        for case in document["cases"].as_array().expect("cases") {
            let case = &resolve_shared(case, &shared);
            count += 1;
            let title = format!(
                "{}/{} [{}] truth {}",
                module,
                file.file_stem().unwrap().to_string_lossy(),
                case["name"].as_str().unwrap_or(""),
                strings(&case["args"]).join(" ")
            );
            if let Err(message) = replay(base, case) {
                failures.push(format!("{title}\n{message}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {count} golden cases differ:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

/// The case with its `{"shared": N}` Git history and externals expanded.
fn resolve_shared(case: &Value, shared: &[Value]) -> Value {
    let expand = |value: &Value| match value.get("shared").and_then(Value::as_u64) {
        Some(index) => shared[index as usize].clone(),
        None => value.clone(),
    };
    let mut case = case.clone();
    if let Some(git) = case.get("git").map(expand) {
        case["git"] = git;
    }
    if let Some(externals) = case["externals"]
        .as_array()
        .map(|items| items.iter().map(expand).collect())
    {
        case["externals"] = Value::Array(externals);
    }
    case
}

fn strings(value: &Value) -> Vec<String> {
    value
        .as_array()
        .map(|items| {
            items
                .iter()
                .map(|item| item.as_str().expect("string").to_owned())
                .collect()
        })
        .unwrap_or_default()
}

/// A temporary directory removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = env::temp_dir().join(format!(
            "truth-golden-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::SeqCst)
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("scratch directory");
        Self(fs::canonicalize(&path).expect("canonical scratch"))
    }
}

impl Drop for Scratch {
    /// `TRUTH_GOLDEN_KEEP=1` keeps the replayed checkouts for inspection.
    fn drop(&mut self) {
        if env::var_os("TRUTH_GOLDEN_KEEP").is_none() {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
}

/// The `⟪root⟫`, `⟪ext:N⟫`, `⟪commit:N⟫` and `⟪producer⟫` substitutions.
struct Tokens(Vec<(String, String)>);

impl Tokens {
    fn apply(&self, text: &str) -> String {
        let mut text = text.to_owned();
        for (token, value) in &self.0 {
            if text.contains(token.as_str()) {
                text = text.replace(token.as_str(), value);
            }
        }
        text
    }

    fn value(&self, value: &Value) -> Value {
        match value {
            Value::String(text) => Value::String(self.apply(text)),
            Value::Array(items) => {
                Value::Array(items.iter().map(|item| self.value(item)).collect())
            }
            Value::Object(entries) => Value::Object(
                entries
                    .iter()
                    .map(|(key, item)| (self.apply(key), self.value(item)))
                    .collect(),
            ),
            other => other.clone(),
        }
    }
}

type Tree = BTreeMap<String, String>;

/// A symbolic link entry's content: the target behind this marker.
const SYMLINK: &str = "\u{0}symlink:";

/// A file entry's content: the text, a repository file it references or a
/// symbolic link (`SYMLINK` and its target).
fn content(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        Value::Object(entry) if entry.contains_key("symlink") => {
            format!(
                "{SYMLINK}{}",
                entry["symlink"].as_str().expect("symlink target")
            )
        }
        Value::Object(entry) => {
            let path = entry["repo"].as_str().expect("repo reference");
            fs::read_to_string(repository().join(path))
                .unwrap_or_else(|error| panic!("referenced repository file {path}: {error}"))
        }
        other => panic!("unexpected file entry {other}"),
    }
}

fn overlay(tree: &mut Tree, changes: &Map<String, Value>) {
    for (path, value) in changes {
        if value.is_null() {
            tree.remove(path);
        } else {
            tree.insert(path.clone(), content(value));
        }
    }
}

fn write_tree(
    directory: &Path,
    tree: &Tree,
    executable: &[String],
    empty: &[String],
    tokens: &Tokens,
) {
    for (path, text) in tree {
        let target = directory.join(path);
        fs::create_dir_all(target.parent().expect("parent")).expect("directory");
        if let Some(link) = text.strip_prefix(SYMLINK) {
            #[cfg(unix)]
            std::os::unix::fs::symlink(tokens.apply(link), &target).expect("fixture symlink");
            #[cfg(not(unix))]
            panic!("golden symlinks need a Unix host: {link}");
        } else {
            fs::write(&target, tokens.apply(text)).expect("fixture file");
        }
    }
    for path in empty {
        fs::create_dir_all(directory.join(path)).expect("empty directory");
    }
    #[cfg(unix)]
    for path in executable {
        use std::os::unix::fs::PermissionsExt;
        let target = directory.join(path);
        fs::set_permissions(&target, fs::Permissions::from_mode(0o755)).expect("executable bit");
    }
}

fn entries(value: &Value) -> Tree {
    let mut tree = Tree::new();
    if let Some(files) = value["files"].as_object() {
        overlay(&mut tree, files);
    }
    tree
}

fn git(root: &Path, args: &[&str], extra: &[(&str, &str)], input: Option<&str>) -> String {
    let mut command = Command::new("git");
    command
        .arg("-C")
        .arg(root)
        .args(args)
        .envs(GIT_ENV)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .envs(extra.iter().copied())
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().expect("git");
    if let Some(input) = input {
        child
            .stdin
            .take()
            .expect("stdin")
            .write_all(input.as_bytes())
            .expect("git stdin");
    }
    let output = child.wait_with_output().expect("git output");
    assert!(
        output.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("git output")
        .trim()
        .to_owned()
}

/// Rebuilds the recorded history in `root` and returns the commit ids in
/// recorded order.
fn replay_history(root: &Path, scratch: &Path, history: &Value) -> Vec<String> {
    git(root, &["init", "-q"], &[], None);
    let index = scratch.join("golden-index");
    let index = index.to_str().expect("UTF-8 path");
    let mut trees: Vec<Tree> = Vec::new();
    let mut ids: Vec<String> = Vec::new();
    let none = Tokens(Vec::new());
    for commit in history["commits"].as_array().expect("commits") {
        let parents: Vec<usize> = commit["parents"]
            .as_array()
            .expect("parents")
            .iter()
            .map(|parent| parent.as_u64().expect("parent") as usize)
            .collect();
        let mut tree = parents
            .first()
            .map(|parent| trees[*parent].clone())
            .unwrap_or_default();
        overlay(&mut tree, commit["overlay"].as_object().expect("overlay"));
        let stage = scratch.join(format!("golden-stage-{}", trees.len()));
        fs::create_dir_all(&stage).expect("stage");
        write_tree(&stage, &tree, &strings(&commit["executable"]), &[], &none);
        let environment = [("GIT_INDEX_FILE", index)];
        let _ = fs::remove_file(index);
        let git_dir = format!("--git-dir={}", root.join(".git").display());
        git(
            &stage,
            &[&git_dir, "--work-tree=.", "add", "-A", "--force", "."],
            &environment,
            None,
        );
        let tree_id = git(root, &["write-tree"], &environment, None);
        let mut args = vec!["commit-tree".to_owned(), tree_id];
        for parent in &parents {
            args.push("-p".into());
            args.push(ids[*parent].clone());
        }
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let message = commit["message"].as_str().unwrap_or("golden");
        ids.push(git(root, &args, &[], Some(message)));
        trees.push(tree);
        fs::remove_dir_all(&stage).expect("stage cleanup");
    }
    let _ = fs::remove_file(index);
    for (name, commit) in history["refs"].as_object().expect("refs") {
        let commit = &ids[commit.as_u64().expect("ref target") as usize];
        git(root, &["update-ref", name, commit], &[], None);
    }
    match &history["head"] {
        Value::String(reference) => {
            git(root, &["symbolic-ref", "HEAD", reference], &[], None);
        }
        Value::Object(detached) => {
            let commit = &ids[detached["detached"].as_u64().expect("detached head") as usize];
            git(
                root,
                &["update-ref", "--no-deref", "HEAD", commit],
                &[],
                None,
            );
        }
        other => panic!("unexpected HEAD {other}"),
    }
    if !ids.is_empty() {
        git(root, &["read-tree", "HEAD"], &[], None);
    }
    ids
}

fn replay(base: &Map<String, Value>, case: &Value) -> Result<(), String> {
    let scratch = Scratch::new();
    let root = scratch.0.join("root");
    fs::create_dir_all(&root).expect("root");
    let externals = case["externals"].as_array().expect("externals");
    let mut pairs = vec![("⟪root⟫".to_owned(), root.display().to_string())];
    let mut external_dirs = Vec::new();
    for (number, _) in externals.iter().enumerate() {
        let directory = scratch.0.join(format!("ext{number}"));
        fs::create_dir_all(&directory).expect("external directory");
        pairs.push((format!("⟪ext:{number}⟫"), directory.display().to_string()));
        external_dirs.push(directory);
    }
    pairs.push(("⟪producer⟫".to_owned(), PRODUCER.to_owned()));
    if case["git"].is_object() {
        let ids = replay_history(&root, &scratch.0, &case["git"]);
        for (number, id) in ids.iter().enumerate() {
            pairs.push((format!("⟪commit:{number}⟫"), id.clone()));
        }
    }
    // Longest token first, so `⟪commit:1⟫` never rewrites part of `⟪commit:10⟫`.
    pairs.sort_by_key(|pair| std::cmp::Reverse(pair.0.len()));
    let tokens = Tokens(pairs);

    let mut tree = Tree::new();
    overlay(&mut tree, base);
    overlay(
        &mut tree,
        case["tree"]["overlay"].as_object().expect("tree overlay"),
    );
    write_tree(
        &root,
        &tree,
        &strings(&case["tree"]["executable"]),
        &strings(&case["tree"]["empty"]),
        &tokens,
    );
    for (directory, external) in external_dirs.iter().zip(externals) {
        write_tree(
            directory,
            &entries(external),
            &strings(&external["executable"]),
            &strings(&external["empty"]),
            &tokens,
        );
    }

    let args: Vec<String> = strings(&case["args"])
        .iter()
        .map(|arg| tokens.apply(arg))
        .collect();
    let cwd = case["cwd"]
        .as_str()
        .map(|cwd| PathBuf::from(tokens.apply(cwd)))
        .unwrap_or_else(|| root.clone());
    let mut command = Command::new(BINARY);
    command.args(&args).current_dir(&cwd).stdin(Stdio::null());
    if let Some(variables) = case["env"].as_object() {
        for (key, value) in variables {
            command.env(key, tokens.apply(value.as_str().expect("env value")));
        }
    }
    let prepend = strings(&case["path_prepend"]);
    if !prepend.is_empty() {
        let mut paths: Vec<PathBuf> = prepend
            .iter()
            .map(|path| PathBuf::from(tokens.apply(path)))
            .collect();
        paths.extend(env::split_paths(&env::var_os("PATH").unwrap_or_default()));
        command.env("PATH", env::join_paths(paths).expect("PATH"));
    }
    let output = command.output().expect("run truth");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    compare(
        &case["expect"],
        &tokens,
        output.status.code(),
        &stdout,
        &stderr,
    )
}

fn strip_producer(text: &str) -> String {
    const FIELD: &str = "\"producer_sha256\": \"";
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find(FIELD) {
        let after = &rest[start + FIELD.len()..];
        let digest = after.get(..64).filter(|digest| {
            digest
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        });
        match digest.and_then(|_| after[64..].strip_prefix("\",")) {
            Some(tail) => {
                out.push_str(&rest[..start]);
                rest = tail.trim_start();
            }
            None => {
                out.push_str(&rest[..start + FIELD.len()]);
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
}

/// The Rust-only additions a parity test removes from Rust's stdout before
/// comparing it with Python's (`scripts/truth_parity/common.py`).
fn normalize(name: &str, stdout: &str) -> String {
    const NOTE_BLOCK: &str = "\n\nNotes mentioning the target records (";
    const BIND_TYPES_NOTICE: &str = "  elaborated types: no bind-check cache at ";
    let json_key = match name {
        "note_mentions" => "note_mentions",
        "bind_types" => "bind_types",
        "mentioned_by_notes" => "mentioned_by_notes",
        "note_hits" => "",
        other => panic!("unknown golden normalization {other}"),
    };
    if let Ok(mut value) = serde_json::from_str::<Value>(stdout) {
        // Re-serialized only when something was removed, so byte-exact
        // expectations of untouched JSON output keep their formatting.
        let changed = match &mut value {
            Value::Object(entries) if !json_key.is_empty() => entries.remove(json_key).is_some(),
            Value::Array(items) if name == "note_hits" => {
                let before = items.len();
                items.retain(|item| item["kind"] != "note");
                items.len() != before
            }
            _ => false,
        };
        return if changed {
            value.to_string()
        } else {
            stdout.to_owned()
        };
    }
    match name {
        "note_mentions" => match stdout.rfind(NOTE_BLOCK) {
            Some(cut) => format!("{}\n", &stdout[..cut]),
            None => stdout.to_owned(),
        },
        "bind_types" => stdout
            .split_inclusive('\n')
            .filter(|line| !line.starts_with(BIND_TYPES_NOTICE))
            .collect(),
        _ => stdout.to_owned(),
    }
}

fn text_difference(label: &str, expected: &str, actual: &str) -> String {
    let expected_lines: Vec<&str> = expected.split_inclusive('\n').collect();
    let actual_lines: Vec<&str> = actual.split_inclusive('\n').collect();
    let line = expected_lines
        .iter()
        .zip(&actual_lines)
        .position(|(left, right)| left != right)
        .unwrap_or(expected_lines.len().min(actual_lines.len()));
    format!(
        "  {label} differs at line {}:\n    expected: {:?}\n    actual:   {:?}",
        line + 1,
        expected_lines.get(line).copied().unwrap_or("<end>"),
        actual_lines.get(line).copied().unwrap_or("<end>")
    )
}

fn path<'a>(value: &'a Value, dotted: &str) -> Option<&'a Value> {
    dotted
        .split('.')
        .try_fold(value, |current, key| current.get(key))
}

fn compare(
    expect: &Value,
    tokens: &Tokens,
    code: Option<i32>,
    stdout: &str,
    stderr: &str,
) -> Result<(), String> {
    let mut problems = Vec::new();
    let wanted = expect["code"].as_i64().map(|code| code as i32);
    if code != wanted {
        problems.push(format!(
            "  exit code: expected {wanted:?}, actual {code:?}; stderr: {stderr:?}"
        ));
    }
    let mut stdout = if expect["strip_producer"].as_bool() == Some(true) {
        strip_producer(stdout)
    } else {
        stdout.to_owned()
    };
    for name in strings(&expect["normalize"]) {
        stdout = normalize(&name, &stdout);
    }
    for (label, actual) in [("stdout", stdout.as_str()), ("stderr", stderr)] {
        if let Some(expected) = expect[label].as_str() {
            let expected = tokens.apply(expected);
            if expected != actual {
                problems.push(text_difference(label, &expected, actual));
            }
        }
    }
    let parsed = || serde_json::from_str::<Value>(&stdout);
    if let Some(expected) = expect.get("stdout_json") {
        match parsed() {
            Ok(mut actual) => {
                if let Value::Object(entries) = &mut actual {
                    for key in strings(&expect["ignore_keys"]) {
                        entries.remove(&key);
                    }
                }
                let expected = tokens.value(expected);
                if actual != expected {
                    problems.push(format!(
                        "  stdout JSON differs:\n    expected: {}\n    actual:   {}",
                        truncate(&expected.to_string()),
                        truncate(&actual.to_string())
                    ));
                }
            }
            Err(error) => problems.push(format!("  stdout is not JSON ({error}): {stdout:?}")),
        }
    }
    if let Some(paths) = expect["json_paths"].as_object() {
        match parsed() {
            Ok(actual) => {
                for (dotted, expected) in paths {
                    let expected = tokens.value(expected);
                    if path(&actual, dotted) != Some(&expected) {
                        problems.push(format!(
                            "  {dotted}: expected {expected}, actual {:?}",
                            path(&actual, dotted)
                        ));
                    }
                }
            }
            Err(error) => problems.push(format!("  stdout is not JSON ({error}): {stdout:?}")),
        }
    }
    if let Some(expected) = expect["error_message"].as_str() {
        let actual = serde_json::from_str::<Value>(stderr)
            .ok()
            .and_then(|value| value["error"]["message"].as_str().map(str::to_owned));
        if actual.as_deref() != Some(tokens.apply(expected).as_str()) {
            problems.push(format!(
                "  error message: expected {expected:?}, actual {actual:?}"
            ));
        }
    }
    if let Some(files) = expect["files"].as_object() {
        for (relative, expected) in files {
            let target = PathBuf::from(tokens.apply(relative));
            let mut actual = fs::read_to_string(&target).unwrap_or_default();
            if expect["strip_producer"].as_bool() == Some(true) {
                actual = strip_producer(&actual);
            }
            let expected = tokens.apply(expected.as_str().expect("file content"));
            if actual != expected {
                problems.push(text_difference(relative, &expected, &actual));
            }
        }
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

fn truncate(text: &str) -> String {
    const LIMIT: usize = 2000;
    if text.len() <= LIMIT {
        text.to_owned()
    } else {
        let mut end = LIMIT;
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        format!("{}…", &text[..end])
    }
}
