//! The verified configuration explorer bundle (#954 slice A6): Python
//! `scripts/configuration_explorer.py`.
//!
//! [`write_bundle`] writes the disposable `.cache` bundle byte for byte as
//! Python's `json.dump(..., ensure_ascii=False, sort_keys=True, indent=2)`
//! does, plus `producer.producer_sha256`, the fingerprint of the truth crate
//! that produced it (`build.rs`, as the structure report records). It lies
//! outside the input manifest and digest; [`read_bundle`] requires it to match
//! the running binary after Python's freshness checks, so a Rust change makes
//! old bundles stale. Freshness binds a trusted producer's output to the
//! current inputs; it does not execute Lean again.

use crate::{
    configuration_live,
    configurations::{self, Context, model_profile_mismatches, order_key, str_of, strs},
    pyjson::Ordered,
    sha256::sha256_hex,
    structure::{PRODUCER_SHA256, os_error},
    subprocess,
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};

type Obj = Map<String, Value>;

pub const SCHEMA_VERSION: i64 = 1;
/// Bound exhaustive transport generation to at most 2,048 syntactic
/// selections (Python `MAX_DIMENSIONS`).
pub const MAX_DIMENSIONS: usize = 11;
pub const PRODUCER_TRUST: &str = "Output of the trusted verification producer. Digest validation checks freshness, not fresh proof execution.";
/// The only bundle path a certified build reads.
pub const CACHE_PATH: &str = ".cache/configuration-explorer.json";

const INPUT_FILES: [&str; 16] = [
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "TruthCore.lean",
    "scripts/corpus.py",
    "scripts/configurations.py",
    "scripts/configuration_explorer.py",
    "scripts/finite_models.py",
    "scripts/premise_dossiers.py",
    "scripts/source_evidence.py",
    "scripts/BindTypes.lean",
    "scripts/verify-result.sh",
    "scripts/verifier-pins.env",
    "scripts/bootstrap-verifier.sh",
    "verifier/Cargo.toml",
    "verifier/Cargo.lock",
];
/// `(directory, pattern)`: `*.suffix` or an exact file name (pathlib
/// `rglob`).
const INPUT_DIRECTORIES: [(&str, &str); 8] = [
    ("TruthCore", "*.lean"),
    ("results", "comparator.json"),
    ("verifier/src", "*.rs"),
    ("corpus/statements", "*.json"),
    ("corpus/arguments", "*.json"),
    ("corpus/results", "*.json"),
    ("corpus/models", "*.json"),
    ("corpus/configurations", "*.json"),
];

/// The input files and their SHA-256, keyed by POSIX path relative to root.
pub type Manifest = BTreeMap<String, String>;

fn rglob(directory: &Path, pattern: &str, found: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).into_iter().flatten().flatten() {
        let path = entry.path();
        let matches =
            entry
                .file_name()
                .to_str()
                .is_some_and(|name| match pattern.strip_prefix('*') {
                    Some(suffix) => name.ends_with(suffix),
                    None => name == pattern,
                });
        if matches {
            found.push(path.clone());
        }
        if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
            rglob(&path, pattern, found);
        }
    }
}

/// Python `input_manifest(root)`: the existing global transcription scan and
/// the exact configuration inputs; docs and CSS are excluded.
pub fn input_manifest(root: &Path) -> Result<Manifest, String> {
    let mut paths: Vec<PathBuf> = INPUT_FILES.iter().map(|path| root.join(path)).collect();
    for (directory, pattern) in INPUT_DIRECTORIES {
        rglob(&root.join(directory), pattern, &mut paths);
    }
    // Python sorts paths component-wise.
    paths.sort_by(|a, b| a.components().cmp(b.components()));
    paths.dedup();
    let mut manifest = Manifest::new();
    for path in paths {
        let relative = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .components()
            .map(|part| part.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let symlink = fs::symlink_metadata(&path).is_ok_and(|meta| meta.file_type().is_symlink());
        if symlink || !path.is_file() {
            return Err(format!(
                "configuration report input is missing or a symlink: {relative}"
            ));
        }
        let bytes = fs::read(&path).map_err(|error| os_error(&error, &path))?;
        manifest.insert(relative, sha256_hex(&bytes));
    }
    Ok(manifest)
}

/// Python `input_digest(manifest)`: SHA-256 of the compact sorted JSON.
pub fn input_digest(manifest: &Manifest) -> String {
    let body = manifest
        .iter()
        .map(|(path, digest)| {
            format!(
                "{}:{}",
                crate::pyfmt::json_str(path, true),
                crate::pyfmt::json_str(digest, true)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    sha256_hex(format!("{{{body}}}").as_bytes())
}

/// Python `source_head(root)`: `git rev-parse HEAD`.
pub fn source_head(root: &Path) -> Result<String, String> {
    let mut command = Command::new("git");
    command.args(["rev-parse", "HEAD"]).current_dir(root);
    match subprocess::run_bounded(command, Duration::from_secs(10)) {
        Ok(Some(done)) if done.success => {
            Ok(done.stdout.trim_matches(crate::pyfmt::is_space).to_owned())
        }
        Ok(Some(done)) => Err(format!(
            "cannot resolve producer source head: {}",
            done.stderr.trim_matches(crate::pyfmt::is_space)
        )),
        Ok(None) => Err(
            "cannot resolve producer source head: Command '['git', 'rev-parse', 'HEAD']' timed out after 10 seconds"
                .into(),
        ),
        Err(subprocess::Failure::Spawn(error) | subprocess::Failure::Wait(error)) => Err(format!(
            "cannot resolve producer source head: {}",
            os_error(&error, Path::new("git"))
        )),
    }
}

/// Python `bounded_family(case, classify)`: a decision tree over the
/// profile's assumptions that prunes whole families with cores and shared
/// witnesses. Counts concern syntactic selections.
pub fn bounded_family(
    case: &Obj,
    context: &Context,
    classify: &mut dyn FnMut(&[&str]) -> Result<Value, String>,
) -> Result<Value, String> {
    let mut dimensions: Vec<&str> = case
        .get("semantics")
        .and_then(|semantics| semantics.get("applications"))
        .and_then(Value::as_object)
        .map(|applications| applications.keys().map(String::as_str).collect())
        .unwrap_or_default();
    // Ordered by legacy id, else uuid (corpus_ids.order_key).
    dimensions.sort_by_key(|sid| order_key(sid, context.statements.get(sid).copied()));
    if dimensions.len() > MAX_DIMENSIONS {
        return Err(format!(
            "{}: explorer supports at most {MAX_DIMENSIONS} assumption dimensions",
            str_of(case, "id")
        ));
    }
    struct Walk<'c, 'v> {
        dimensions: &'c [&'v str],
        nodes: Vec<Value>,
        memo: HashMap<Vec<&'v str>, Value>,
        classify: &'c mut dyn FnMut(&[&str]) -> Result<Value, String>,
    }
    impl<'v> Walk<'_, 'v> {
        fn report(&mut self, ids: &[&'v str]) -> Result<Value, String> {
            let mut key = ids.to_vec();
            key.sort_unstable();
            if let Some(found) = self.memo.get(&key) {
                return Ok(found.clone());
            }
            let report = (self.classify)(&key)?;
            self.memo.insert(key, report.clone());
            Ok(report)
        }

        fn visit(&mut self, selected: Vec<&'v str>, index: usize) -> Result<String, String> {
            let remaining = &self.dimensions[index..];
            let prefix = self.report(&selected)?;
            let mut all = selected.clone();
            all.extend_from_slice(remaining);
            let full = self.report(&all)?;
            let empty = |value: &Value| !crate::pyfmt::truthy(Some(value));
            let terminal = if prefix["status"] == "verified incompatible" {
                Some(prefix)
            } else if full["status"] == "model witnessed" {
                // This one certified assignment covers every member of the family.
                Some(full)
            } else if empty(&prefix["model_ids"])
                && full["status"] == "unresolved"
                && empty(&full["core_composition"]["truncated"])
            {
                // No registered model covers the prefix, so none covers a
                // superset; a complete supplied-rule closure has no core even
                // at the extension.
                Some(prefix)
            } else if remaining.is_empty() {
                Some(prefix)
            } else {
                None
            };
            let identifier = format!("n{}", self.nodes.len());
            let position = self.nodes.len();
            self.nodes.push(json!({"id": identifier}));
            let node = match terminal {
                Some(report) => json!({
                    "id": identifier, "kind": "terminal", "required_statement_ids": selected,
                    "optional_statement_ids": remaining, "report": report,
                    "syntactic_selections_covered": 1u64 << remaining.len(),
                }),
                None => {
                    let exclude = self.visit(selected.clone(), index + 1)?;
                    let mut with = selected.clone();
                    with.push(remaining[0]);
                    let include = self.visit(with, index + 1)?;
                    json!({"id": identifier, "kind": "decision", "statement_id": remaining[0],
                           "exclude": exclude, "include": include})
                }
            };
            self.nodes[position] = node;
            Ok(identifier)
        }
    }
    let mut walk = Walk {
        dimensions: &dimensions,
        nodes: Vec::new(),
        memo: HashMap::new(),
        classify,
    };
    let root = walk.visit(Vec::new(), 0)?;
    let terminals: Vec<&Value> = walk
        .nodes
        .iter()
        .filter(|node| node["kind"] == "terminal")
        .collect();
    let covered: u64 = terminals
        .iter()
        .map(|node| node["syntactic_selections_covered"].as_u64().unwrap_or(0))
        .sum();
    let limits = json!({
        "classifier_calls": walk.memo.len(),
        "decision_nodes": walk.nodes.len() - terminals.len(),
        "terminal_families": terminals.len(),
        "syntactic_selections": 1u64 << dimensions.len(),
        "covered_selections": covered,
        "note": "Counts describe bounded syntactic assumption selections, not philosophically distinct theories. Incomplete implication/core closure remains explicit in terminal reports.",
    });
    Ok(json!({
        "statement_ids": dimensions, "max_dimensions": MAX_DIMENSIONS, "root": root,
        "nodes": walk.nodes, "limits": limits,
    }))
}

/// Python `build_case_spaces(context, reports, root=)`: each freshly verified
/// report with its assumption space and verified implications; with `root`
/// the family cores are replayed in Lean (`family_verification`).
pub fn build_case_spaces(
    context: &Context,
    reports: &[Value],
    root: Option<&Path>,
) -> Result<Vec<Value>, String> {
    let by_id: HashMap<&str, &Value> = reports
        .iter()
        .map(|report| (report["id"].as_str().unwrap_or_default(), report))
        .collect();
    let mut cases = Vec::new();
    for case in &context.cases {
        let Some(report) = by_id.get(str_of(case, "id")) else {
            return Err(format!("KeyError: {}", str_of(case, "id")));
        };
        if report["verified"] != true || !report["verification"].is_object() {
            return Err(
                "registered or unverified data cannot produce a certified explorer bundle".into(),
            );
        }
        let mut classify = |ids: &[&str]| -> Result<Value, String> {
            let mut report = configurations::configuration_report(
                case,
                &context.results,
                &context.arguments,
                &context.models,
                true,
                Some(("selection", ids.to_vec())),
            )?;
            Ok(report["configurations"][0].take())
        };
        let space = bounded_family(case, context, &mut classify)?;
        let verification = match root {
            Some(root) => {
                let terminals: Vec<Value> = space["nodes"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter(|node| node["kind"] == "terminal")
                    .map(|node| node["report"].clone())
                    .collect();
                configuration_live::verify_compositions(
                    root,
                    case,
                    &json!({"configurations": terminals}),
                    context,
                )?
            }
            None => Value::Null,
        };
        let mut implications = strs(case, "implication_result_ids");
        implications.sort_unstable();
        let implications: Vec<Value> = implications
            .into_iter()
            .map(|rid| {
                let result = context.results.get(rid).copied();
                let argument = result
                    .and_then(|result| context.arguments.get(str_of(result, "argument_id")))
                    .copied();
                json!({
                    "result_id": rid,
                    "theorem": result.and_then(|result| result.get("theorem")),
                    "premise_statement_ids": argument.and_then(|argument| argument.get("premise_statement_ids")),
                    "conclusion_statement_id": argument.and_then(|argument| argument.get("conclusion_statement_id")),
                })
            })
            .collect();
        let mut entry = (*report).clone();
        entry["assumption_space"] = space;
        entry["verified_implications"] = Value::Array(implications);
        entry["family_verification"] = verification;
        cases.push(entry);
    }
    Ok(cases)
}

/// `value` as Python's `json.dump(value, ensure_ascii=False, sort_keys=True,
/// indent=2)` writes it (serde_json maps are sorted by key already).
pub fn dumps(value: &Value) -> String {
    fn ordered(value: &Value) -> Ordered {
        match value {
            Value::Null => Ordered::Null,
            Value::Bool(value) => Ordered::Bool(*value),
            Value::Number(number) => match number.as_i64() {
                Some(int) => Ordered::Int(int.into()),
                None => match number.as_u64() {
                    Some(int) => Ordered::Int(int.into()),
                    None => Ordered::Float(number.as_f64().unwrap_or(f64::NAN)),
                },
            },
            Value::String(text) => Ordered::String(text.clone()),
            Value::Array(items) => Ordered::Array(items.iter().map(ordered).collect()),
            Value::Object(map) => Ordered::Object(
                map.iter()
                    .map(|(key, value)| (key.clone(), ordered(value)))
                    .collect(),
            ),
        }
    }
    ordered(value).dumps(Some(2))
}

pub use crate::strength::resolve;

fn is_symlink(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_symlink())
}

/// The output path [`write_bundle`] accepts: no symlink and inside the
/// clone's `.cache` directory. Checked before any Lean runs.
pub fn output_path(root: &Path, output: &Path) -> Result<PathBuf, String> {
    if is_symlink(output) || is_symlink(&root.join(".cache")) {
        return Err("configuration output/cache symlinks are unsupported".into());
    }
    let output = resolve(output);
    if !output.starts_with(resolve(&root.join(".cache"))) {
        return Err("configuration report output must be inside the clone .cache directory".into());
    }
    Ok(output)
}

/// Python `write_bundle`: replays the family cores, requires unchanged
/// inputs and atomically replaces one ignored output file. `output` comes
/// from [`output_path`].
pub fn write_bundle(
    root: &Path,
    output: &Path,
    context: &Context,
    reports: &[Value],
    initial: &Manifest,
) -> Result<Value, String> {
    let cases = build_case_spaces(context, reports, Some(root))?;
    let manifest = input_manifest(root)?;
    if &manifest != initial {
        return Err(
            "configuration inputs changed during report verification; discard and rerun".into(),
        );
    }
    let bundle = json!({
        "schema_version": SCHEMA_VERSION,
        "producer": {"mode": "live-verified", "source_head": source_head(root)?,
                     "input_digest": input_digest(&manifest), "inputs": manifest,
                     "trust": PRODUCER_TRUST, "producer_sha256": PRODUCER_SHA256},
        "cases": cases,
    });
    let parent = output.parent().unwrap_or(root);
    fs::create_dir_all(parent).map_err(|error| os_error(&error, parent))?;
    let temporary = parent.join(format!(
        ".{}.{}.tmp",
        output
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default(),
        std::process::id()
    ));
    let written =
        fs::write(&temporary, dumps(&bundle) + "\n").and_then(|()| fs::rename(&temporary, output));
    if let Err(error) = written {
        let _ = fs::remove_file(&temporary);
        return Err(os_error(&error, output));
    }
    Ok(bundle)
}

/// Python `read_bundle`, then the producer fingerprint: validates trusted
/// output freshness and its canonical projection. This is NOT a fresh proof
/// gate.
pub fn read_bundle(root: &Path, path: &Path, context: &Context) -> Result<Value, String> {
    if is_symlink(path) || is_symlink(&root.join(".cache")) {
        return Err("configuration report/cache symlinks are unsupported".into());
    }
    let text = fs::read_to_string(path).map_err(|error| {
        format!(
            "cannot read configuration report: {}",
            os_error(&error, path)
        )
    })?;
    let bundle: Value = serde_json::from_str(&text)
        .map_err(|error| format!("cannot read configuration report: {error}"))?;
    let schema = bundle.get("schema_version");
    if !bundle.is_object()
        || !schema.is_some_and(|value| value.is_i64() || value.is_u64())
        || schema != Some(&json!(SCHEMA_VERSION))
    {
        return Err("unsupported configuration report schema".into());
    }
    let producer = &bundle["producer"];
    if !producer.is_object()
        || producer["mode"] != "live-verified"
        || producer["trust"] != PRODUCER_TRUST
    {
        return Err("configuration report lacks a live-verification producer".into());
    }
    let manifest = input_manifest(root)?;
    let head = source_head(root)?;
    if producer["source_head"] != head.as_str()
        || producer["inputs"] != json!(manifest)
        || producer["input_digest"] != input_digest(&manifest).as_str()
    {
        return Err(
            "stale configuration report: source head or current input digest differs".into(),
        );
    }
    let reports = match bundle.get("cases") {
        Some(Value::Array(reports)) if reports.len() == context.cases.len() => reports,
        _ => return Err("configuration report does not cover the exact current cases".into()),
    };
    let mut expected_reports = Vec::new();
    for (case, report) in context.cases.iter().zip(reports) {
        if !report.is_object() || report["verified"] != true {
            return Err("malformed configuration report case".into());
        }
        let expected = configurations::configuration_report(
            case,
            &context.results,
            &context.arguments,
            &context.models,
            true,
            None,
        )?;
        for (key, value) in expected.as_object().into_iter().flatten() {
            if report.get(key).unwrap_or(&Value::Null) != value {
                return Err(format!(
                    "{}: configuration projection disagrees with current inputs",
                    str_of(case, "id")
                ));
            }
        }
        let verification = &report["verification"];
        let mut chosen = strs(case, "incompatibility_result_ids");
        chosen.extend(strs(case, "implication_result_ids"));
        chosen.sort_unstable();
        chosen.dedup();
        let chosen = json!(chosen);
        if !verification.is_object()
            || verification["result_ids"] != chosen
            || verification["original_bound_result_ids"] != chosen
        {
            return Err(format!(
                "{}: missing exact original theorem verification provenance",
                str_of(case, "id")
            ));
        }
        let eligible: Vec<&Obj> = case
            .get("model_bindings")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_object)
            .filter(|entry| model_profile_mismatches(case, entry, &context.models).is_empty())
            .filter_map(|entry| context.models.get(str_of(entry, "model_id")).copied())
            .collect();
        let count =
            |model: &Obj, key: &str| model.get(key).and_then(Value::as_array).map_or(0, Vec::len);
        let certificates: usize = eligible
            .iter()
            .map(|model| 1 + count(model, "carriers") + count(model, "evaluations"))
            .sum();
        let model_gate =
            json!({"models": eligible.len(), "certificates": certificates, "axioms": []});
        let cores: usize = expected["configurations"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| entry["incompatible_cores"].as_array().map_or(0, Vec::len))
            .sum();
        if verification["models"] != model_gate
            || verification["compositions"] != json!({"cores": cores})
        {
            return Err(format!(
                "{}: missing exact model/composition verification provenance",
                str_of(case, "id")
            ));
        }
        let mut expected = expected;
        expected["verification"] = verification.clone();
        expected_reports.push(expected);
    }
    let spaces = build_case_spaces(context, &expected_reports, None)?;
    for (actual, expected) in reports.iter().zip(&spaces) {
        if actual["verified_implications"] != expected["verified_implications"] {
            return Err("conditional theorem provenance disagrees with current inputs".into());
        }
        if actual["assumption_space"] != expected["assumption_space"] {
            return Err("configuration decision tree disagrees with canonical projection".into());
        }
        let cores: usize = expected["assumption_space"]["nodes"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|node| node["kind"] == "terminal")
            .map(|node| {
                node["report"]["incompatible_cores"]
                    .as_array()
                    .map_or(0, Vec::len)
            })
            .sum();
        if actual["family_verification"] != json!({"cores": cores}) {
            return Err("missing exact family-core verification provenance".into());
        }
    }
    // After Python's checks, so a shared failure reports the same message.
    match &producer["producer_sha256"] {
        Value::String(saved) if saved == PRODUCER_SHA256 => {}
        Value::String(_) => {
            return Err("stale configuration report producer: truth sources changed".into());
        }
        _ => return Err("configuration report lacks producer provenance".into()),
    }
    Ok(bundle)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn output_must_stay_inside_cache_after_normalization() {
        let root = std::env::temp_dir().join(format!("truth-config-cache-{}", std::process::id()));
        fs::create_dir_all(root.join(".cache")).unwrap();
        let inside = output_path(&root, &root.join(".cache/new/report.json")).unwrap();
        assert!(inside.ends_with(".cache/new/report.json"));
        for escaping in [
            ".cache/new/../../victim.txt",
            ".cache/../victim.txt",
            ".cache/a/b/../../../x",
        ] {
            assert_eq!(
                output_path(&root, &root.join(escaping)).unwrap_err(),
                "configuration report output must be inside the clone .cache directory",
                "{escaping}"
            );
        }
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn digest_is_compact_sorted_json() {
        let mut manifest = Manifest::new();
        manifest.insert("b".into(), "2".into());
        manifest.insert("a".into(), "1".into());
        assert_eq!(input_digest(&manifest), sha256_hex(br#"{"a":"1","b":"2"}"#));
    }

    #[test]
    fn dumps_matches_python_indent() {
        let value = json!({"b": [], "a": {"x": [1, "é"], "y": {}}, "c": null});
        assert_eq!(
            dumps(&value),
            "{\n  \"a\": {\n    \"x\": [\n      1,\n      \"é\"\n    ],\n    \"y\": {}\n  },\n  \"b\": [],\n  \"c\": null\n}"
        );
    }
}
