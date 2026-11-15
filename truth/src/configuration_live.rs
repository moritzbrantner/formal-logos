//! Live configuration verification (#954 slice A6): Python
//! `configurations.verify_case`, `verify_compositions` and the live part of
//! `corpus.py collect_configuration_reports`.
//!
//! Lean stays the verifier. This module writes the same certificate and
//! composition sources as Python, runs `lake build`, `lake env lean` and
//! `scripts/verify-result.sh` (each process tree bounded by Python's
//! timeout) and reads only their exit status and `#print axioms` lines; the
//! original theorems bind through `scripts/BindTypes.lean`
//! ([`bind_check::bind_originals`]). No verdict is computed here.

use crate::{
    Corpus, bind_check,
    configurations::{self, Context, Index, model_profile_mismatches, str_of, strs},
    pyfmt::{self, repr},
    structure::os_error,
    subprocess::{self, Failure},
};
use fancy_regex::Regex;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeSet, HashMap},
    fs,
    path::Path,
    process::Command,
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

type Obj = Map<String, Value>;

/// `verify_case`'s `subprocess.run(..., timeout=1200)`.
const CASE_TIMEOUT: Duration = Duration::from_secs(1200);
/// `verify_compositions`' `subprocess.run(..., timeout=600)`.
const COMPOSITION_TIMEOUT: Duration = Duration::from_secs(600);

/// One finished program run or Python's exception text for it.
enum Ran {
    Done(subprocess::Finished),
    /// `OSError` or `TimeoutExpired` text.
    Unavailable(String),
}

/// Runs `argv` in `root` (Python `subprocess.run(argv, cwd=root,
/// capture_output=True, timeout=…)`). A relative program with a slash
/// (`scripts/verify-result.sh`) runs from `root`, as Python's does.
fn run(root: &Path, argv: &[String], timeout: Duration) -> Ran {
    let program = if argv[0].contains('/') {
        root.join(&argv[0])
    } else {
        argv[0].clone().into()
    };
    let mut command = Command::new(&program);
    command.args(&argv[1..]).current_dir(root);
    match subprocess::run_bounded(command, timeout) {
        Ok(Some(done)) => Ran::Done(done),
        Ok(None) => Ran::Unavailable(timed_out(argv, timeout)),
        Err(Failure::Spawn(error)) => Ran::Unavailable(os_error(&error, Path::new(&argv[0]))),
        Err(Failure::Wait(error)) => Ran::Unavailable(error.to_string()),
    }
}

/// Python `str(subprocess.TimeoutExpired(argv, timeout))`.
fn timed_out(argv: &[String], timeout: Duration) -> String {
    format!(
        "Command '{}' timed out after {} seconds",
        list_repr(argv),
        timeout.as_secs()
    )
}

/// Python `repr` of a list of strings.
fn list_repr(items: &[String]) -> String {
    repr(&json!(items))
}

/// A temporary `.lean` file in `root` (Python `NamedTemporaryFile(...,
/// suffix='.lean', dir=root)`), removed when dropped.
struct Scratch(std::path::PathBuf);

impl Scratch {
    fn write(root: &Path, source: &str) -> Result<Self, String> {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = root.join(format!(
            ".truth-configuration-{}-{}.lean",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::write(&path, source).map_err(|error| os_error(&error, &path))?;
        Ok(Self(path))
    }

    fn name(&self) -> String {
        self.0.display().to_string()
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn object(value: Option<&Value>) -> Option<&Obj> {
    value.and_then(Value::as_object)
}

fn semantics(case: &Obj) -> &Obj {
    static EMPTY: OnceLock<Obj> = OnceLock::new();
    object(case.get("semantics")).unwrap_or_else(|| EMPTY.get_or_init(Obj::new))
}

fn constant<'v>(profile: &'v Obj, role: &'v str) -> &'v str {
    object(profile.get("constants"))
        .and_then(|constants| constants.get(role))
        .and_then(Value::as_str)
        .unwrap_or(role)
}

/// Python `application(profile, statements, sid)`.
fn application(profile: &Obj, statements: &Index, sid: &str) -> String {
    let roles = object(profile.get("applications"))
        .map(|applications| strs(applications, sid))
        .unwrap_or_default();
    let args: Vec<&str> = roles.iter().map(|role| constant(profile, role)).collect();
    let declaration = statements
        .get(sid)
        .map(|statement| str_of(statement, "lean_declaration"))
        .unwrap_or_default();
    format!("(@{declaration} {})", args.join(" "))
}

/// The profile's parameters: `(name, type)` in order.
fn parameters(profile: &Obj) -> Vec<(&str, &str)> {
    profile
        .get("parameters")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_object)
        .map(|parameter| (str_of(parameter, "name"), str_of(parameter, "type")))
        .collect()
}

/// `' '.join(f'({name} : {type})')`, the variable names and the role
/// arguments in `parameter_order` (default: the parameter order).
fn binders(profile: &Obj) -> (String, Vec<&str>, String) {
    let parameters = parameters(profile);
    let declared = parameters
        .iter()
        .map(|(name, kind)| format!("({name} : {kind})"))
        .collect::<Vec<_>>()
        .join(" ");
    let names: Vec<&str> = parameters.iter().map(|(name, _)| *name).collect();
    let order = if profile.contains_key("parameter_order") {
        strs(profile, "parameter_order")
    } else {
        names.clone()
    };
    let roles = order
        .iter()
        .map(|role| constant(profile, role))
        .collect::<Vec<_>>()
        .join(" ");
    (declared, names, roles)
}

/// The case's selected results: incompatibilities, then implications.
fn selected(case: &Obj) -> Vec<&str> {
    let mut ids = strs(case, "incompatibility_result_ids");
    ids.extend(strs(case, "implication_result_ids"));
    ids
}

fn result_field<'v>(results: &Index<'v>, rid: &str, field: &str) -> &'v str {
    results
        .get(rid)
        .map(|result| str_of(result, field))
        .unwrap_or_default()
}

fn argument_of<'v>(results: &Index<'v>, arguments: &Index<'v>, rid: &str) -> Option<&'v Obj> {
    arguments
        .get(result_field(results, rid, "argument_id"))
        .copied()
}

fn modules<'v>(profile: &'v Obj, case: &'v Obj, results: &Index<'v>) -> BTreeSet<&'v str> {
    let mut modules: BTreeSet<&str> = strs(profile, "modules").into_iter().collect();
    modules.extend(
        selected(case)
            .into_iter()
            .map(|rid| result_field(results, rid, "solution_module")),
    );
    modules
}

/// Python `generated_names(source)`: the `theorem`/`def` names in order.
fn generated_names(source: &str) -> Vec<&str> {
    static NAME: OnceLock<Regex> = OnceLock::new();
    let name = NAME.get_or_init(|| {
        Regex::new(r"^(?:theorem|def) ([A-Za-z_][A-Za-z_0-9]*)").expect("valid pattern")
    });
    source
        .split('\n')
        .filter_map(|line| {
            name.captures(line)
                .ok()
                .flatten()
                .and_then(|captures| captures.get(1))
                .map(|found| found.as_str())
        })
        .collect()
}

/// Python `check_generated_axioms(output, source, namespace, permitted)`.
fn check_generated_axioms(
    output: &str,
    source: &str,
    namespace: &str,
    permitted: &[&str],
) -> Result<(), String> {
    for name in generated_names(source) {
        let qualified = format!("{namespace}.{name}");
        if output.contains(&format!("'{qualified}' does not depend on any axioms")) {
            continue;
        }
        let pattern = format!(
            r"{}\s*\[([^\]]*)\]",
            fancy_regex::escape(&format!("'{qualified}' depends on axioms:"))
        );
        let found = Regex::new(&pattern)
            .ok()
            .and_then(|pattern| pattern.captures(output).ok().flatten())
            .and_then(|captures| captures.get(1).map(|found| found.as_str().to_owned()));
        let Some(listed) = found else {
            return Err(format!("missing axiom verification for {qualified}"));
        };
        let actual: BTreeSet<&str> = listed
            .split(',')
            .map(|axiom| axiom.trim_matches(pyfmt::is_space))
            .filter(|axiom| !axiom.is_empty())
            .collect();
        let forbidden: Vec<&str> = actual
            .iter()
            .filter(|axiom| !permitted.contains(axiom))
            .copied()
            .collect();
        if !forbidden.is_empty() {
            return Err(format!(
                "{qualified}: profile-forbidden axioms {}",
                repr(&json!(forbidden))
            ));
        }
    }
    Ok(())
}

/// The model registrations of `case` whose model binds every profile
/// constant as the profile does (`eligible`; `known` also requires the model
/// to be registered, as `certificate_source` does).
fn eligible<'v>(case: &'v Obj, models: &Index<'v>, known: bool) -> Vec<&'v Obj> {
    case.get("model_bindings")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_object)
        .filter(|entry| !known || models.contains_key(str_of(entry, "model_id")))
        .filter(|entry| model_profile_mismatches(case, entry, models).is_empty())
        .collect()
}

/// Python `configurations.certificate_source(case, statements, results,
/// arguments, models)`.
pub fn certificate_source(case: &Obj, context: &Context) -> String {
    let profile = semantics(case);
    let (statements, results, arguments, models) = (
        &context.statements,
        &context.results,
        &context.arguments,
        &context.models,
    );
    let witnesses = eligible(case, models, true);
    let mut imports = modules(profile, case, results);
    for entry in &witnesses {
        if let Some(model) = models.get(str_of(entry, "model_id")) {
            imports.extend(strs(model, "modules"));
        }
    }
    let mut lines: Vec<String> = imports
        .iter()
        .map(|module| format!("import {module}"))
        .collect();
    lines.push("namespace ConfigurationCertificates".into());
    let (declared, names, roles) = binders(profile);
    let incompatible = strs(case, "incompatibility_result_ids");
    for (index, rid) in selected(case).into_iter().enumerate() {
        let argument = argument_of(results, arguments, rid);
        let mut parts: Vec<String> = argument
            .map(|argument| strs(argument, "premise_statement_ids"))
            .unwrap_or_default()
            .into_iter()
            .map(|sid| application(profile, statements, sid))
            .collect();
        parts.push(if incompatible.contains(&rid) {
            "False".into()
        } else {
            application(
                profile,
                statements,
                argument
                    .map(|argument| str_of(argument, "conclusion_statement_id"))
                    .unwrap_or_default(),
            )
        });
        lines.push(format!(
            "theorem certificate_{index} : ∀ {declared}, {} := by",
            parts.join(" → ")
        ));
        lines.push(format!("  intro {}", names.join(" ")));
        lines.push(format!(
            "  exact @{} {roles}",
            result_field(results, rid, "theorem")
        ));
    }
    static ROLE: OnceLock<Regex> = OnceLock::new();
    let role = ROLE.get_or_init(|| {
        Regex::new(r"(?<![A-Za-z_0-9.])[A-Za-z_][A-Za-z_0-9]*(?![A-Za-z_0-9.])")
            .expect("valid pattern")
    });
    for (index, entry) in witnesses.iter().enumerate() {
        let Some(model) = models.get(str_of(entry, "model_id")) else {
            continue;
        };
        let bindings = object(model.get("bindings"));
        let substitutions: HashMap<&str, &str> = object(entry.get("parameters"))
            .into_iter()
            .flatten()
            .map(|(role, key)| {
                let term = bindings
                    .and_then(|bindings| bindings.get(key.as_str().unwrap_or_default()))
                    .and_then(Value::as_str)
                    .unwrap_or_default();
                (role.as_str(), term)
            })
            .collect();
        for (j, (name, kind)) in parameters(profile).into_iter().enumerate() {
            // Roles are unqualified names. A role named Model must not
            // replace the final component of ExistencePSR.Model.
            let expected = role.replace_all(kind, |captures: &fancy_regex::Captures<'_, str>| {
                let found = &captures[0];
                match substitutions.get(found) {
                    Some(term) => format!("({term})"),
                    None => found.to_owned(),
                }
            });
            lines.push(format!(
                "def model_parameter_{index}_{j} : {expected} := {}",
                substitutions.get(name).copied().unwrap_or_default()
            ));
        }
    }
    let joined = lines.join("\n");
    let prints: Vec<String> = generated_names(&joined)
        .into_iter()
        .map(|name| format!("#print axioms {name}"))
        .collect();
    lines.extend(prints);
    lines.push("end ConfigurationCertificates".into());
    lines.join("\n") + "\n"
}

/// Python `composition_source(case, report, statements, results,
/// arguments)`: each reported composed core replayed as a Lean proof term
/// over its inputs, and the number of cores.
pub fn composition_source(case: &Obj, report: &Value, context: &Context) -> (String, usize) {
    let profile = semantics(case);
    let (statements, results, arguments) =
        (&context.statements, &context.results, &context.arguments);
    let mut lines: Vec<String> = modules(profile, case, results)
        .iter()
        .map(|module| format!("import {module}"))
        .collect();
    lines.push("namespace ConfigurationCompositions".into());
    let (declared, names, roles) = binders(profile);
    let mut count = 0;
    for entry in report["configurations"].as_array().into_iter().flatten() {
        for core in entry["incompatible_cores"].as_array().into_iter().flatten() {
            let assumptions: Vec<&str> = core["statement_ids"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect();
            let mut expected: Vec<String> = assumptions
                .iter()
                .map(|sid| application(profile, statements, sid))
                .collect();
            expected.push("False".into());
            let mut hypothesis: HashMap<String, String> = assumptions
                .iter()
                .enumerate()
                .map(|(i, sid)| (sid.to_string(), format!("h_{i}")))
                .collect();
            lines.push(format!(
                "theorem composition_{count} : ∀ {declared}, {} := by",
                expected.join(" → ")
            ));
            let mut intro: Vec<String> = names.iter().map(|name| name.to_string()).collect();
            intro.extend((0..assumptions.len()).map(|i| format!("h_{i}")));
            lines.push(format!("  intro {}", intro.join(" ")));
            for (index, rid) in core["result_ids"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .enumerate()
            {
                let argument = argument_of(results, arguments, rid);
                let premise_args = argument
                    .map(|argument| strs(argument, "premise_statement_ids"))
                    .unwrap_or_default()
                    .into_iter()
                    .map(|sid| hypothesis.get(sid).cloned().unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(" ");
                let term = format!(
                    "@{} {roles} {premise_args}",
                    result_field(results, rid, "theorem")
                );
                if core["result_id"].as_str() == Some(rid) {
                    lines.push(format!("  exact {term}"));
                } else {
                    let sid = argument
                        .map(|argument| str_of(argument, "conclusion_statement_id"))
                        .unwrap_or_default();
                    let name = format!("derived_{index}");
                    lines.push(format!(
                        "  have {name} : {} := {term}",
                        application(profile, statements, sid)
                    ));
                    hypothesis.insert(sid.to_owned(), name);
                }
            }
            count += 1;
        }
    }
    let joined = lines.join("\n");
    let prints: Vec<String> = generated_names(&joined)
        .into_iter()
        .map(|name| format!("#print axioms {name}"))
        .collect();
    lines.extend(prints);
    lines.push("end ConfigurationCompositions".into());
    (lines.join("\n") + "\n", count)
}

fn permitted(case: &Obj) -> Vec<&str> {
    strs(semantics(case), "permitted_axioms")
}

/// Python `verify_case`: rebuilds the modules, checks the certificates
/// (zero forbidden axioms), runs `scripts/verify-result.sh` for each selected
/// result not yet verified in this invocation and checks the eligible
/// models. No marker, stale olean or registration counts as success.
pub fn verify_case(
    root: &Path,
    case: &Obj,
    context: &Context,
    verified_results: &mut BTreeSet<String>,
) -> Result<Value, String> {
    let profile = semantics(case);
    let chosen = selected(case);
    let witnesses: Vec<&Obj> = eligible(case, &context.models, false)
        .into_iter()
        .filter_map(|entry| context.models.get(str_of(entry, "model_id")).copied())
        .collect();
    let mut imports = modules(profile, case, &context.results);
    for model in &witnesses {
        imports.extend(strs(model, "modules"));
    }
    let step = |argv: Vec<String>| -> Result<subprocess::Finished, String> {
        match run(root, &argv, CASE_TIMEOUT) {
            Ran::Unavailable(error) => {
                Err(format!("configuration verification unavailable: {error}"))
            }
            Ran::Done(done) if !done.success => Err(format!(
                "configuration verification failed ({}):\n{}\n{}",
                list_repr(&argv),
                done.stdout,
                done.stderr
            )),
            Ran::Done(done) => Ok(done),
        }
    };
    let argv = |parts: &[&str]| parts.iter().map(|part| part.to_string()).collect();
    let mut build = vec!["lake", "build"];
    build.extend(imports.iter().copied());
    step(argv(&build))?;
    let source = certificate_source(case, context);
    let scratch = Scratch::write(root, &source)?;
    let done = step(vec![
        "lake".into(),
        "env".into(),
        "lean".into(),
        scratch.name(),
    ])?;
    check_generated_axioms(
        &done.stdout,
        &source,
        "ConfigurationCertificates",
        &permitted(case),
    )?;
    drop(scratch);
    let unique: BTreeSet<&str> = chosen.iter().copied().collect();
    let reused: Vec<&str> = unique
        .iter()
        .filter(|rid| verified_results.contains(**rid))
        .copied()
        .collect();
    for rid in &unique {
        if !verified_results.contains(*rid) {
            step(argv(&["scripts/verify-result.sh", rid]))?;
            verified_results.insert(rid.to_string());
        }
    }
    let statements: HashMap<&str, &Obj> = context
        .statements
        .iter()
        .map(|(id, record)| (*id, *record))
        .collect();
    let models = bind_check::verify_model_records(root, &witnesses, &statements)?;
    Ok(json!({
        "result_ids": unique,
        "reused_result_ids_in_this_invocation": reused,
        "models": models,
    }))
}

/// Python `verify_compositions(case, report, ...)`: replays every reported
/// core in Lean; `{"cores": n}`.
pub fn verify_compositions(
    root: &Path,
    case: &Obj,
    report: &Value,
    context: &Context,
) -> Result<Value, String> {
    let (source, count) = composition_source(case, report, context);
    if count == 0 {
        return Ok(json!({"cores": 0}));
    }
    let scratch = Scratch::write(root, &source)?;
    let argv = vec![
        "lake".to_owned(),
        "env".into(),
        "lean".into(),
        scratch.name(),
    ];
    let done = match run(root, &argv, COMPOSITION_TIMEOUT) {
        Ran::Unavailable(error) => {
            return Err(format!(
                "configuration composition verification unavailable: {error}"
            ));
        }
        Ran::Done(done) => done,
    };
    if !done.success {
        return Err(format!(
            "configuration composition rejected:\n{}\n{}",
            done.stdout, done.stderr
        ));
    }
    check_generated_axioms(
        &done.stdout,
        &source,
        "ConfigurationCompositions",
        &permitted(case),
    )?;
    Ok(json!({"cores": count}))
}

/// The live part of Python `collect_configuration_reports`: for each
/// `(case, selection)` in order, verify the case in Lean, compute its
/// verified report and replay its cores; then bind every selected original
/// theorem in one exporter run. No report is returned if any step fails.
pub fn verified_reports(
    root: &Path,
    corpus: &Corpus,
    context: &Context,
    selections: &[(&Obj, Option<Vec<&str>>)],
) -> Result<Vec<Value>, String> {
    let root = &bind_check::absolute(root);
    let mut verified_results = BTreeSet::new();
    let mut originals = BTreeSet::new();
    let mut reports = Vec::new();
    for (case, selection) in selections {
        let mut verification = verify_case(root, case, context, &mut verified_results)?;
        let chosen: BTreeSet<String> = selected(case).into_iter().map(str::to_owned).collect();
        verification["original_bound_result_ids"] = json!(chosen);
        originals.extend(chosen);
        let mut report = configurations::configuration_report(
            case,
            &context.results,
            &context.arguments,
            &context.models,
            true,
            selection.as_ref().map(|ids| ("selection", ids.to_vec())),
        )?;
        verification["compositions"] = verify_compositions(root, case, &report, context)?;
        report["verification"] = verification;
        reports.push(report);
    }
    if !originals.is_empty() {
        bind_check::bind_originals(root, corpus, &originals)?;
    }
    Ok(reports)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn axiom_lines_and_names() {
        let source =
            "import A\nnamespace N\ntheorem a : True := by\ndef b : Nat := 1\n#print axioms a\n";
        assert_eq!(generated_names(source), vec!["a", "b"]);
        let clean =
            "'N.a' does not depend on any axioms\n'N.b' depends on axioms: [propext,\n Quot.sound]";
        assert!(check_generated_axioms(clean, source, "N", &["propext", "Quot.sound"]).is_ok());
        assert_eq!(
            check_generated_axioms(clean, source, "N", &["propext"]).unwrap_err(),
            "N.b: profile-forbidden axioms ['Quot.sound']"
        );
        assert_eq!(
            check_generated_axioms("", source, "N", &[]).unwrap_err(),
            "missing axiom verification for N.a"
        );
    }

    #[test]
    fn timeouts_print_as_python_does() {
        let argv = vec!["lake".to_owned(), "build".into()];
        assert_eq!(
            timed_out(&argv, CASE_TIMEOUT),
            "Command '['lake', 'build']' timed out after 1200 seconds"
        );
    }
}
