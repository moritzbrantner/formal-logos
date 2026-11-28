//! `bind-check` (#162): argument records must match each result theorem's
//! Lean type. A port of `scripts/corpus.py bind-check`.
//!
//! Lean stays the verifier: `scripts/BindTypes.lean` describes every theorem's
//! binders, result type, theory-bundle conjuncts, reached sense constants and
//! exact-expression contracts, and this module compares that description with
//! the corpus records, rule for rule as Python's `bind_result`, `bind_report`
//! and `add_sense_bind_problems` do. [`tool_input`] writes the exporter input
//! byte for byte as Python's `json.dump`, so one recorded exporter output can
//! drive both implementations (`--lean-json`). [`verify_models`] is Python's
//! `finite_models.verify_models`: it compiles the registered finite-model
//! certificates and checks that each is zero-axiom.

use crate::{Corpus, identity::legacy_uuid, pyfmt};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};

/// The Lean exporter, relative to the repository root.
pub const BIND_TOOL: &str = "scripts/BindTypes.lean";

/// Theory definitions (#149, #160): a hypothesis whose head lies in one of
/// these namespaces is a theory bundle, unfolded one step by the exporter.
pub const THEORY_BUNDLE_PREFIXES: &[&str] = &["TruthCore.Comparison."];

const SCHEMA_INSTANCE_PREDICATE: &str = "instance_of_schema";
const SENSE_ALLOWLIST: &str = "corpus/sense-index-allowlist.json";
const CONTRACTS: &str = "scripts/contracts";
const MODEL_TIMEOUT: Duration = Duration::from_secs(600);

type Obj = Map<String, Value>;
/// `(result id, role, statement id)`, as Python's pin keys.
type PinKey = (String, String, String);

/// Python `PINNED_UNDECLARED_BINDINGS`: the statements without
/// `lean_declaration` that bind to a logical-form Lean type, each pinned to
/// that exact (whitespace-normalized) type.
pub fn pins() -> BTreeMap<PinKey, &'static str> {
    [
        (
            "PLATO-TIM-28A-28C-COSMOS-CAUSE-A",
            "STMT-COSMOS-HAS-CAUSE",
            "∃ cause, Causes cause cosmos",
        ),
        (
            "PLATO-TIM-28A-28C-COSMOS-CAUSE-B",
            "STMT-COSMOS-HAS-DISTINCT-CAUSE",
            "∃ cause, cause ≠ cosmos ∧ Causes cause cosmos",
        ),
    ]
    .into_iter()
    .map(|(result, statement, lean_type)| {
        (
            (
                legacy_uuid("result", result),
                "conclusion".to_owned(),
                legacy_uuid("statement", statement),
            ),
            lean_type,
        )
    })
    .collect()
}

/// The reviewed exact-expression contracts (`scripts/contracts/*.json`),
/// by result id (Python `expression_contracts.contracts`).
pub struct Contracts {
    root: PathBuf,
    by_result: BTreeMap<String, Value>,
}

impl Contracts {
    /// No contracts: binding by head constant and pins alone.
    pub fn none() -> Self {
        Self {
            root: PathBuf::new(),
            by_result: BTreeMap::new(),
        }
    }

    pub fn load(root: &Path) -> Result<Self, String> {
        let mut paths: Vec<PathBuf> = match fs::read_dir(root.join(CONTRACTS)) {
            Ok(entries) => entries
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
                .collect(),
            Err(_) => Vec::new(),
        };
        paths.sort();
        let mut by_result = BTreeMap::new();
        for path in paths {
            let item: Value = fs::read(&path)
                .map_err(|error| error.to_string())
                .and_then(|bytes| serde_json::from_slice(&bytes).map_err(|e| e.to_string()))
                .map_err(|error| format!("{}: {error}", path.display()))?;
            let id = text(&item["result_id"]);
            by_result.insert(id, item);
        }
        Ok(Self {
            root: root.to_owned(),
            by_result,
        })
    }

    /// Python `expression_contracts.check`.
    fn check(&self, result: &Obj, described: &Value) -> Vec<Value> {
        let Some(contract) = self.by_result.get(&text(field(result, "id"))) else {
            return Vec::new();
        };
        let mut problems = Vec::new();
        if field(result, "theorem") != &contract["theorem"] {
            problems.push(
                json!({"kind": "expression-contract-theorem", "expected": contract["theorem"]}),
            );
        }
        for item in contract["frozen_inputs"].as_array().into_iter().flatten() {
            let path = self.root.join(text(&item["path"]));
            let intact = path.is_file()
                && fs::read(&path)
                    .is_ok_and(|bytes| Value::String(sha256_hex(&bytes)) == item["sha256"]);
            if !intact {
                problems.push(
                    json!({"kind": "expression-contract-frozen-input", "path": item["path"]}),
                );
            }
        }
        let empty = Value::Object(Map::new());
        let expression = described.get("expression_contract").unwrap_or(&empty);
        let (type_sha256, current) = match summarize(expression) {
            Ok(summary) => summary,
            Err(detail) => {
                problems.push(json!({"kind": "expression-contract-unavailable", "detail": detail}));
                return problems;
            }
        };
        if Value::String(type_sha256.clone()) != contract["type_sha256"] {
            problems.push(json!({"kind": "expression-contract-type",
                                 "expected": contract["type_sha256"], "actual": type_sha256}));
        }
        let empty = Map::new();
        let expected = contract["dependencies"].as_object().unwrap_or(&empty);
        let names: BTreeSet<&String> = expected.keys().chain(current.keys()).collect();
        let changed: Vec<&String> = names
            .into_iter()
            .filter(|name| {
                expected.get(*name)
                    != current
                        .get(*name)
                        .map(|v| Value::String(v.clone()))
                        .as_ref()
            })
            .collect();
        if !changed.is_empty() {
            problems
                .push(json!({"kind": "expression-contract-dependencies", "declarations": changed}));
        }
        problems
    }
}

/// Python `expression_contracts.summarize`: the type fingerprint and one
/// fingerprint per dependency, or the error detail.
fn summarize(expression: &Value) -> Result<(String, BTreeMap<String, String>), String> {
    if expression.get("encoding") != Some(&json!("closed-expression-v1")) {
        return Err("unsupported or missing closed-expression encoding".into());
    }
    if pyfmt::json_dumps(expression, true).contains("unsupported-") {
        return Err("unsupported expression boundary in exact contract".into());
    }
    let dependencies = expression
        .get("dependencies")
        .and_then(Value::as_array)
        .ok_or("missing or duplicated expression dependencies")?;
    let mut fingerprints = BTreeMap::new();
    for dependency in dependencies {
        let name = dependency.get("declaration").ok_or("'declaration'")?;
        fingerprints.insert(text(name), fingerprint(dependency));
    }
    if fingerprints.len() != dependencies.len() {
        return Err("missing or duplicated expression dependencies".into());
    }
    let universe = expression
        .get("universe_parameters")
        .ok_or("'universe_parameters'")?;
    let lean_type = expression.get("type").ok_or("'type'")?;
    Ok((fingerprint(&json!([universe, lean_type])), fingerprints))
}

/// Python `fingerprint`: SHA-256 of the compact, key-sorted, non-ASCII JSON.
fn fingerprint(value: &Value) -> String {
    sha256_hex(serde_json::to_string(value).unwrap_or_default().as_bytes())
}

fn field<'a>(record: &'a Obj, key: &str) -> &'a Value {
    record.get(key).unwrap_or(&Value::Null)
}

fn text(value: &Value) -> String {
    pyfmt::text(value)
}

fn strings(value: Option<&Value>) -> Vec<String> {
    value
        .and_then(Value::as_array)
        .map(|items| items.iter().map(text).collect())
        .unwrap_or_default()
}

/// Python `is_corpus_constant`.
fn is_corpus_constant(name: &Value) -> bool {
    name.as_str()
        .is_some_and(|name| name == "TruthCore" || name.starts_with("TruthCore."))
}

/// A binding request: a result record, or a schema registration's synthetic
/// `{id, solution_module, theorem}` record, with the argument it binds.
pub struct Request {
    pub record: Obj,
    pub argument: Obj,
    pub schema: bool,
}

/// Python `schema_binding_records` over the relations whose verification
/// result is in `scope` (all with `None`).
pub fn schema_requests(
    corpus: &Corpus,
    scope: Option<&BTreeSet<String>>,
) -> Result<Vec<Request>, String> {
    let mut relations: Vec<&Obj> = corpus
        .records("relations")
        .into_iter()
        .filter(|relation| {
            scope.is_none_or(|scope| {
                relation
                    .get("verification_result_id")
                    .and_then(Value::as_str)
                    .is_some_and(|id| scope.contains(id))
            })
        })
        .collect();
    relations.sort_by_key(|relation| text(field(relation, "id")));
    let mut requests = Vec::new();
    for relation in relations {
        if field(relation, "predicate") != SCHEMA_INSTANCE_PREDICATE {
            continue;
        }
        let result_id = text(field(relation, "verification_result_id"));
        let result = corpus.get("results", &result_id).ok_or_else(|| {
            format!(
                "{}: unknown verification result {result_id}",
                text(field(relation, "id"))
            )
        })?;
        for (side, theorem_field, statement_field) in [
            ("instance", "instance_theorem", "subject_id"),
            ("schema", "schema_theorem", "object_id"),
        ] {
            let record = json!({
                "id": format!("{}:{side}", text(field(relation, "id"))),
                "solution_module": field(&result.fields, "solution_module"),
                "theorem": field(relation, theorem_field),
            });
            let argument = json!({"premise_statement_ids": [],
                                  "conclusion_statement_id": field(relation, statement_field)});
            requests.push(Request {
                record: record.as_object().cloned().unwrap_or_default(),
                argument: argument.as_object().cloned().unwrap_or_default(),
                schema: true,
            });
        }
    }
    Ok(requests)
}

/// The result requests in `scope` (all with `None`), in file order.
pub fn result_requests(corpus: &Corpus, scope: Option<&BTreeSet<String>>) -> Vec<Request> {
    corpus
        .records("results")
        .into_iter()
        .filter(|result| scope.is_none_or(|scope| scope.contains(&text(field(result, "id")))))
        .map(|result| Request {
            record: result.clone(),
            argument: corpus
                .get("arguments", &text(field(result, "argument_id")))
                .map(|argument| argument.fields.clone())
                .unwrap_or_default(),
            schema: false,
        })
        .collect()
}

/// Python `bind_tool_input(..., senses=True)`, serialized as `json.dump`
/// writes it (insertion order, `", "`/`": "` separators, ASCII escapes).
pub fn tool_input(corpus: &Corpus, contracts: &Contracts, requests: &[Request]) -> String {
    let mut out = tool_input_with(corpus, contracts, requests, true);
    let restating = restating_input(requests);
    if !restating.is_empty() {
        out.pop();
        out.push_str(&format!(
            ", \"restating\": {}}}",
            serde_json::to_string(&restating).unwrap_or_default()
        ));
    }
    out
}

/// The exporter's `restating` input (#2190): for each result request that
/// declares `restates_conclusion`, in result-id order, its lemma and the
/// named dischargers of its side conditions as `[hypothesis, declaration]`.
fn restating_input(requests: &[Request]) -> Vec<Value> {
    let mut ordered: Vec<&Request> = requests.iter().filter(|r| !r.schema).collect();
    ordered.sort_by_key(|request| text(field(&request.record, "id")));
    ordered
        .into_iter()
        .filter_map(|request| request.record.get(RESTATES).and_then(Value::as_object))
        .map(|marker| {
            let dischargers: Vec<Value> = marker
                .get("side_conditions")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|condition| {
                    let discharger = condition.get("discharged_by")?.as_str()?;
                    Some(json!([text(&condition["hypothesis"]), discharger]))
                })
                .collect();
            json!({"lemma": text(field(marker, "lemma")), "dischargers": dischargers})
        })
        .collect()
}

/// Python `bind_tool_input(..., senses)`: without `senses` (as
/// `unused-premises` calls it) the input names no sense constants or
/// sense theorems, so the exporter adds no `sense_aliases` element.
pub fn tool_input_with(
    corpus: &Corpus,
    contracts: &Contracts,
    requests: &[Request],
    senses: bool,
) -> String {
    let mut ordered: Vec<&Request> = requests.iter().collect();
    ordered.sort_by_key(|request| text(field(&request.record, "id")));
    let modules: BTreeSet<String> = ordered
        .iter()
        .map(|request| text(field(&request.record, "solution_module")))
        .collect();
    let theorems: Vec<String> = ordered
        .iter()
        .map(|request| text(field(&request.record, "theorem")))
        .collect();
    let sense_constants: BTreeSet<String> = corpus
        .records("disambiguations")
        .into_iter()
        .flat_map(|record| {
            record
                .get("senses")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
        })
        .filter_map(|sense| sense.get("lean_declaration"))
        .filter(|declaration| pyfmt::truthy(Some(declaration)))
        .map(text)
        .collect();
    let sense_theorems: Vec<String> = ordered
        .iter()
        .filter(|request| {
            let argument = request
                .record
                .get("argument_id")
                .and_then(Value::as_str)
                .and_then(|id| corpus.get("arguments", id));
            argument.is_some_and(|argument| pyfmt::truthy(argument.fields.get("term_senses")))
        })
        .map(|request| text(field(&request.record, "theorem")))
        .collect();
    let contract_theorems: Vec<String> = ordered
        .iter()
        .filter(|request| {
            contracts
                .by_result
                .contains_key(&text(field(&request.record, "id")))
        })
        .map(|request| text(field(&request.record, "theorem")))
        .collect();
    let list = |items: &mut dyn Iterator<Item = &String>| {
        format!(
            "[{}]",
            items
                .map(|item| pyfmt::json_str(item, true))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let prefixes: Vec<String> = THEORY_BUNDLE_PREFIXES
        .iter()
        .map(|p| p.to_string())
        .collect();
    let mut out = format!(
        "{{\"modules\": {}, \"theorems\": {}, \"bundle_prefixes\": {}",
        list(&mut modules.iter()),
        list(&mut theorems.iter()),
        list(&mut prefixes.iter()),
    );
    if senses {
        out.push_str(&format!(
            ", \"sense_constants\": {}, \"sense_theorems\": {}",
            list(&mut sense_constants.iter()),
            list(&mut sense_theorems.iter()),
        ));
    }
    if !contract_theorems.is_empty() {
        out.push_str(&format!(
            ", \"contract_theorems\": {}",
            list(&mut contract_theorems.iter())
        ));
    }
    out.push('}');
    out
}

/// Runs the exporter on `input` (Python `run_bind_tool`); needs `lake build`.
pub fn run_tool(root: &Path, input: &str) -> Result<Vec<Value>, String> {
    run_exporter(root, BIND_TOOL, input, "bind-check")
}

/// Runs the Lean exporter `tool` (a path below `root`, such as
/// `scripts/BindTypes.lean`) on `input` with `lake env lean --run`, as
/// Python `run_bind_tool(tool_input, tool=…, command_name=…)` does, and
/// returns the JSON array it prints. `command` names the command in the
/// missing-`lake` message. Lean stays the verifier; this only runs it.
pub fn run_exporter(
    root: &Path,
    tool_path: &str,
    input: &str,
    command: &str,
) -> Result<Vec<Value>, String> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let root = &absolute(root);
    let path = std::env::temp_dir().join(format!(
        "truth-{command}-{}-{}.json",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    fs::write(&path, input).map_err(|error| format!("cannot write the exporter input: {error}"))?;
    let tool = root.join(tool_path);
    let output = Command::new("lake")
        .args(["env", "lean", "--run"])
        .arg(&tool)
        .arg(&path)
        .current_dir(root)
        .output();
    let _ = fs::remove_file(&path);
    let output = match output {
        Ok(output) => output,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!(
                "{command} needs `lake` on PATH (run after `lake build`)"
            ));
        }
        Err(error) => return Err(format!("cannot run {tool_path}: {error}")),
    };
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let detail = if stderr.trim().is_empty() {
            stdout.trim()
        } else {
            stderr.trim()
        };
        return Err(format!(
            "{tool_path} failed (exit {}):\n{detail}",
            output.status.code().unwrap_or(-1)
        ));
    }
    match serde_json::from_slice::<Value>(&output.stdout) {
        Ok(Value::Array(items)) => Ok(items),
        Ok(_) => Err(format!("{tool_path} must print a JSON array")),
        Err(error) => Err(format!("{tool_path} printed invalid JSON: {error}")),
    }
}

/// The statement records by id.
fn statements(corpus: &Corpus) -> HashMap<&str, &Obj> {
    corpus
        .records_by_id("statements")
        .map(|(id, record)| (id, &record.fields))
        .collect()
}

/// Python `bind_result`: one request's argument against the Lean description
/// of its theorem.
fn bind_result(
    request: &Request,
    statements: &HashMap<&str, &Obj>,
    described: &Value,
    pins: &BTreeMap<PinKey, &str>,
    contracts: &Contracts,
) -> Value {
    let result = &request.record;
    let argument = &request.argument;
    let declaration = |statement_id: &Value| -> Option<Value> {
        statements
            .get(statement_id.as_str().unwrap_or_default())
            .and_then(|record| record.get("lean_declaration"))
            .filter(|value| !value.is_null())
            .cloned()
    };
    let declaration_or_null =
        |statement_id: &Value| declaration(statement_id).unwrap_or(Value::Null);
    let mut problems: Vec<Value> = Vec::new();
    let mut undecidable: Vec<Obj> = Vec::new();
    if let Some(error) = described.get("error") {
        return json!({
            "id": result["id"], "theorem": result["theorem"], "status": "mismatch",
            "premises": [], "conclusion": null, "parameters": [],
            "problems": [{"kind": "lean-error", "detail": error}], "undecidable": [],
        });
    }
    let binders: &[Value] = described
        .get("binders")
        .and_then(Value::as_array)
        .map_or(&[], Vec::as_slice);
    let parameters: Vec<&Value> = binders
        .iter()
        .filter(|binder| !pyfmt::truthy(binder.get("prop")))
        .map(|binder| &binder["name"])
        .collect();
    // (hypothesis fields, position, conjunct, bundle head)
    let mut hypotheses: Vec<(Obj, usize, Option<usize>, Option<Value>)> = Vec::new();
    for (index, binder) in binders.iter().enumerate() {
        if !pyfmt::truthy(binder.get("prop")) {
            continue;
        }
        let fields = binder.as_object().cloned().unwrap_or_default();
        match binder.get("bundle") {
            None | Some(Value::Null) => hypotheses.push((fields, index, None, None)),
            Some(Value::Array(conjuncts)) => {
                for (number, conjunct) in conjuncts.iter().enumerate() {
                    let mut fields = conjunct.as_object().cloned().unwrap_or_default();
                    fields.insert(
                        "name".into(),
                        json!(format!("{}.{}", text(&binder["name"]), number + 1)),
                    );
                    hypotheses.push((fields, index, Some(number), Some(binder["head"].clone())));
                }
            }
            Some(_) => {
                problems.push(json!({"kind": "bundle-unfold-failed",
                                             "hypothesis": binder["name"], "head": binder["head"]}))
            }
        }
    }

    let mut unused: Vec<Value> = argument
        .get("premise_statement_ids")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut premises: Vec<(usize, usize, Obj)> = Vec::new();
    let mut unmatched = Vec::new();
    // First pass: bind by head constant.
    for hypothesis in &hypotheses {
        let (fields, position, conjunct, bundle) = hypothesis;
        let head = field(fields, "head");
        let found = unused
            .iter()
            .position(|sid| declaration(sid).is_some_and(|declaration| &declaration == head));
        let Some(found) = found else {
            unmatched.push(hypothesis);
            continue;
        };
        let statement_id = unused.remove(found);
        let mut entry = Obj::new();
        entry.insert("hypothesis".into(), field(fields, "name").clone());
        entry.insert("position".into(), json!(position));
        entry.insert("statement_id".into(), statement_id);
        entry.insert("lean_declaration".into(), head.clone());
        if let Some(bundle) = bundle.as_ref().filter(|bundle| pyfmt::truthy(Some(bundle))) {
            entry.insert("bundle".into(), bundle.clone());
            entry.insert("conjunct".into(), json!(conjunct));
        }
        premises.push((*position, conjunct.unwrap_or(0), entry));
    }
    // Second pass: statements without a declaration take logical-form hypotheses.
    for (fields, position, conjunct, bundle) in unmatched {
        let head = field(fields, "head");
        if let Some(bundle) = bundle.as_ref().filter(|bundle| pyfmt::truthy(Some(bundle))) {
            // Bundle conjuncts never bind by logical form or pin.
            problems.push(
                json!({"kind": "unbound-bundle-conjunct", "hypothesis": fields["name"],
                                 "bundle": bundle, "head": head, "type": field(fields, "type")}),
            );
            continue;
        }
        let found = if is_corpus_constant(head) {
            None
        } else {
            unused.iter().position(|sid| declaration(sid).is_none())
        };
        let Some(found) = found else {
            problems.push(json!({"kind": "extra-hypothesis", "hypothesis": fields["name"],
                                 "position": position, "head": head, "type": field(fields, "type")}));
            continue;
        };
        let statement_id = unused.remove(found);
        let entry = json!({"hypothesis": fields["name"], "position": position,
                           "statement_id": statement_id, "lean_declaration": null});
        premises.push((
            *position,
            conjunct.unwrap_or(0),
            entry.as_object().cloned().unwrap_or_default(),
        ));
        let item = json!({"role": "premise", "statement_id": statement_id, "hypothesis": fields["name"],
                          "position": position, "type": field(fields, "type")});
        undecidable.push(item.as_object().cloned().unwrap_or_default());
    }
    for statement_id in &unused {
        problems.push(
            json!({"kind": "missing-premise", "statement_id": statement_id,
                             "lean_declaration": declaration_or_null(statement_id)}),
        );
    }

    let conclusion_id = field(argument, "conclusion_statement_id");
    let expected = declaration(conclusion_id);
    let outcome = described.get("result").unwrap_or(&Value::Null);
    let mut conclusion = json!({"statement_id": conclusion_id, "lean_declaration": outcome["head"],
                                "type": outcome["type"]});
    if !pyfmt::truthy(outcome.get("prop")) {
        problems.push(json!({"kind": "conclusion-not-prop", "type": outcome["type"]}));
    } else if let Some(expected) = expected {
        if expected != outcome["head"] {
            problems.push(
                json!({"kind": "conclusion-mismatch", "statement_id": conclusion_id,
                                 "lean_declaration": expected, "head": outcome["head"],
                                 "type": outcome["type"]}),
            );
        }
    } else if is_corpus_constant(&outcome["head"]) {
        problems.push(
            json!({"kind": "conclusion-unbound-declaration", "statement_id": conclusion_id,
                             "head": outcome["head"], "type": outcome["type"]}),
        );
    } else {
        conclusion["lean_declaration"] = Value::Null;
        let item =
            json!({"role": "conclusion", "statement_id": conclusion_id, "type": outcome["type"]});
        undecidable.push(item.as_object().cloned().unwrap_or_default());
    }

    let mut commitments = Vec::new();
    let mut commitment_ids: Vec<Value> = argument
        .get("commitment_statement_ids")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let bundle = outcome.get("bundle").filter(|bundle| !bundle.is_null());
    if commitment_ids.is_empty() && bundle.is_some() {
        // A theory-definition conclusion is a consistency claim; its commitments
        // must be recorded so that every conjunct is checked.
        problems.push(json!({"kind": "theory-conclusion-without-commitments",
                             "head": outcome.get("head"), "type": outcome["type"]}));
    }
    if !commitment_ids.is_empty() {
        match bundle.and_then(Value::as_array) {
            None => problems.push(json!({"kind": "commitments-without-bundle",
                                          "head": outcome.get("head"), "type": outcome["type"]})),
            Some(items) => {
                for (number, item) in items.iter().enumerate() {
                    let found = commitment_ids
                        .iter()
                        .position(|sid| declaration(sid).is_some_and(|d| d == item["head"]));
                    let Some(found) = found else {
                        problems.push(json!({"kind": "unbound-commitment", "position": number,
                                             "head": item["head"], "type": item["type"]}));
                        continue;
                    };
                    let statement_id = commitment_ids.remove(found);
                    commitments.push(json!({"position": number, "statement_id": statement_id,
                                            "lean_declaration": item["head"]}));
                }
                for statement_id in &commitment_ids {
                    problems.push(
                        json!({"kind": "missing-commitment", "statement_id": statement_id,
                                         "lean_declaration": declaration_or_null(statement_id)}),
                    );
                }
            }
        }
    }

    for item in &mut undecidable {
        let key = (
            text(&result["id"]),
            text(field(item, "role")),
            text(field(item, "statement_id")),
        );
        item.insert("pin".into(), json!([key.0, key.1, key.2]));
        let pinned = pins.get(&key);
        let lean_type = text(field(item, "type"));
        if pinned.is_none_or(|pinned| pyfmt::collapse(pinned) != pyfmt::collapse(&lean_type)) {
            problems.push(json!({"kind": "undeclared-binding", "role": item["role"],
                                 "statement_id": item["statement_id"], "type": item["type"],
                                 "pinned_type": pinned}));
        }
    }

    problems.extend(contracts.check(result, described));
    let status = if !problems.is_empty() {
        "mismatch"
    } else if !undecidable.is_empty() {
        "pinned"
    } else {
        "bound"
    };
    premises.sort_by_key(|(position, conjunct, _)| (*position, *conjunct));
    json!({
        "id": result["id"], "theorem": result["theorem"], "status": status,
        "premises": premises.into_iter().map(|(_, _, entry)| entry).collect::<Vec<_>>(),
        "conclusion": conclusion, "commitments": commitments, "parameters": parameters,
        "problems": problems, "undecidable": undecidable,
    })
}

/// The configuration gate's original-theorem binding (the end of Python
/// `collect_configuration_reports`): describes the results `ids` together in
/// one exporter run (without sense constants) and requires each to bind
/// exactly (`bound`; a pinned binding is rejected too).
pub fn bind_originals(root: &Path, corpus: &Corpus, ids: &BTreeSet<String>) -> Result<(), String> {
    let contracts = Contracts::load(root)?;
    let mut requests = result_requests(corpus, Some(ids));
    requests.sort_by_key(|request| text(field(&request.record, "id")));
    let described = run_tool(root, &tool_input_with(corpus, &contracts, &requests, false))?;
    let statements = statements(corpus);
    let pins = pins();
    let lookup = by_theorem(&described);
    let fallback = json!({"error": "missing original theorem description"});
    for request in &requests {
        let theorem = text(field(&request.record, "theorem"));
        let entry = bind_result(
            request,
            &statements,
            lookup.get(theorem.as_str()).copied().unwrap_or(&fallback),
            &pins,
            &contracts,
        );
        if entry["status"] != "bound" {
            return Err(format!(
                "{}: original theorem binding rejected: {}",
                text(field(&request.record, "id")),
                problems_repr(&entry["problems"])
            ));
        }
    }
    Ok(())
}

/// Python `repr` of binding problems, each dictionary in the key order
/// `bind_result` and `expression_contracts.check` build it (one ranking
/// covers every problem kind).
fn problems_repr(problems: &Value) -> String {
    const ORDER: [&str; 15] = [
        "kind",
        "role",
        "hypothesis",
        "bundle",
        "position",
        "statement_id",
        "lean_declaration",
        "head",
        "type",
        "pinned_type",
        "detail",
        "expected",
        "actual",
        "path",
        "declarations",
    ];
    let rank = |key: &str| {
        ORDER
            .iter()
            .position(|known| *known == key)
            .unwrap_or(ORDER.len())
    };
    let items: Vec<String> = problems
        .as_array()
        .into_iter()
        .flatten()
        .map(|problem| match problem.as_object() {
            Some(map) => {
                let mut keys: Vec<&String> = map.keys().collect();
                keys.sort_by_key(|key| rank(key));
                let fields: Vec<String> = keys
                    .into_iter()
                    .map(|key| format!("{}: {}", pyfmt::repr_str(key), pyfmt::repr(&map[key])))
                    .collect();
                format!("{{{}}}", fields.join(", "))
            }
            None => pyfmt::repr(problem),
        })
        .collect();
    format!("[{}]", items.join(", "))
}

/// The exporter descriptions by theorem name (a later entry wins, as in
/// Python's dict comprehension).
fn by_theorem(described: &[Value]) -> HashMap<&str, &Value> {
    described
        .iter()
        .filter_map(|entry| {
            entry
                .get("theorem")
                .and_then(Value::as_str)
                .map(|name| (name, entry))
        })
        .collect()
}

/// The binding entries of Python `bind_report` (results in id order, then
/// schema registrations), before `add_sense_bind_problems`: what
/// `unused-premises` reads.
pub fn bind_entries(
    corpus: &Corpus,
    contracts: &Contracts,
    described: &[Value],
    requests: &[Request],
) -> Vec<Value> {
    let statements = statements(corpus);
    let pins = pins();
    let lookup = by_theorem(described);
    let mut results: Vec<&Request> = requests.iter().filter(|request| !request.schema).collect();
    results.sort_by_key(|request| text(field(&request.record, "id")));
    let schema = requests.iter().filter(|request| request.schema);
    let mut entries = Vec::new();
    for request in results {
        let fallback = json!({"error": "theorem not described by the Lean tool"});
        let theorem = text(field(&request.record, "theorem"));
        let entry = bind_result(
            request,
            &statements,
            lookup.get(theorem.as_str()).copied().unwrap_or(&fallback),
            &pins,
            contracts,
        );
        entries.push(entry);
    }
    for request in schema {
        let fallback = json!({"error": "schema theorem not described by the Lean tool"});
        let theorem = text(field(&request.record, "theorem"));
        let mut entry = bind_result(
            request,
            &statements,
            lookup.get(theorem.as_str()).copied().unwrap_or(&fallback),
            &pins,
            contracts,
        );
        entry["kind"] = json!("schema-registration");
        entries.push(entry);
    }
    entries
}

/// Python `bind_report` followed by `add_sense_bind_problems`: binds every
/// request; a scoped report (`scope`) checks no stale pins.
pub fn report(
    root: &Path,
    corpus: &Corpus,
    contracts: &Contracts,
    described: &[Value],
    requests: &[Request],
    scope: Option<&BTreeSet<String>>,
) -> Result<Value, String> {
    let statements = statements(corpus);
    let pins = pins();
    let lookup = by_theorem(described);
    let mut entries = bind_entries(corpus, contracts, described, requests);
    let used: BTreeSet<(String, String, String)> = entries
        .iter()
        .flat_map(|entry| entry["undecidable"].as_array().into_iter().flatten())
        .map(|item| {
            let pin = strings(item.get("pin"));
            (
                pin.first().cloned().unwrap_or_default(),
                pin.get(1).cloned().unwrap_or_default(),
                pin.get(2).cloned().unwrap_or_default(),
            )
        })
        .collect();
    let stale: Vec<Value> = if scope.is_none() {
        pins.keys()
            .filter(|key| !used.contains(*key))
            .map(|(a, b, c)| json!([a, b, c]))
            .collect()
    } else {
        Vec::new()
    };
    add_sense_problems(root, corpus, &statements, &lookup, &mut entries)?;
    add_restating_problems(root, corpus, &statements, described, &mut entries);
    let aliases = sense_aliases(root, corpus, described)?;
    let mut report = json!({
        "summary": summary(&entries),
        "stale_pins": stale,
        "results": entries,
        "sense_aliases": aliases,
    });
    if let Some(scope) = scope {
        report["scope"] = json!(scope);
    }
    Ok(report)
}

/// The record field of a result whose premises restate its conclusion (#2190).
const RESTATES: &str = crate::transcription::RESTATES_CONCLUSION;

/// The axioms a result's Comparator config permits (`permitted_axioms`), or
/// `None` when the config cannot be read.
fn permitted_axioms(root: &Path, result: &Obj) -> Option<BTreeSet<String>> {
    let config = root.join(text(field(result, "comparator_config")));
    let value: Value = serde_json::from_slice(&fs::read(config).ok()?).ok()?;
    Some(strings(value.get("permitted_axioms")).into_iter().collect())
}

/// The `restates_conclusion` check (#2190) of every bound result that
/// declares it: problems are added to the entry, which then mismatches, and
/// the entry gets a `restates_conclusion` summary of what was checked.
///
/// What is checked, against the exporter's description of the lemma:
/// - the lemma exists in the environment of the result's Solution module (or
///   a module it imports), is a theorem, and its axioms are permitted by the
///   result's Comparator config;
/// - its body (after its binders) is either an `Iff` one side of which has the
///   conclusion's declaration as head constant (`iff`), or the lemma has a
///   propositional binder headed by the conclusion's declaration (`converse`);
/// - the other side (`iff`) or the body (`converse`) opens with at least one
///   `∃` binder that occurs in its matrix (the free parameters), and that
///   matrix mentions every premise's declaration, except premises held fixed
///   as propositional binders of the lemma and the listed
///   `unrestated_premise_ids` (which it must not mention);
/// - every other propositional binder is a listed side condition, and a
///   listed `discharged_by` declaration exists, is axiom-clean under the same
///   policy, and concludes that binder's type once its trailing binders are
///   metavariables (`isDefEq`); its remaining hypotheses are reported.
///
/// What is not checked: that the existentially bound variables correspond to
/// the result theorem's own free parameters, that the premise declarations
/// are applied to the same arguments as in the result theorem, or that the
/// matrix is exactly the premise conjunction. Mentioning a constant is a
/// syntactic test; the record's `note` and review carry the rest. A wrong
/// marker can only withdraw closure (rule (a)) from its conclusion, never add it.
fn add_restating_problems(
    root: &Path,
    corpus: &Corpus,
    statements: &HashMap<&str, &Obj>,
    described: &[Value],
    entries: &mut [Value],
) {
    let lemmas: HashMap<&str, &Value> = described
        .iter()
        .filter_map(|item| Some((item.get("restating_lemma")?.as_str()?, item)))
        .collect();
    let declaration = |statement_id: &str| -> Option<String> {
        statements
            .get(statement_id)
            .and_then(|record| record.get("lean_declaration"))
            .and_then(Value::as_str)
            .map(str::to_owned)
    };
    for entry in entries.iter_mut() {
        if entry["kind"] == "schema-registration" {
            continue;
        }
        let Some(result) = corpus.get("results", &text(&entry["id"])) else {
            continue;
        };
        let Some(marker) = result.fields.get(RESTATES).and_then(Value::as_object) else {
            continue;
        };
        let argument = corpus
            .get("arguments", &text(field(&result.fields, "argument_id")))
            .map(|argument| argument.fields.clone())
            .unwrap_or_default();
        let (problems, summary) = restating_problems(
            marker,
            &argument,
            &declaration,
            lemmas.get(text(field(marker, "lemma")).as_str()).copied(),
            permitted_axioms(root, &result.fields).as_ref(),
        );
        entry[RESTATES] = summary;
        if !problems.is_empty() {
            if let Some(list) = entry["problems"].as_array_mut() {
                list.extend(problems);
            }
            entry["status"] = json!("mismatch");
        }
    }
}

/// The problems and summary of one `restates_conclusion` marker against the
/// exporter's description of its lemma (see [`add_restating_problems`]).
fn restating_problems(
    marker: &Obj,
    argument: &Obj,
    declaration: &dyn Fn(&str) -> Option<String>,
    lemma: Option<&Value>,
    permitted: Option<&BTreeSet<String>>,
) -> (Vec<Value>, Value) {
    let name = text(field(marker, "lemma"));
    let mut problems = Vec::new();
    let mut summary = json!({"lemma": name});
    let Some(lemma) = lemma else {
        problems.push(json!({"kind": "restates-lemma-not-described", "head": name}));
        return (problems, summary);
    };
    if let Some(error) = lemma.get("error") {
        problems.push(json!({"kind": "restates-lemma-error", "head": name, "detail": error}));
        return (problems, summary);
    }
    if lemma["kind"] != "theorem" {
        problems.push(json!({"kind": "restates-lemma-not-theorem", "head": name,
                             "detail": lemma["kind"]}));
    }
    let disallowed = |axioms: &Value| -> Vec<String> {
        strings(Some(axioms))
            .into_iter()
            .filter(|axiom| permitted.is_none_or(|permitted| !permitted.contains(axiom)))
            .collect()
    };
    let unpermitted = disallowed(&lemma["axioms"]);
    if !unpermitted.is_empty() {
        problems
            .push(json!({"kind": "restates-axioms", "head": name, "declarations": unpermitted}));
    }
    summary["axioms"] = lemma["axioms"].clone();

    let conclusion_id = text(field(argument, "conclusion_statement_id"));
    let Some(conclusion) = declaration(&conclusion_id) else {
        problems.push(json!({"kind": "restates-conclusion-undeclared",
                             "statement_id": conclusion_id}));
        return (problems, summary);
    };
    let unrestated: BTreeSet<String> = strings(marker.get("unrestated_premise_ids"))
        .into_iter()
        .collect();
    let premises: Vec<String> = strings(argument.get("premise_statement_ids"));
    let binders: Vec<&Value> = lemma["binders"].as_array().into_iter().flatten().collect();
    let prop_binders: Vec<&Value> = binders
        .iter()
        .copied()
        .filter(|binder| binder["prop"] == true)
        .collect();
    let binder_heads: BTreeSet<String> = prop_binders
        .iter()
        .filter_map(|binder| binder["head"].as_str().map(str::to_owned))
        .collect();
    // The shape: (mode, restated side, name of the conclusion binder).
    let iff_side = lemma["sides"].as_array().and_then(|sides| {
        let index = sides
            .iter()
            .position(|side| side["head"].as_str() == Some(conclusion.as_str()))?;
        sides.get(1 - index)
    });
    let conclusion_binder = prop_binders
        .iter()
        .find(|binder| binder["head"].as_str() == Some(conclusion.as_str()))
        .map(|binder| text(&binder["name"]));
    let (mode, restated, conclusion_binder) = if lemma["body_head"] == "Iff" {
        match iff_side {
            Some(side) => ("iff", side, None),
            None => {
                problems.push(json!({"kind": "restates-shape", "head": name,
                    "detail": "no side of the Iff has the conclusion's declaration as head",
                    "lean_declaration": conclusion}));
                return (problems, summary);
            }
        }
    } else if conclusion_binder.is_some() {
        ("converse", &lemma["side"], conclusion_binder)
    } else {
        problems.push(json!({"kind": "restates-shape", "head": name,
            "detail": "neither an Iff with the conclusion on one side nor an implication from the conclusion",
            "lean_declaration": conclusion}));
        return (problems, summary);
    };
    summary["shape"] = json!(mode);
    if restated["exists_used"].as_u64().unwrap_or(0) == 0 {
        problems.push(json!({"kind": "restates-no-free-parameter", "head": name,
            "type": restated["type"],
            "detail": "the restated side opens with no existential binder its matrix uses"}));
    }
    let mentioned: BTreeSet<String> = strings(restated["matrix"].get("used_constants"))
        .into_iter()
        .collect();
    let mut held = Vec::new();
    for premise in &premises {
        let Some(premise_declaration) = declaration(premise) else {
            if !unrestated.contains(premise) {
                problems.push(json!({"kind": "restates-premise-undeclared",
                                     "statement_id": premise}));
            }
            continue;
        };
        let in_matrix = mentioned.contains(&premise_declaration);
        if unrestated.contains(premise) {
            if in_matrix {
                problems.push(json!({"kind": "restates-unrestated-premise-mentioned",
                    "statement_id": premise, "lean_declaration": premise_declaration}));
            }
        } else if binder_heads.contains(&premise_declaration) && !in_matrix {
            held.push(json!(premise));
        } else if !in_matrix {
            problems.push(
                json!({"kind": "restates-premise-missing", "statement_id": premise,
                                 "lean_declaration": premise_declaration}),
            );
        }
    }
    summary["held_premise_ids"] = json!(held);
    let premise_declarations: BTreeSet<String> = premises
        .iter()
        .filter_map(|premise| declaration(premise))
        .collect();
    let side_conditions: Vec<&Value> = prop_binders
        .iter()
        .copied()
        .filter(|binder| Some(text(&binder["name"])) != conclusion_binder)
        .filter(|binder| {
            !binder["head"]
                .as_str()
                .is_some_and(|head| premise_declarations.contains(head))
        })
        .collect();
    let listed: Vec<&Value> = marker
        .get("side_conditions")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .collect();
    let listed_names: BTreeSet<String> = listed
        .iter()
        .map(|condition| text(&condition["hypothesis"]))
        .collect();
    let mut conditions = Vec::new();
    for binder in &side_conditions {
        let hypothesis = text(&binder["name"]);
        if !listed_names.contains(&hypothesis) {
            problems.push(
                json!({"kind": "restates-unlisted-side-condition", "head": name,
                                 "hypothesis": hypothesis, "type": binder["type"]}),
            );
        }
    }
    for condition in listed {
        let hypothesis = text(&condition["hypothesis"]);
        if !side_conditions
            .iter()
            .any(|binder| text(&binder["name"]) == hypothesis)
        {
            problems.push(
                json!({"kind": "restates-unknown-side-condition", "head": name,
                                 "hypothesis": hypothesis}),
            );
            continue;
        }
        let mut item = json!({"hypothesis": hypothesis, "discharged_by": Value::Null});
        if let Some(discharger) = condition.get("discharged_by").and_then(Value::as_str) {
            item["discharged_by"] = json!(discharger);
            let described = &lemma["dischargers"][hypothesis.as_str()];
            if described.is_null() || described.get("error").is_some() {
                problems.push(
                    json!({"kind": "restates-discharger", "hypothesis": hypothesis,
                    "head": discharger,
                    "detail": described.get("error").cloned().unwrap_or(json!("not described"))}),
                );
            } else {
                if described["matches"] != true {
                    problems.push(
                        json!({"kind": "restates-discharger", "hypothesis": hypothesis,
                        "head": discharger,
                        "detail": "its conclusion does not unify with the hypothesis"}),
                    );
                }
                let unpermitted = disallowed(&described["axioms"]);
                if !unpermitted.is_empty() {
                    problems.push(json!({"kind": "restates-axioms", "hypothesis": hypothesis,
                        "head": discharger, "declarations": unpermitted}));
                }
                item["remaining_hypotheses"] = described["remaining_hypotheses"].clone();
            }
        }
        conditions.push(item);
    }
    summary["side_conditions"] = json!(conditions);
    (problems, summary)
}

fn summary(entries: &[Value]) -> Value {
    let count = |status: &str| {
        entries
            .iter()
            .filter(|entry| entry["status"] == status)
            .count()
    };
    json!({"bound": count("bound"), "pinned": count("pinned"), "mismatch": count("mismatch")})
}

/// The terms' sense constants (term label -> sense id -> Lean declaration)
/// and the senses each definition gives.
type SenseIndex = (
    BTreeMap<String, BTreeMap<String, Option<String>>>,
    HashMap<String, BTreeSet<String>>,
);

fn sense_index(corpus: &Corpus) -> SenseIndex {
    let mut term_constants: BTreeMap<String, BTreeMap<String, Option<String>>> = BTreeMap::new();
    let mut definition_senses: HashMap<String, BTreeSet<String>> = HashMap::new();
    for record in corpus.records("disambiguations") {
        for sense in record
            .get("senses")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let id = text(&sense["id"]);
            term_constants
                .entry(text(field(record, "term_label")))
                .or_default()
                .insert(
                    id.clone(),
                    sense
                        .get("lean_declaration")
                        .filter(|v| !v.is_null())
                        .map(text),
                );
            definition_senses
                .entry(text(&sense["definition_id"]))
                .or_default()
                .insert(id);
        }
    }
    (term_constants, definition_senses)
}

/// The sense constants a described item (binder or result) reaches.
fn reached(item: &Value) -> BTreeSet<String> {
    strings(item.get("senses")).into_iter().collect()
}

/// Python `add_sense_bind_problems` (its per-result part).
fn add_sense_problems(
    _root: &Path,
    corpus: &Corpus,
    statements: &HashMap<&str, &Obj>,
    lookup: &HashMap<&str, &Value>,
    entries: &mut [Value],
) -> Result<(), String> {
    let (term_constants, definition_senses) = sense_index(corpus);
    for entry in entries.iter_mut() {
        if entry["kind"] == "schema-registration" {
            continue;
        }
        let Some(result) = corpus.get("results", &text(&entry["id"])) else {
            continue;
        };
        let argument_id = text(field(&result.fields, "argument_id"));
        let argument = corpus
            .get("arguments", &argument_id)
            .ok_or_else(|| format!("unknown argument {argument_id}"))?;
        if !pyfmt::truthy(argument.fields.get("term_senses")) {
            continue;
        }
        let empty = json!({});
        let theorem = text(field(&result.fields, "theorem"));
        let described = lookup.get(theorem.as_str()).copied().unwrap_or(&empty);
        let problems = sense_problems(
            &argument.fields,
            described,
            statements,
            &term_constants,
            &definition_senses,
            entry,
        );
        if !problems.is_empty() {
            if let Some(list) = entry["problems"].as_array_mut() {
                list.extend(problems);
            }
            entry["status"] = json!("mismatch");
        }
    }
    Ok(())
}

/// Python `sense_bind_problems`.
fn sense_problems(
    argument: &Obj,
    described: &Value,
    statements: &HashMap<&str, &Obj>,
    term_constants: &BTreeMap<String, BTreeMap<String, Option<String>>>,
    definition_senses: &HashMap<String, BTreeSet<String>>,
    binding: &Value,
) -> Vec<Value> {
    let mut problems = Vec::new();
    if described.get("error").is_some()
        || argument.get("sense_mixing_control") == Some(&json!(true))
    {
        return problems;
    }
    // Python's dict comprehension: a repeated name keeps its first position
    // and its last binder.
    let mut binders: Vec<(String, &Value)> = Vec::new();
    for binder in described
        .get("binders")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        if !pyfmt::truthy(binder.get("prop")) {
            continue;
        }
        let name = text(&binder["name"]);
        match binders.iter_mut().find(|(existing, _)| *existing == name) {
            Some(slot) => slot.1 = binder,
            None => binders.push((name, binder)),
        }
    }
    let empty = json!({});
    let mut items: Vec<(String, &Value)> = binders.clone();
    items.push(("result".into(), described.get("result").unwrap_or(&empty)));
    if items.iter().any(|(_, item)| item.get("senses").is_none()) {
        return vec![json!({"kind": "sense-description-missing",
                           "detail": "rerun scripts/BindTypes.lean with sense_theorems"})];
    }
    let mut bound: Vec<(String, String, &Value)> = Vec::new();
    for entry in binding["premises"].as_array().into_iter().flatten() {
        let hypothesis = text(&entry["hypothesis"]);
        let name = hypothesis.split('.').next().unwrap_or_default();
        if let Some((_, binder)) = binders.iter().find(|(existing, _)| existing == name) {
            bound.push((text(&entry["statement_id"]), hypothesis.clone(), binder));
        }
    }
    if pyfmt::truthy(binding.get("conclusion")) {
        let result = items.last().map(|(_, item)| *item).unwrap_or(&empty);
        bound.push((
            text(field(argument, "conclusion_statement_id")),
            "result".into(),
            result,
        ));
    }
    let term_senses = argument
        .get("term_senses")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    let no_constants = BTreeMap::new();
    for (term, sense_id) in &term_senses {
        let sense_id = text(sense_id);
        let constants = term_constants.get(term).unwrap_or(&no_constants);
        let Some(declared) = constants.get(&sense_id).cloned().flatten() else {
            problems.push(
                json!({"kind": "sense-without-lean-declaration", "term": term,
                                 "sense_id": sense_id}),
            );
            continue;
        };
        let others: BTreeSet<&String> = constants
            .iter()
            .filter(|(sid, _)| **sid != sense_id)
            .filter_map(|(_, constant)| constant.as_ref())
            .filter(|constant| !constant.is_empty() && **constant != declared)
            .collect();
        let bridges: Vec<&Value> = argument
            .get("sense_bridges")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter(|bridge| bridge.get("term") == Some(&json!(term)))
            .collect();
        let bridge_heads: BTreeSet<String> = bridges
            .iter()
            .filter(|bridge| bridge.get("role").unwrap_or(&json!("premise")) == "premise")
            .filter_map(|bridge| {
                statements
                    .get(text(&bridge["statement_id"]).as_str())
                    .and_then(|statement| statement.get("lean_declaration"))
                    .filter(|value| !value.is_null())
                    .map(text)
            })
            .collect();
        let conclusion_bridge = bridges
            .iter()
            .any(|bridge| bridge.get("role") == Some(&json!("conclusion")));
        if !items
            .iter()
            .any(|(_, item)| reached(item).contains(&declared))
        {
            problems.push(json!({"kind": "declared-sense-not-mentioned", "term": term,
                                 "constant": declared}));
        }
        for (name, item) in &items {
            if name == "result" && conclusion_bridge {
                continue;
            }
            if name != "result"
                && item
                    .get("head")
                    .and_then(Value::as_str)
                    .is_some_and(|head| bridge_heads.contains(head))
            {
                continue;
            }
            let reached = reached(item);
            let wrong: Vec<&&String> = others.iter().filter(|c| reached.contains(**c)).collect();
            if !wrong.is_empty() {
                problems.push(
                    json!({"kind": "other-sense-mentioned", "term": term, "where": name,
                                     "declared": declared, "constants": wrong}),
                );
            }
        }
        for (statement_id, place, item) in &bound {
            let links: BTreeSet<&String> = statements
                .get(statement_id.as_str())
                .map(|statement| strings(statement.get("definition_ids")))
                .unwrap_or_default()
                .iter()
                .filter_map(|definition| definition_senses.get(definition))
                .flatten()
                .collect();
            if links.contains(&sense_id) && !reached(item).contains(&declared) {
                problems.push(
                    json!({"kind": "statement-sense-not-instantiated", "term": term,
                                     "statement_id": statement_id, "where": place,
                                     "constant": declared}),
                );
            }
        }
    }
    problems
}

/// Python `add_sense_bind_problems` (its alias part): two senses of one
/// disambiguation whose constants are aliases of one canonical constant.
fn sense_aliases(root: &Path, corpus: &Corpus, described: &[Value]) -> Result<Vec<Value>, String> {
    let empty = Map::new();
    let aliases = described
        .iter()
        .find_map(|entry| entry.get("sense_aliases"))
        .and_then(Value::as_object)
        .unwrap_or(&empty);
    let legacy: BTreeSet<String> = match fs::read(root.join(SENSE_ALLOWLIST)) {
        Ok(bytes) => {
            let data: Value = serde_json::from_slice(&bytes)
                .map_err(|error| format!("{SENSE_ALLOWLIST}: {error}"))?;
            strings(data.get("senses_without_lean_declaration"))
                .into_iter()
                .collect()
        }
        Err(_) => BTreeSet::new(),
    };
    let mut problems = Vec::new();
    for record in corpus.records("disambiguations") {
        let mut canonical: BTreeMap<String, String> = BTreeMap::new();
        for sense in record
            .get("senses")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let Some(constant) = sense.get("lean_declaration").and_then(Value::as_str) else {
                continue;
            };
            let Some(target) = aliases.get(constant) else {
                continue;
            };
            if legacy.contains(&text(&sense["id"])) {
                continue;
            }
            let target = text(target);
            if let Some(existing) = canonical.get(&target)
                && existing != constant
            {
                let mut pair = [existing.clone(), constant.to_owned()];
                pair.sort();
                problems.push(json!({"disambiguation_id": record["id"], "constants": pair,
                                     "canonical": target}));
            }
            canonical
                .entry(target)
                .or_insert_with(|| constant.to_owned());
        }
    }
    Ok(problems)
}

/// The text Python prints (before `humanize`), and whether it fails.
pub fn format(report: &Value) -> (String, bool) {
    let mut lines = Vec::new();
    for entry in report["results"].as_array().into_iter().flatten() {
        if entry["status"] == "pinned" {
            for item in entry["undecidable"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "pinned: {}: {} {} has no lean_declaration; Lean type is `{}`",
                    text(&entry["id"]),
                    text(&item["role"]),
                    text(&item["statement_id"]),
                    text(&item["type"])
                ));
            }
        }
        for problem in entry["problems"].as_array().into_iter().flatten() {
            lines.push(format!(
                "mismatch: {}: {}",
                text(&entry["id"]),
                pyfmt::json_dumps(problem, false)
            ));
        }
    }
    for problem in report["sense_aliases"].as_array().into_iter().flatten() {
        lines.push(format!(
            "sense alias: {}",
            pyfmt::json_dumps(problem, false)
        ));
    }
    let summary = &report["summary"];
    lines.push(format!(
        "bind-check: {} bound, {} pinned, {} mismatch",
        summary["bound"], summary["pinned"], summary["mismatch"]
    ));
    for key in report["stale_pins"].as_array().into_iter().flatten() {
        lines.push(format!(
            "stale pin: {} is not used by any result; remove it from PINNED_UNDECLARED_BINDINGS",
            pyfmt::repr(key)
        ));
    }
    (lines.join("\n") + "\n", failed(report))
}

/// Python's exit condition: a mismatch, a stale pin or a sense alias.
pub fn failed(report: &Value) -> bool {
    report["summary"]["mismatch"].as_u64().unwrap_or(0) > 0
        || report["stale_pins"]
            .as_array()
            .is_some_and(|pins| !pins.is_empty())
        || report["sense_aliases"]
            .as_array()
            .is_some_and(|aliases| !aliases.is_empty())
}

/// Python `finite_models.certificate_source`: the Lean file that checks every
/// registered model's exact closed applications, and its theorem names.
pub fn certificate_source(corpus: &Corpus) -> (String, Vec<String>) {
    model_certificate_source(&corpus.records("models"), &statements(corpus))
}

/// [`certificate_source`] for `models` (in order), as Python
/// `certificate_source(models, statements)`.
pub fn model_certificate_source(
    models: &[&Obj],
    statements: &HashMap<&str, &Obj>,
) -> (String, Vec<String>) {
    let modules: BTreeSet<String> = models
        .iter()
        .flat_map(|model| strings(model.get("modules")))
        .collect();
    let mut lines: Vec<String> = modules
        .iter()
        .map(|module| format!("import {module}"))
        .collect();
    lines.push("namespace FiniteModelCertificates".into());
    let mut names = Vec::new();
    let empty = Map::new();
    for (i, model) in models.iter().enumerate() {
        let bindings = model
            .get("bindings")
            .and_then(Value::as_object)
            .unwrap_or(&empty);
        let name = format!("interpretation_{i}");
        lines.push(format!(
            "def {name} := @{}",
            text(field(model, "lean_declaration"))
        ));
        names.push(name);
        for (j, carrier) in model
            .get("carriers")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .enumerate()
        {
            let alternatives: Vec<String> = carrier["elements"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|element| format!("x = ({})", text(element)))
                .collect();
            let name = format!("carrier_{i}_{j}");
            let binding = bindings
                .get(&text(&carrier["binding"]))
                .map(text)
                .unwrap_or_default();
            lines.push(format!(
                "theorem {name} : ∀ x : ({binding}), {} := {}",
                alternatives.join(" ∨ "),
                text(&carrier["theorem"])
            ));
            names.push(name);
        }
        for (j, evaluation) in model
            .get("evaluations")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .enumerate()
        {
            let declaration = statements
                .get(text(&evaluation["statement_id"]).as_str())
                .map(|statement| text(field(statement, "lean_declaration")))
                .unwrap_or_default();
            let arguments: Vec<String> = evaluation["arguments"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|key| {
                    format!(
                        "({})",
                        bindings.get(&text(key)).map(text).unwrap_or_default()
                    )
                })
                .collect();
            let mut proposition = format!("@{declaration} {}", arguments.join(" "));
            if evaluation["value"] == "violates" {
                proposition = format!("¬ ({proposition})");
            }
            let name = format!("evaluation_{i}_{j}");
            lines.push(format!(
                "theorem {name} : {proposition} := {}",
                text(&evaluation["theorem"])
            ));
            names.push(name);
        }
    }
    lines.extend(names.iter().map(|name| format!("#print axioms {name}")));
    lines.push("end FiniteModelCertificates".into());
    (lines.join("\n") + "\n", names)
}

/// Runs `command` in `root` with Python's `subprocess.run(..., timeout=600)`
/// limit, killing its process tree on a timeout; returns (exit success,
/// stdout, stderr).
fn run_limited(
    root: &Path,
    program: &str,
    args: &[&str],
) -> Result<(bool, String, String), String> {
    let mut command = Command::new(program);
    command.args(args).current_dir(root);
    match crate::subprocess::run_bounded(command, MODEL_TIMEOUT) {
        Ok(Some(done)) => Ok((done.success, done.stdout, done.stderr)),
        Ok(None) => {
            let argv: Vec<&str> = std::iter::once(program)
                .chain(args.iter().copied())
                .collect();
            Err(format!(
                "finite model verification unavailable: Command '{}' timed out after 600 seconds",
                pyfmt::repr(&json!(argv))
            ))
        }
        Err(crate::subprocess::Failure::Spawn(error)) => Err(format!(
            "finite model verification unavailable: {}",
            crate::structure::os_error(&error, Path::new(program))
        )),
        Err(crate::subprocess::Failure::Wait(error)) => {
            Err(format!("finite model verification unavailable: {error}"))
        }
    }
}

/// Python `finite_models.verify_models`: builds the models' modules, compiles
/// the certificates and requires each to be zero-axiom.
pub fn verify_models(root: &Path, corpus: &Corpus) -> Result<Value, String> {
    verify_model_records(root, &corpus.records("models"), &statements(corpus))
}

/// [`verify_models`] for `models` (Python `verify_models(models, statements,
/// root)`, as `verify_case` calls it for a profile's eligible witnesses).
pub fn verify_model_records(
    root: &Path,
    models: &[&Obj],
    statements: &HashMap<&str, &Obj>,
) -> Result<Value, String> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let root = &absolute(root);
    if models.is_empty() {
        return Ok(json!({"models": 0, "certificates": 0, "axioms": []}));
    }
    let (source, names) = model_certificate_source(models, statements);
    let file = root.join(format!(
        ".truth-model-certificates-{}-{}.lean",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    fs::write(&file, source)
        .map_err(|error| format!("finite model verification unavailable: {error}"))?;
    let modules: BTreeSet<String> = models
        .iter()
        .flat_map(|model| strings(model.get("modules")))
        .collect();
    let outcome = (|| {
        let mut build_args = vec!["build"];
        build_args.extend(modules.iter().map(String::as_str));
        let (ok, stdout, stderr) = run_limited(root, "lake", &build_args)?;
        if !ok {
            return Err(format!(
                "finite model modules failed to build:\n{stdout}\n{stderr}"
            ));
        }
        let file_name = file.to_string_lossy().into_owned();
        run_limited(root, "lake", &["env", "lean", &file_name])
    })();
    let _ = fs::remove_file(&file);
    let (ok, stdout, stderr) = outcome?;
    if !ok {
        return Err(format!(
            "finite model certificates failed:\n{stdout}\n{stderr}"
        ));
    }
    for name in &names {
        let expected = format!("'FiniteModelCertificates.{name}' does not depend on any axioms");
        if !stdout.contains(&expected) {
            let marker = format!("FiniteModelCertificates.{name}'");
            let lines: Vec<&str> = stdout
                .lines()
                .filter(|line| line.contains(&marker))
                .collect();
            return Err(format!(
                "certificate {name} is not zero-axiom: {}",
                lines.join("\n")
            ));
        }
    }
    Ok(json!({"models": models.len(), "certificates": names.len(), "axioms": []}))
}

/// `root` as an absolute path, so a path built from it still names the same
/// file inside a child process whose working directory is `root` (a relative
/// `--root` other than `.` would otherwise be resolved twice).
pub fn absolute(root: &Path) -> PathBuf {
    fs::canonicalize(root)
        .or_else(|_| std::path::absolute(root))
        .unwrap_or_else(|_| root.to_owned())
}

pub use crate::sha256::sha256_hex;

#[cfg(test)]
mod tests {
    use super::*;

    /// The exporter description of a restating lemma `(∃ s, P s ∧ Q s) ↔ C`
    /// with one propositional binder `h` headed by `held`.
    fn restating_lemma(held: &str, exists_used: u64, matrix: &[&str]) -> Value {
        json!({
            "restating_lemma": "Ns.iff", "kind": "theorem", "axioms": [],
            "binders": [
                {"name": "x", "prop": false, "head": null, "core_head": null},
                {"name": "h", "prop": true, "head": held, "core_head": held, "type": "H x"},
            ],
            "dischargers": {"h": {"declaration": "Ns.discharge", "axioms": ["propext"],
                                  "matches": true, "remaining_hypotheses": ["K x"]}},
            "body_head": "Iff",
            "sides": [
                {"head": "Exists", "exists_binders": 1, "exists_used": exists_used,
                 "matrix": {"head": "And", "used_constants": matrix}, "type": "∃ s, …"},
                {"head": "Ns.C", "exists_binders": 0, "exists_used": 0,
                 "matrix": {"head": "Ns.C", "used_constants": ["Ns.C"]}, "type": "C"},
            ],
        })
    }

    fn kinds(problems: &[Value]) -> Vec<&str> {
        problems.iter().filter_map(|p| p["kind"].as_str()).collect()
    }

    #[test]
    fn restating_lemma_shape_is_checked() {
        let declaration = |id: &str| -> Option<String> {
            match id {
                "P" => Some("Ns.P".into()),
                "Q" => Some("Ns.Q".into()),
                "R" => Some("Ns.R".into()),
                "C" => Some("Ns.C".into()),
                _ => None,
            }
        };
        let argument = json!({"premise_statement_ids": ["P", "Q", "R"],
                              "conclusion_statement_id": "C"});
        let argument = argument.as_object().unwrap();
        let marker = |extra: Value| {
            let mut marker = json!({"lemma": "Ns.iff", "note": "n"});
            for (key, value) in extra.as_object().unwrap() {
                marker[key] = value.clone();
            }
            marker.as_object().cloned().unwrap()
        };
        let permitted: BTreeSet<String> = ["propext".to_owned()].into();
        // P and Q restated, R held fixed as the binder h: bound.
        let lemma = restating_lemma("Ns.R", 1, &["And", "Ns.P", "Ns.Q"]);
        let (problems, summary) = restating_problems(
            &marker(json!({})),
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(problems, Vec::<Value>::new());
        assert_eq!(summary["shape"], "iff");
        assert_eq!(summary["held_premise_ids"], json!(["R"]));
        // h headed by a non-premise is a side condition: unlisted, then listed
        // with a discharger whose axiom the empty policy forbids.
        let lemma = restating_lemma("Ns.H", 1, &["And", "Ns.P", "Ns.Q"]);
        let (problems, _) = restating_problems(
            &marker(json!({"unrestated_premise_ids": ["R"]})),
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(kinds(&problems), ["restates-unlisted-side-condition"]);
        let listed = marker(json!({"unrestated_premise_ids": ["R"],
            "side_conditions": [{"hypothesis": "h", "note": "n", "discharged_by": "Ns.discharge"}]}));
        let (problems, summary) = restating_problems(
            &listed,
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(problems, Vec::<Value>::new());
        assert_eq!(
            summary["side_conditions"][0]["remaining_hypotheses"],
            json!(["K x"])
        );
        let (problems, _) = restating_problems(
            &listed,
            argument,
            &declaration,
            Some(&lemma),
            Some(&BTreeSet::new()),
        );
        assert_eq!(kinds(&problems), ["restates-axioms"]);
        // A missing premise, no used existential, an unrestated premise the
        // lemma mentions, and a lemma the exporter did not describe.
        let lemma = restating_lemma("Ns.R", 0, &["And", "Ns.P"]);
        let (problems, _) = restating_problems(
            &marker(json!({})),
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(
            kinds(&problems),
            ["restates-no-free-parameter", "restates-premise-missing"]
        );
        let lemma = restating_lemma("Ns.H", 1, &["And", "Ns.P", "Ns.Q", "Ns.R"]);
        let (problems, _) = restating_problems(
            &listed,
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(kinds(&problems), ["restates-unrestated-premise-mentioned"]);
        let (problems, _) =
            restating_problems(&marker(json!({})), argument, &declaration, None, None);
        assert_eq!(kinds(&problems), ["restates-lemma-not-described"]);
        // No side of the Iff is the conclusion.
        let mut lemma = restating_lemma("Ns.R", 1, &["And", "Ns.P", "Ns.Q"]);
        lemma["sides"][1]["head"] = json!("Ns.Other");
        let (problems, _) = restating_problems(
            &marker(json!({})),
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(kinds(&problems), ["restates-shape"]);
        // The converse shape: the conclusion as a hypothesis, ∃ … as body.
        let lemma = json!({
            "restating_lemma": "Ns.conv", "kind": "theorem", "axioms": [],
            "binders": [{"name": "c", "prop": true, "head": "Ns.C", "core_head": "Ns.C",
                         "type": "C"}],
            "dischargers": {}, "body_head": "Exists",
            "side": {"head": "Exists", "exists_binders": 1, "exists_used": 1,
                     "matrix": {"head": "And", "used_constants": ["Ns.P", "Ns.Q", "Ns.R"]},
                     "type": "∃ s, …"},
        });
        let (problems, summary) = restating_problems(
            &marker(json!({})),
            argument,
            &declaration,
            Some(&lemma),
            Some(&permitted),
        );
        assert_eq!(problems, Vec::<Value>::new());
        assert_eq!(summary["shape"], "converse");
    }

    #[test]
    fn restating_input_lists_lemmas_and_dischargers() {
        let request = |id: &str, marker: Option<Value>| {
            let mut record = json!({"id": id, "solution_module": "M", "theorem": "t"});
            if let Some(marker) = marker {
                record[RESTATES] = marker;
            }
            Request {
                record: record.as_object().cloned().unwrap(),
                argument: Obj::new(),
                schema: false,
            }
        };
        let requests = [
            request(
                "B",
                Some(json!({"lemma": "Ns.b", "note": "n", "side_conditions": [
                    {"hypothesis": "h", "note": "n", "discharged_by": "Ns.d"},
                    {"hypothesis": "k", "note": "n"}]})),
            ),
            request("A", Some(json!({"lemma": "Ns.a", "note": "n"}))),
            request("C", None),
        ];
        assert_eq!(
            restating_input(&requests),
            vec![
                json!({"lemma": "Ns.a", "dischargers": []}),
                json!({"lemma": "Ns.b", "dischargers": [["h", "Ns.d"]]}),
            ]
        );
    }

    #[test]
    fn absolute_root_survives_a_child_working_directory() {
        let parent = std::env::current_dir().unwrap();
        let relative = Path::new("src");
        let root = absolute(relative);
        assert!(root.is_absolute());
        assert_eq!(root, fs::canonicalize(parent.join("src")).unwrap());
        // The exporter path is the same file whatever the child's directory.
        assert!(root.join("bind_check.rs").is_file());
    }

    #[test]
    fn sha256_matches_known_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let long = vec![b'a'; 1000];
        assert_eq!(
            sha256_hex(&long),
            "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
        );
    }

    #[test]
    fn python_json_strings() {
        assert_eq!(
            pyfmt::json_str("a\"é\u{1F600}\x7f", true),
            "\"a\\\"\\u00e9\\ud83d\\ude00\\u007f\""
        );
        assert_eq!(pyfmt::json_str("é\x01", false), "\"é\\u0001\"");
        assert_eq!(
            pyfmt::json_dumps(&json!({"b": [1, null], "a": "x"}), false),
            "{\"a\": \"x\", \"b\": [1, null]}"
        );
    }
}
