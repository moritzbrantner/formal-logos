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
    process::{Command, Stdio},
    time::{Duration, Instant},
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
        "{{\"modules\": {}, \"theorems\": {}, \"bundle_prefixes\": {}, \"sense_constants\": {}, \"sense_theorems\": {}",
        list(&mut modules.iter()),
        list(&mut theorems.iter()),
        list(&mut prefixes.iter()),
        list(&mut sense_constants.iter()),
        list(&mut sense_theorems.iter()),
    );
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
    let root = &absolute(root);
    let path = std::env::temp_dir().join(format!(
        "truth-bind-check-{}-{}.json",
        std::process::id(),
        Instant::now().elapsed().as_nanos()
    ));
    fs::write(&path, input).map_err(|error| format!("cannot write the exporter input: {error}"))?;
    let tool = root.join(BIND_TOOL);
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
            return Err("bind-check needs `lake` on PATH (run after `lake build`)".into());
        }
        Err(error) => return Err(format!("cannot run {BIND_TOOL}: {error}")),
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
            "{BIND_TOOL} failed (exit {}):\n{detail}",
            output.status.code().unwrap_or(-1)
        ));
    }
    match serde_json::from_slice::<Value>(&output.stdout) {
        Ok(Value::Array(items)) => Ok(items),
        Ok(_) => Err(format!("{BIND_TOOL} must print a JSON array")),
        Err(error) => Err(format!("{BIND_TOOL} printed invalid JSON: {error}")),
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
    let models = corpus.records("models");
    let statements = statements(corpus);
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
/// limit; returns (exit success, stdout, stderr).
fn run_limited(
    root: &Path,
    program: &str,
    args: &[&str],
) -> Result<(bool, String, String), String> {
    let scratch = std::env::temp_dir();
    let tag = format!("truth-models-{}-{}", std::process::id(), args.len());
    let out_path = scratch.join(format!("{tag}.out"));
    let err_path = scratch.join(format!("{tag}.err"));
    let spawn = || -> std::io::Result<std::process::Child> {
        Command::new(program)
            .args(args)
            .current_dir(root)
            .stdin(Stdio::null())
            .stdout(fs::File::create(&out_path)?)
            .stderr(fs::File::create(&err_path)?)
            .spawn()
    };
    let mut child =
        spawn().map_err(|error| format!("finite model verification unavailable: {error}"))?;
    let start = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if start.elapsed() > MODEL_TIMEOUT => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = fs::remove_file(&out_path);
                let _ = fs::remove_file(&err_path);
                return Err(format!(
                    "finite model verification unavailable: Command '{program} {}' timed out after 600 seconds",
                    args.join(" ")
                ));
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(50)),
            Err(error) => return Err(format!("finite model verification unavailable: {error}")),
        }
    };
    let read =
        |path: &Path| String::from_utf8_lossy(&fs::read(path).unwrap_or_default()).into_owned();
    let (stdout, stderr) = (read(&out_path), read(&err_path));
    let _ = fs::remove_file(&out_path);
    let _ = fs::remove_file(&err_path);
    Ok((status.success(), stdout, stderr))
}

/// Python `finite_models.verify_models`: builds the models' modules, compiles
/// the certificates and requires each to be zero-axiom.
pub fn verify_models(root: &Path, corpus: &Corpus) -> Result<Value, String> {
    let root = &absolute(root);
    let models = corpus.records("models");
    if models.is_empty() {
        return Ok(json!({"models": 0, "certificates": 0, "axioms": []}));
    }
    let (source, names) = certificate_source(corpus);
    let file = root.join(format!(
        ".truth-model-certificates-{}.lean",
        std::process::id()
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

/// SHA-256 as lowercase hex (FIPS 180-4).
pub fn sha256_hex(bytes: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut message = bytes.to_vec();
    let bits = (bytes.len() as u64).wrapping_mul(8);
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&bits.to_be_bytes());
    for block in message.chunks(64) {
        let mut w = [0u32; 64];
        for (i, word) in block.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(value);
        }
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

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
