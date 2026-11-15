//! Python `scripts/strength_comparisons.py`: the evidence-backed
//! `strength_comparison` presentation behind `corpus.py strength-comparisons`
//! and `strength-report`.
//!
//! Rust only orchestrates. It validates registrations (through the shared
//! `check` rules), builds the modules with Lake, runs the Lean exporters
//! `scripts/BindTypes.lean`, `scripts/CheckStrength.lean` and
//! `scripts/PropositionStructure.lean` and `scripts/verify-result.sh` through
//! `scripts/worker_env.py`, and assembles the same reports and bundle, byte for
//! byte, as Python. Lean's definitional-equality binding and degeneracy guard,
//! Comparator and NanoDa stay the authorities: nothing here reimplements a
//! verdict, and a freshness check is never fresh proof execution.

use crate::{
    Corpus, bind_check,
    check::{result_config, validate_strength_comparison},
    pyfmt,
    pyjson::Ordered,
    structure::{self, Extractor, Records, Sources, os_error},
};
use serde_json::{Map, Number, Value};
use std::{
    collections::{BTreeSet, HashMap},
    fs,
    path::{Component, Path, PathBuf},
    time::Duration,
};

pub const PREDICATE: &str = "strength_comparison";
pub const SCHEMA_VERSION: i128 = 2;
/// The default `strength-report --output`.
pub const DEFAULT_OUTPUT: &str = ".cache/strength-comparisons.json";
/// The roles whose certificates make a delta exact, sorted.
const EXACT_DELTA_ROLES: [&str; 4] = [
    "delta_forward",
    "equivalence",
    "implication",
    "reconstruction",
];
pub const TRUST: &str = "Trusted live producer; freshness validation is not fresh proof execution. Existing result verifiers remain authoritative.";
const SCOPE_NOTES: [&str; 7] = [
    "Comparison is under the displayed shared background and vocabulary, not the entire theorem environment.",
    "Exact factorization S ↔ (W ∧ D) does not certify that D is informative: even S ∧ True can be an exact factorization.",
    "The degeneracy guard detects only definitional matches to S, W → S, W or True; a negative check proves no semantic nonredundancy.",
    "A checked separating instance refutes the general converse under this comparison, not the converse for every fixed domain or interpretation. Current examples use Type 0; closed settings need not use universe zero.",
    "D is a proposed additional requirement; W ∧ ¬S denotes cases admitted only by W. They are distinct roles.",
    "No unique or minimal delta is claimed. Proof-term use does not establish premise necessity.",
    "The artifact is derived presentation; corpus results, Comparator and NanoDa remain the proof authorities.",
];
/// `configuration_explorer.INPUT_FILES`.
const CONFIGURATION_FILES: [&str; 16] = [
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
/// `configuration_explorer.INPUT_DIRECTORIES`: directory and file pattern
/// (`*` + suffix, or an exact name).
const CONFIGURATION_DIRECTORIES: [(&str, &str); 8] = [
    ("TruthCore", "*.lean"),
    ("results", "comparator.json"),
    ("verifier/src", "*.rs"),
    ("corpus/statements", "*.json"),
    ("corpus/arguments", "*.json"),
    ("corpus/results", "*.json"),
    ("corpus/models", "*.json"),
    ("corpus/configurations", "*.json"),
];
/// The relation-interpretation inputs `input_manifest` adds.
const STRENGTH_FILES: [&str; 5] = [
    "scripts/strength_comparisons.py",
    "scripts/CheckStrength.lean",
    "scripts/proposition_structure.py",
    "scripts/PropositionStructure.lean",
    "scripts/worker_env.py",
];
const STRENGTH_KINDS: [&str; 5] = [
    "relations",
    "inferences",
    "definitions",
    "disambiguations",
    "claims",
];
const TIMEOUT: Duration = Duration::from_secs(1200);

// ---------------------------------------------------------------------------
// Python value semantics over `Ordered`

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

/// Python `str(KeyError(key))`.
fn key_error(key: &str) -> String {
    pyfmt::repr_str(key)
}

/// Python `record[key]`.
fn required<'a>(value: &'a Ordered, key: &str) -> Result<&'a Ordered, String> {
    value.get(key).ok_or_else(|| key_error(key))
}

fn text<'a>(value: &'a Ordered, key: &str) -> &'a str {
    match value.get(key) {
        Some(Ordered::String(text)) => text,
        _ => "",
    }
}

/// Python truthiness of `value.get(key)`.
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

/// Python `value is True`.
fn is_true(value: Option<&Ordered>) -> bool {
    matches!(value, Some(Ordered::Bool(true)))
}

/// Python `==` on JSON-loaded values: dicts ignore key order, and `True`,
/// `1` and `1.0` are equal.
pub fn py_eq(left: &Ordered, right: &Ordered) -> bool {
    fn number(value: &Ordered) -> Option<f64> {
        match value {
            Ordered::Bool(flag) => Some(f64::from(u8::from(*flag))),
            Ordered::Int(number) => Some(*number as f64),
            Ordered::Float(number) => Some(*number),
            _ => None,
        }
    }
    match (left, right) {
        (Ordered::Null, Ordered::Null) => true,
        (Ordered::String(a), Ordered::String(b)) => a == b,
        (Ordered::Int(a), Ordered::Int(b)) => a == b,
        (Ordered::Bool(a), Ordered::Bool(b)) => a == b,
        (Ordered::Array(a), Ordered::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| py_eq(a, b))
        }
        (Ordered::Object(a), Ordered::Object(b)) => {
            let other: HashMap<&str, &Ordered> =
                b.iter().map(|(key, value)| (key.as_str(), value)).collect();
            let keys: std::collections::HashSet<&str> =
                a.iter().map(|(key, _)| key.as_str()).collect();
            keys.len() == other.len()
                && a.iter().all(|(key, value)| {
                    other
                        .get(key.as_str())
                        .is_some_and(|other| py_eq(value, other))
                })
        }
        (a, b) => match (number(a), number(b)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        },
    }
}

/// Python `value.get(key) == other`, with a missing key as `None`.
fn get_eq(value: &Ordered, key: &str, other: &Ordered) -> bool {
    py_eq(value.get(key).unwrap_or(&Ordered::Null), other)
}

/// Python `{**record, key: value, ...}`: each key keeps its position.
fn merged(record: &Ordered, updates: Vec<(&str, Ordered)>) -> Ordered {
    let mut entries = match record {
        Ordered::Object(entries) => entries.clone(),
        _ => Vec::new(),
    };
    for (key, value) in updates {
        match entries.iter_mut().find(|(name, _)| name == key) {
            Some(entry) => entry.1 = value,
            None => entries.push((key.to_owned(), value)),
        }
    }
    Ordered::Object(entries)
}

fn object_entries(value: Option<&Ordered>) -> &[(String, Ordered)] {
    match value {
        Some(Ordered::Object(entries)) => entries,
        _ => &[],
    }
}

fn array(value: Option<&Ordered>) -> &[Ordered] {
    match value {
        Some(Ordered::Array(items)) => items,
        _ => &[],
    }
}

/// `value` with every object's keys sorted (`json.dumps(sort_keys=True)`).
fn sorted_keys(value: &Ordered) -> Ordered {
    match value {
        Ordered::Array(items) => Ordered::Array(items.iter().map(sorted_keys).collect()),
        Ordered::Object(entries) => {
            let mut entries: Vec<(String, Ordered)> = entries
                .iter()
                .map(|(key, item)| (key.clone(), sorted_keys(item)))
                .collect();
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            Ordered::Object(entries)
        }
        scalar => scalar.clone(),
    }
}

/// The `serde_json` value of a loaded record, for the shared `check` rules.
fn plain(value: &Ordered) -> Value {
    match value {
        Ordered::Null => Value::Null,
        Ordered::Bool(flag) => Value::Bool(*flag),
        Ordered::Int(number) => i64::try_from(*number)
            .map(Number::from)
            .ok()
            .or_else(|| u64::try_from(*number).ok().map(Number::from))
            .or_else(|| Number::from_f64(*number as f64))
            .map_or(Value::Null, Value::Number),
        Ordered::Float(number) => Number::from_f64(*number).map_or(Value::Null, Value::Number),
        Ordered::String(text) => Value::String(text.clone()),
        Ordered::Array(items) => Value::Array(items.iter().map(plain).collect()),
        Ordered::Object(entries) => Value::Object(
            entries
                .iter()
                .map(|(key, item)| (key.clone(), plain(item)))
                .collect(),
        ),
    }
}

fn ordered(value: &Value) -> Ordered {
    match value {
        Value::Null => Ordered::Null,
        Value::Bool(flag) => Ordered::Bool(*flag),
        Value::Number(number) => match (number.as_i64(), number.as_u64()) {
            (Some(number), _) => Ordered::Int(number.into()),
            (_, Some(number)) => Ordered::Int(number.into()),
            _ => Ordered::Float(number.as_f64().unwrap_or(f64::NAN)),
        },
        Value::String(text) => Ordered::String(text.clone()),
        Value::Array(items) => Ordered::Array(items.iter().map(ordered).collect()),
        Value::Object(entries) => Ordered::Object(
            entries
                .iter()
                .map(|(key, item)| (key.clone(), ordered(item)))
                .collect(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Context

/// Python `{r["id"]: r for _, r in load_dir(kind)}`: first position, last value.
#[derive(Default)]
struct Table {
    order: Vec<String>,
    by_id: HashMap<String, Ordered>,
}

impl Table {
    fn load(records: &Records, kind: &str) -> Result<Self, String> {
        let mut table = Table::default();
        for record in records.of(kind) {
            let id = match required(record, "id")? {
                Ordered::String(id) => id.clone(),
                other => other.dumps(None),
            };
            if table.by_id.insert(id.clone(), record.clone()).is_none() {
                table.order.push(id);
            }
        }
        Ok(table)
    }

    fn get(&self, id: &str) -> Result<&Ordered, String> {
        self.by_id.get(id).ok_or_else(|| key_error(id))
    }

    fn values(&self) -> impl Iterator<Item = &Ordered> {
        self.order.iter().filter_map(|id| self.by_id.get(id))
    }

    fn plain(&self) -> HashMap<String, Map<String, Value>> {
        self.by_id
            .iter()
            .map(|(id, record)| {
                let fields = match plain(record) {
                    Value::Object(fields) => fields,
                    _ => Map::new(),
                };
                (id.clone(), fields)
            })
            .collect()
    }
}

/// Python `context`: the loaded records, the registered comparisons in id
/// order and the Comparator configuration of every result they select.
pub struct Data {
    statements: Table,
    results: Table,
    definitions: Table,
    disambiguations: Table,
    /// The `strength_comparison` relations, by id.
    pub comparisons: Vec<Ordered>,
    configs: HashMap<String, Ordered>,
}

/// The result ids a comparison selects: evidence, controls and separator.
fn selected_results(relation: &Ordered) -> Vec<String> {
    let mut ids: Vec<String> = Vec::new();
    for value in object_entries(relation.get("evidence_result_ids"))
        .iter()
        .map(|(_, rid)| rid)
        .chain(array(relation.get("explanatory_control_result_ids")))
        .chain(relation.get("separator").and_then(|s| s.get("result_id")))
    {
        if let Ordered::String(rid) = value {
            ids.push(rid.clone());
        }
    }
    ids
}

fn borrowed(table: &HashMap<String, Map<String, Value>>) -> HashMap<&str, &Map<String, Value>> {
    table
        .iter()
        .map(|(id, fields)| (id.as_str(), fields))
        .collect()
}

impl Data {
    /// Python `context(root, load_dir)`.
    pub fn load(root: &Path, records: &Records) -> Result<Self, String> {
        let statements = Table::load(records, "statements")?;
        let results = Table::load(records, "results")?;
        let arguments = Table::load(records, "arguments")?;
        let relations = Table::load(records, "relations")?;
        let definitions = Table::load(records, "definitions")?;
        let disambiguations = Table::load(records, "disambiguations")?;
        let mut comparisons: Vec<Ordered> = relations
            .values()
            .filter(|relation| text(relation, "predicate") == PREDICATE)
            .cloned()
            .collect();
        comparisons.sort_by(|a, b| text(a, "id").cmp(text(b, "id")));
        let (plain_statements, plain_results, plain_arguments) =
            (statements.plain(), results.plain(), arguments.plain());
        let (s, r, a) = (
            borrowed(&plain_statements),
            borrowed(&plain_results),
            borrowed(&plain_arguments),
        );
        let validate = |configs: Option<&HashMap<String, Map<String, Value>>>| {
            comparisons.iter().try_for_each(|relation| {
                let fields = match plain(relation) {
                    Value::Object(fields) => fields,
                    _ => Map::new(),
                };
                validate_strength_comparison(&fields, &s, &r, &a, configs)
            })
        };
        validate(None)?;
        let selected: BTreeSet<String> = comparisons.iter().flat_map(selected_results).collect();
        let argument_ids: HashMap<String, usize> = arguments
            .order
            .iter()
            .enumerate()
            .map(|(index, id)| (id.clone(), index))
            .collect();
        let mut configs = HashMap::new();
        for rid in &selected {
            let result = r.get(rid.as_str()).ok_or_else(|| key_error(rid))?;
            let config = result_config(
                root,
                &format!("corpus/results/{rid}.json"),
                result,
                &argument_ids,
            )?;
            configs.insert(rid.clone(), config);
        }
        validate(Some(&configs))?;
        let configs = configs
            .iter()
            .map(|(rid, config)| (rid.clone(), ordered(&Value::Object(config.clone()))))
            .collect();
        Ok(Data {
            statements,
            results,
            definitions,
            disambiguations,
            comparisons,
            configs,
        })
    }

    fn declaration(&self, sid: &str) -> Result<&Ordered, String> {
        required(self.statements.get(sid)?, "lean_declaration")
    }
}

// ---------------------------------------------------------------------------
// Projection

/// Python `{role: data["statements"][relation[field]]["lean_declaration"]}`
/// for every bound field, in Python's insertion order.
fn field_declarations(relation: &Ordered, data: &Data) -> Result<Vec<(String, Ordered)>, String> {
    let mut declarations = Vec::new();
    for (role, field) in [
        ("stronger", "subject_id"),
        ("weaker", "object_id"),
        ("delta", "delta_statement_id"),
    ] {
        declarations.push((
            role.to_owned(),
            data.declaration(text(relation, field))?.clone(),
        ));
    }
    for (index, sid) in array(relation.get("background_statement_ids"))
        .iter()
        .enumerate()
    {
        let sid = match sid {
            Ordered::String(sid) => sid.as_str(),
            _ => "",
        };
        declarations.push((
            format!("background.{index}"),
            data.declaration(sid)?.clone(),
        ));
    }
    if truthy(relation.get("remainder_statement_id")) {
        declarations.push((
            "remainder".to_owned(),
            data.declaration(text(relation, "remainder_statement_id"))?
                .clone(),
        ));
    }
    Ok(declarations)
}

/// Python `validate_binding`: refuses incomplete checker responses; equality
/// itself remains Lean's job.
pub fn validate_binding(relation: &Ordered, data: &Data, binding: &Ordered) -> Result<(), String> {
    let id = text(relation, "id");
    if !matches!(binding, Ordered::Object(_))
        || !is_true(binding.get("bound"))
        || !get_eq(binding, "id", required(relation, "id")?)
        || !get_eq(
            binding,
            "specification",
            required(relation, "comparison_spec")?,
        )
    {
        return Err(format!(
            "{id}: complete theorem application/background mismatch: {}",
            structure::repr(binding)
        ));
    }
    let expected = object_entries(relation.get("evidence_result_ids"));
    let certificates = array(binding.get("certificates"));
    let roles: BTreeSet<Option<&str>> = certificates
        .iter()
        .map(|certificate| match certificate.get("role") {
            Some(Ordered::String(role)) => Some(role.as_str()),
            _ => None,
        })
        .collect();
    let expected_roles: BTreeSet<Option<&str>> = expected
        .iter()
        .map(|(role, _)| Some(role.as_str()))
        .collect();
    if certificates.len() != expected.len() || roles != expected_roles {
        return Err(format!("{id}: incomplete certificate role bindings"));
    }
    for certificate in certificates {
        let role = text(certificate, "role");
        let rid = expected
            .iter()
            .rev()
            .find(|(name, _)| name == role)
            .map(|(_, rid)| rid)
            .ok_or_else(|| key_error(role))?;
        let rid = match rid {
            Ordered::String(rid) => rid.as_str(),
            _ => "",
        };
        let theorem = required(data.results.get(rid)?, "theorem")?;
        if !is_true(certificate.get("bound")) || !get_eq(certificate, "theorem", theorem) {
            return Err(format!("{id}: mismatched certificate arguments/theorem"));
        }
    }
    let declarations = field_declarations(relation, data)?;
    let fields = array(binding.get("field_bindings"));
    let field_roles: BTreeSet<Option<&str>> = fields
        .iter()
        .map(|field| match field.get("role") {
            Some(Ordered::String(role)) => Some(role.as_str()),
            _ => None,
        })
        .collect();
    let declared_roles: BTreeSet<Option<&str>> = declarations
        .iter()
        .map(|(role, _)| Some(role.as_str()))
        .collect();
    if fields.len() != declarations.len() || field_roles != declared_roles {
        return Err(format!("{id}: incomplete statement/background bindings"));
    }
    let maps = required(relation, "statement_parameter_indices")?;
    for field in fields {
        let role = text(field, "role");
        let declaration = declarations
            .iter()
            .find(|(name, _)| name == role)
            .map(|(_, declaration)| declaration)
            .ok_or_else(|| key_error(role))?;
        if !is_true(field.get("bound"))
            || !get_eq(field, "declaration", declaration)
            || !get_eq(field, "parameter_indices", required(maps, role)?)
            || !truthy(field.get("expected_application"))
        {
            return Err(format!("{id}: mismatched statement/background binding"));
        }
    }
    if truthy(relation.get("separator")) {
        let expected = required(relation, "separator")?;
        let separator = binding.get("separator").unwrap_or(&Ordered::Null);
        let result = data
            .results
            .get(text(required(relation, "separator")?, "result_id"))?;
        if !is_true(separator.get("bound"))
            || !get_eq(separator, "setting", required(expected, "setting")?)
            || !get_eq(separator, "theorem", required(result, "theorem")?)
        {
            return Err(format!(
                "{id}: unsupported strictness without same-background separating application"
            ));
        }
    }
    Ok(())
}

/// Python `projection`: only checked roles produce claims; a sufficient
/// condition is never exact content.
pub fn projection(
    relation: &Ordered,
    data: &Data,
    binding: Option<&Ordered>,
    verified: bool,
) -> Result<Ordered, String> {
    if verified {
        validate_binding(relation, data, binding.unwrap_or(&Ordered::Null))?;
    }
    let id = text(relation, "id");
    let evidence = object_entries(relation.get("evidence_result_ids"));
    let roles: BTreeSet<&str> = if verified {
        evidence.iter().map(|(role, _)| role.as_str()).collect()
    } else {
        BTreeSet::new()
    };
    let implied = roles.contains("implication") || roles.contains("equivalence");
    let separated = !matches!(relation.get("separator"), None | Some(Ordered::Null));
    let strict = implied && separated;
    let equivalent = implied && roles.contains("converse");
    if strict && equivalent {
        return Err(format!(
            "{id}: contradictory converse and separating evidence"
        ));
    }
    let exact = roles.contains("equivalence")
        || ["implication", "delta_forward", "reconstruction"]
            .iter()
            .all(|role| roles.contains(role));
    if exact
        && binding.is_some_and(|binding| truthy(Some(binding)))
        && truthy(binding.and_then(|binding| binding.get("delta_degenerate")))
    {
        return Err(format!(
            "{id}: delta is definitionally S, W → S, W or True, excluded by the definitional degeneracy guard; explanatory usefulness is not certified"
        ));
    }
    let mut bound_by_role: HashMap<&str, &Ordered> = HashMap::new();
    for certificate in array(binding.and_then(|binding| binding.get("certificates"))) {
        required(certificate, "role")?;
        bound_by_role.insert(text(certificate, "role"), certificate);
    }
    let mut sorted_evidence: Vec<&(String, Ordered)> = evidence.iter().collect();
    sorted_evidence.sort_by(|a, b| a.0.cmp(&b.0));
    let empty = Ordered::Object(Vec::new());
    let mut obligations = Vec::new();
    for (role, rid) in sorted_evidence {
        let rid_text = match rid {
            Ordered::String(rid) => rid.as_str(),
            _ => "",
        };
        let result = data.results.get(rid_text)?;
        let permitted = data
            .configs
            .get(rid_text)
            .and_then(|config| config.get("permitted_axioms"))
            .cloned()
            .unwrap_or(Ordered::Array(Vec::new()));
        obligations.push(merged(
            bound_by_role.get(role.as_str()).copied().unwrap_or(&empty),
            vec![
                ("role", string(role)),
                ("result_id", rid.clone()),
                ("argument_id", required(result, "argument_id")?.clone()),
                ("theorem", required(result, "theorem")?.clone()),
                ("verified", Ordered::Bool(verified)),
                ("permitted_axioms", permitted),
            ],
        ));
    }
    let mut statement_ids: Vec<&Ordered> = Vec::new();
    for field in ["subject_id", "object_id", "delta_statement_id"] {
        statement_ids.push(required(relation, field)?);
    }
    statement_ids.extend(array(relation.get("background_statement_ids")));
    if truthy(relation.get("remainder_statement_id")) {
        statement_ids.push(required(relation, "remainder_statement_id")?);
    }
    let mut statements = Vec::new();
    for sid in statement_ids {
        let sid = match sid {
            Ordered::String(sid) => sid.as_str(),
            _ => "",
        };
        statements.push(data.statements.get(sid)?);
    }
    let links = |statement: &Ordered, key: &str, id: &Ordered| {
        array(statement.get(key)).iter().any(|item| py_eq(item, id))
    };
    let mut definitions = Vec::new();
    for definition in data.definitions.values() {
        let id = required(definition, "id")?;
        if statements
            .iter()
            .any(|statement| links(statement, "definition_ids", id))
        {
            definitions.push(definition.clone());
        }
    }
    let definition_ids: Vec<&Ordered> = definitions
        .iter()
        .filter_map(|definition| definition.get("id"))
        .collect();
    let mut disambiguations = Vec::new();
    for disambiguation in data.disambiguations.values() {
        let senses = array(disambiguation.get("sense_definition_ids"));
        let id = required(disambiguation, "id")?;
        if senses
            .iter()
            .any(|sense| definition_ids.iter().any(|id| py_eq(id, sense)))
            || statements
                .iter()
                .any(|statement| links(statement, "disambiguation_ids", id))
        {
            disambiguations.push(disambiguation.clone());
        }
    }
    let mut controls = Vec::new();
    for rid in array(relation.get("explanatory_control_result_ids")) {
        let result = data.results.get(match rid {
            Ordered::String(rid) => rid,
            _ => "",
        })?;
        controls.push(object(vec![
            ("result_id", rid.clone()),
            ("argument_id", required(result, "argument_id")?.clone()),
            ("theorem", required(result, "theorem")?.clone()),
            ("description", required(result, "description")?.clone()),
        ]));
    }
    let remaining: Vec<&str> = if exact {
        Vec::new()
    } else {
        EXACT_DELTA_ROLES
            .iter()
            .copied()
            .filter(|role| !roles.contains(role))
            .collect()
    };
    let status = |value: &str| string(value);
    let mut report = vec![
        ("id", required(relation, "id")?.clone()),
        (
            "stronger_statement_id",
            required(relation, "subject_id")?.clone(),
        ),
        (
            "weaker_statement_id",
            required(relation, "object_id")?.clone(),
        ),
        (
            "delta_statement_id",
            required(relation, "delta_statement_id")?.clone(),
        ),
        (
            "background_statement_ids",
            required(relation, "background_statement_ids")?.clone(),
        ),
        (
            "comparison_spec",
            required(relation, "comparison_spec")?.clone(),
        ),
        ("note", required(relation, "note")?.clone()),
        ("verified", Ordered::Bool(verified)),
        (
            "comparison_status",
            status(if strict {
                "strict strengthening"
            } else if equivalent {
                "proved equivalence"
            } else if implied {
                "proved implication"
            } else {
                "unresolved"
            }),
        ),
        (
            "converse_status",
            status(if strict {
                "refuted by separating setting"
            } else if roles.contains("converse") {
                "proved"
            } else {
                "unresolved"
            }),
        ),
        (
            "delta_status",
            status(if exact {
                "exact factorization proved"
            } else if roles.contains("reconstruction") {
                "sufficient only; exactness unresolved"
            } else {
                "unresolved"
            }),
        ),
        ("explanatory_controls", Ordered::Array(controls)),
        (
            "explanatory_status",
            status(
                "reviewed interpretation; informative explanation is not certified by factorization",
            ),
        ),
        ("obligations", Ordered::Array(obligations)),
        ("binding", binding.cloned().unwrap_or(Ordered::Null)),
        ("remaining_obligations", string_list(remaining)),
        ("definitions", Ordered::Array(definitions)),
        ("disambiguations", Ordered::Array(disambiguations)),
        ("scope_notes", string_list(SCOPE_NOTES)),
    ];
    if truthy(relation.get("remainder_statement_id")) {
        report.push((
            "remainder_statement_id",
            required(relation, "remainder_statement_id")?.clone(),
        ));
        report.push((
            "remainder_status",
            status(
                if roles.contains("allowed_cases") && roles.contains("remainder_identity") {
                    "exact admitted-only remainder proved"
                } else {
                    "unresolved"
                },
            ),
        ));
    }
    let separator = relation.get("separator").filter(|s| truthy(Some(s)));
    if let Some(separator) = separator {
        let result = data.results.get(text(separator, "result_id"))?;
        let bound = binding
            .and_then(|binding| binding.get("separator"))
            .filter(|bound| truthy(Some(bound)))
            .unwrap_or(&empty);
        let mut value = merged(separator, Vec::new());
        if let Ordered::Object(entries) = bound {
            value = merged(
                &value,
                entries
                    .iter()
                    .map(|(key, item)| (key.as_str(), item.clone()))
                    .collect(),
            );
        }
        report.push((
            "separator",
            merged(
                &value,
                vec![
                    ("theorem", required(result, "theorem")?.clone()),
                    ("verified", Ordered::Bool(verified)),
                ],
            ),
        ));
    }
    if verified {
        let ids: BTreeSet<String> = evidence
            .iter()
            .filter_map(|(_, rid)| match rid {
                Ordered::String(rid) => Some(rid.clone()),
                _ => None,
            })
            .chain(separator.map(|separator| text(separator, "result_id").to_owned()))
            .collect();
        report.push((
            "provenance",
            object(vec![
                ("result_ids", string_list(ids)),
                ("bind_check", string("bound")),
                ("semantic_binding", string("definitional equality")),
                ("comparator", string("passed")),
            ]),
        ));
    }
    Ok(object(report))
}

// ---------------------------------------------------------------------------
// Live verification

/// Where the Lean outputs come from.
pub enum Exporters<'a> {
    /// Build with Lake, run the exporters and `scripts/verify-result.sh`.
    Lean,
    /// Recorded exporter stdouts (`BindTypes.json`, `CheckStrength.json`,
    /// `PropositionStructure.json`) in this directory: no Lean, no Lake and
    /// no Comparator run. Parity replay only; never a verification.
    Recorded(&'a Path),
}

impl Exporters<'_> {
    fn recorded(&self, tool: &str) -> Option<Result<String, String>> {
        match self {
            Exporters::Lean => None,
            Exporters::Recorded(directory) => {
                let stem = tool
                    .trim_start_matches("scripts/")
                    .trim_end_matches(".lean");
                let path = directory.join(format!("{stem}.json"));
                Some(fs::read_to_string(&path).map_err(|error| os_error(&error, &path)))
            }
        }
    }
}

fn python_list(items: &[String]) -> String {
    format!(
        "[{}]",
        items
            .iter()
            .map(|item| pyfmt::repr_str(item))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// Python `run`: `command` through `scripts/worker_env.py`, failing on a
/// nonzero exit; returns its stdout.
fn run(root: &Path, command: &[String]) -> Result<String, String> {
    let full: Vec<String> = ["scripts/worker_env.py", "--"]
        .iter()
        .map(|part| part.to_string())
        .chain(command.iter().cloned())
        .collect();
    let finished = structure::run_bounded(root, "python3", &full, TIMEOUT)
        .map_err(|error| format!("strength verification unavailable: {error}"))?;
    let Some(finished) = finished else {
        let mut shown = vec!["python3".to_owned()];
        shown.extend(full);
        return Err(format!(
            "strength verification unavailable: Command '{}' timed out after {} seconds",
            python_list(&shown),
            TIMEOUT.as_secs()
        ));
    };
    if !finished.success {
        return Err(format!(
            "strength verification failed ({}):\n{}\n{}",
            python_list(command),
            finished.stdout,
            finished.stderr
        ));
    }
    Ok(finished.stdout)
}

/// Python `json_tool`: runs a Lean exporter on `request` and parses its JSON.
fn json_tool(
    root: &Path,
    tool: &str,
    request: &str,
    exporters: &Exporters,
) -> Result<Ordered, String> {
    let stdout = match exporters.recorded(tool) {
        Some(recorded) => recorded?,
        None => {
            static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let input = std::env::temp_dir().join(format!(
                "truth-strength-{}-{}.json",
                std::process::id(),
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            ));
            fs::write(&input, request).map_err(|error| os_error(&error, &input))?;
            let command: Vec<String> = ["lake", "env", "lean", "--run", tool]
                .iter()
                .map(|part| part.to_string())
                .chain([input.display().to_string()])
                .collect();
            let output = run(root, &command);
            let _ = fs::remove_file(&input);
            output?
        }
    };
    structure::parse(&stdout)
        .map_err(|_| format!("{tool} did not return JSON: {}", pyfmt::head(&stdout, 500)))
}

/// Python `checker_request`: the modules to build and the
/// `scripts/CheckStrength.lean` request.
fn checker_request(
    sources: &Sources,
    relations: &[Ordered],
    data: &Data,
) -> Result<Ordered, String> {
    let mut modules: BTreeSet<String> = BTreeSet::new();
    let module = |value: &Ordered| -> String {
        match value {
            Ordered::String(text) => text.clone(),
            other => other.dumps(None),
        }
    };
    let mut comparisons = Vec::new();
    for relation in relations {
        for rid in array(relation.get("explanatory_control_result_ids")) {
            let result = data.results.get(match rid {
                Ordered::String(rid) => rid,
                _ => "",
            })?;
            modules.insert(module(required(result, "solution_module")?));
        }
        let spec = required(relation, "comparison_spec")?;
        modules.insert(sources.module_for(text(relation, "comparison_spec"))?);
        let mut evidence: Vec<&(String, Ordered)> =
            object_entries(relation.get("evidence_result_ids"))
                .iter()
                .collect();
        evidence.sort_by(|a, b| a.0.cmp(&b.0));
        let mut certificates = Vec::new();
        for (role, rid) in evidence {
            let result = data.results.get(match rid {
                Ordered::String(rid) => rid,
                _ => "",
            })?;
            modules.insert(module(required(result, "solution_module")?));
            certificates.push(object(vec![
                ("role", string(role)),
                ("theorem", required(result, "theorem")?.clone()),
            ]));
        }
        let mut declarations = Vec::new();
        for (role, field) in [
            ("stronger", "subject_id"),
            ("weaker", "object_id"),
            ("delta", "delta_statement_id"),
        ] {
            declarations.push((role, data.declaration(text(relation, field))?.clone()));
        }
        let mut background = Vec::new();
        for sid in array(relation.get("background_statement_ids")) {
            background.push(
                data.declaration(match sid {
                    Ordered::String(sid) => sid,
                    _ => "",
                })?
                .clone(),
            );
        }
        declarations.push(("background", Ordered::Array(background)));
        if truthy(relation.get("remainder_statement_id")) {
            let statement = data
                .statements
                .get(text(relation, "remainder_statement_id"))?;
            declarations.push((
                "remainder",
                statement
                    .get("lean_declaration")
                    .cloned()
                    .unwrap_or(Ordered::Null),
            ));
        }
        let mut item = vec![
            ("id", required(relation, "id")?.clone()),
            ("specification", spec.clone()),
            ("certificates", Ordered::Array(certificates)),
            ("statement_declarations", object(declarations)),
            (
                "statement_parameter_indices",
                required(relation, "statement_parameter_indices")?.clone(),
            ),
        ];
        if let Some(separator) = relation.get("separator").filter(|s| truthy(Some(s))) {
            let setting = required(separator, "setting")?;
            let result = data.results.get(text(separator, "result_id"))?;
            modules.insert(sources.module_for(text(separator, "setting"))?);
            modules.insert(module(required(result, "solution_module")?));
            item.push((
                "separator",
                object(vec![
                    ("setting", setting.clone()),
                    ("theorem", required(result, "theorem")?.clone()),
                ]),
            ));
        }
        comparisons.push(object(item));
    }
    Ok(object(vec![
        ("modules", string_list(modules)),
        ("comparisons", Ordered::Array(comparisons)),
    ]))
}

/// Python `json.dump(value)`: ASCII escapes, default separators.
fn dump_ascii(value: &Ordered) -> String {
    match value {
        Ordered::String(text) => pyfmt::json_str(text, true),
        Ordered::Array(items) => format!(
            "[{}]",
            items.iter().map(dump_ascii).collect::<Vec<_>>().join(", ")
        ),
        Ordered::Object(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, item)| format!("{}: {}", pyfmt::json_str(key, true), dump_ascii(item)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        scalar => scalar.dumps(None),
    }
}

/// Python `verify`: build, bind full applications, extract their structure,
/// then run the existing result verification.
pub fn verify(
    root: &Path,
    corpus: &Corpus,
    data: &Data,
    relations: &[Ordered],
    exporters: &Exporters,
) -> Result<Vec<Ordered>, String> {
    let sources = Sources::scan(root)?;
    let request = checker_request(&sources, relations, data)?;
    if relations.is_empty() {
        return Ok(Vec::new());
    }
    let modules: Vec<String> = array(request.get("modules"))
        .iter()
        .map(|module| match module {
            Ordered::String(module) => module.clone(),
            other => other.dumps(None),
        })
        .collect();
    let lean = matches!(exporters, Exporters::Lean);
    if lean {
        let mut build = vec!["lake".to_owned(), "build".to_owned()];
        build.extend(modules.iter().cloned());
        run(root, &build)?;
    }
    let ids: BTreeSet<String> = relations.iter().flat_map(selected_results).collect();
    let contracts = bind_check::Contracts::load(root)?;
    let requests = bind_check::result_requests(corpus, Some(&ids));
    let input = bind_check::tool_input_with(corpus, &contracts, &requests, false);
    let described = match json_tool(root, bind_check::BIND_TOOL, &input, exporters)? {
        Ordered::Array(items) => items.iter().map(plain).collect::<Vec<Value>>(),
        _ => Vec::new(),
    };
    for entry in bind_check::bind_entries(corpus, &contracts, &described, &requests) {
        if entry.get("status").and_then(Value::as_str) != Some("bound") {
            return Err(format!(
                "{}: canonical result binding failed: {}",
                pyfmt::text(entry.get("id").unwrap_or(&Value::Null)),
                pyfmt::repr(&entry)
            ));
        }
    }
    let bindings = json_tool(
        root,
        "scripts/CheckStrength.lean",
        &dump_ascii(&request),
        exporters,
    )?;
    let covered = match &bindings {
        Ordered::Array(items) => {
            let found: BTreeSet<String> = items
                .iter()
                .map(|b| b.get("id").map_or("None".into(), |id| id.dumps(None)))
                .collect();
            let wanted: BTreeSet<String> = relations
                .iter()
                .map(|r| r.get("id").map_or("None".into(), |id| id.dumps(None)))
                .collect();
            found == wanted
        }
        _ => false,
    };
    if !covered {
        return Err("strength semantic checker did not cover the selected comparisons".into());
    }
    let mut indexed: HashMap<String, Ordered> = HashMap::new();
    for binding in array(Some(&bindings)) {
        indexed.insert(text(binding, "id").to_owned(), binding.clone());
    }
    for relation in relations {
        let binding = indexed
            .get(text(relation, "id"))
            .ok_or_else(|| key_error(text(relation, "id")))?;
        validate_binding(relation, data, binding)?;
        // Reject degenerate explanatory claims before spending time in the verifier.
        projection(relation, data, Some(binding), true)?;
    }
    // Reuse the preceding inspector instead of inventing another formula AST.
    let mut relevant: Vec<(String, Vec<String>)> = Vec::new();
    for relation in relations {
        let mut sids: Vec<&str> = vec![
            text(relation, "subject_id"),
            text(relation, "object_id"),
            text(relation, "delta_statement_id"),
        ];
        sids.extend(
            array(relation.get("background_statement_ids"))
                .iter()
                .map(|sid| match sid {
                    Ordered::String(sid) => sid.as_str(),
                    _ => "",
                }),
        );
        if truthy(relation.get("remainder_statement_id")) {
            sids.push(text(relation, "remainder_statement_id"));
        }
        let mut names = vec![text(relation, "comparison_spec").to_owned()];
        for sid in sids {
            names.push(match data.declaration(sid)? {
                Ordered::String(name) => name.clone(),
                other => other.dumps(None),
            });
        }
        let mut unique: Vec<String> = Vec::new();
        for name in names {
            if !unique.contains(&name) {
                unique.push(name);
            }
        }
        relevant.push((text(relation, "id").to_owned(), unique));
    }
    let declarations: BTreeSet<String> = relevant
        .iter()
        .flat_map(|(_, names)| names.iter().cloned())
        .collect();
    let structure_request = object(vec![
        ("modules", string_list(modules.iter().cloned())),
        ("declarations", string_list(declarations.iter().cloned())),
        (
            "unfold",
            string_list(
                declarations
                    .iter()
                    .filter(|name| name.starts_with("TruthCore."))
                    .cloned(),
            ),
        ),
    ]);
    let recorded = exporters
        .recorded("scripts/PropositionStructure.lean")
        .transpose()?;
    let extractor = match &recorded {
        Some(text) => Extractor::Saved(text),
        None => Extractor::Lean,
    };
    let structures = structure::run_extractor(root, &structure_request, &extractor)?
        .ok_or("structure extraction timed out; inspect the built modules and retry")?;
    let mut structure_index: HashMap<String, Ordered> = HashMap::new();
    for description in structures {
        structure_index.insert(text(&description, "declaration").to_owned(), description);
    }
    for (id, names) in &relevant {
        let mut found = Vec::new();
        for name in names {
            found.push(
                structure_index
                    .get(name)
                    .cloned()
                    .ok_or_else(|| key_error(name))?,
            );
        }
        if let Some(binding) = indexed.get_mut(id) {
            *binding = merged(binding, vec![("structure", Ordered::Array(found))]);
        }
    }
    if lean {
        for rid in &ids {
            run(root, &["scripts/verify-result.sh".to_owned(), rid.clone()])?;
        }
    }
    relations
        .iter()
        .map(|relation| projection(relation, data, indexed.get(text(relation, "id")), true))
        .collect()
}

// ---------------------------------------------------------------------------
// The producer bundle

/// Python `configuration_explorer.input_manifest` extended by
/// `strength_comparisons.input_manifest`: every dependency input, hashed.
pub fn input_manifest(root: &Path) -> Result<Vec<(String, String)>, String> {
    fn hashed(
        root: &Path,
        paths: BTreeSet<PathBuf>,
        error: &str,
        manifest: &mut Vec<(String, String)>,
    ) -> Result<(), String> {
        let paths: Vec<PathBuf> = paths.into_iter().collect();
        if let Some(path) = paths
            .iter()
            .find(|path| is_symlink(path) || !path.is_file())
        {
            return Err(format!("{error}: {}", structure::relative(root, path)));
        }
        // Hash in parallel; the manifest is sorted afterwards.
        let workers = std::thread::available_parallelism().map_or(4, usize::from);
        let chunk = paths.len().div_ceil(workers).max(1);
        let hashed: Vec<Result<Vec<(String, String)>, String>> = std::thread::scope(|scope| {
            let handles: Vec<_> = paths
                .chunks(chunk)
                .map(|part| {
                    scope.spawn(move || {
                        part.iter()
                            .map(|path| {
                                Ok((structure::relative(root, path), structure::digest(path)?))
                            })
                            .collect()
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| {
                    handle
                        .join()
                        .unwrap_or_else(|_| Err("hashing panicked".into()))
                })
                .collect()
        });
        for part in hashed {
            manifest.extend(part?);
        }
        Ok(())
    }
    let mut manifest = Vec::new();
    let mut paths: BTreeSet<PathBuf> = CONFIGURATION_FILES
        .iter()
        .map(|path| root.join(path))
        .collect();
    for (directory, pattern) in CONFIGURATION_DIRECTORIES {
        let (suffix, exact) = match pattern.strip_prefix('*') {
            Some(suffix) => (suffix, false),
            None => (pattern, true),
        };
        paths.extend(
            structure::rglob(&root.join(directory), suffix)
                .into_iter()
                .filter(|path| !exact || path.file_name().is_some_and(|name| name == pattern)),
        );
    }
    hashed(
        root,
        paths,
        "configuration report input is missing or a symlink",
        &mut manifest,
    )?;
    let mut paths: BTreeSet<PathBuf> = STRENGTH_FILES.iter().map(|path| root.join(path)).collect();
    for kind in STRENGTH_KINDS {
        paths.extend(structure::glob(&root.join("corpus").join(kind), ".json"));
    }
    hashed(
        root,
        paths,
        "strength input missing or symlink",
        &mut manifest,
    )?;
    // A path in both parts keeps one entry (a Python dict key).
    manifest.sort();
    manifest.dedup_by(|a, b| a.0 == b.0);
    Ok(manifest)
}

fn manifest_value(manifest: &[(String, String)]) -> Ordered {
    Ordered::Object(
        manifest
            .iter()
            .map(|(path, sha)| (path.clone(), string(sha)))
            .collect(),
    )
}

/// Python `input_digest`: sha256 of the compact sorted-key ASCII JSON.
pub fn input_digest(manifest: &[(String, String)]) -> String {
    let mut sorted: Vec<&(String, String)> = manifest.iter().collect();
    sorted.sort();
    let body = sorted
        .iter()
        .map(|(path, sha)| {
            format!(
                "{}:{}",
                pyfmt::json_str(path, true),
                pyfmt::json_str(sha, true)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    bind_check::sha256_hex(format!("{{{body}}}").as_bytes())
}

/// Python `source_head`: `git rev-parse HEAD` in `root`.
fn source_head(root: &Path) -> Result<String, String> {
    let finished = structure::run_bounded(
        root,
        "git",
        &["rev-parse".to_owned(), "HEAD".to_owned()],
        Duration::from_secs(10),
    )
    .map_err(|error| format!("cannot resolve producer source head: {error}"))?
    .ok_or("cannot resolve producer source head: timed out")?;
    if !finished.success {
        return Err(format!(
            "cannot resolve producer source head: {}",
            finished.stderr.trim_matches(pyfmt::is_space)
        ));
    }
    Ok(finished.stdout.trim_matches(pyfmt::is_space).to_owned())
}

fn is_symlink(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_symlink())
}

/// Python `Path.resolve()` (non-strict): the longest existing prefix
/// canonicalized, the rest normalized lexically (a `..` after a missing
/// directory still removes a component). Shared by the configuration
/// explorer's `.cache` containment check.
pub fn resolve(path: &Path) -> PathBuf {
    let mut existing = path.to_path_buf();
    let mut rest: Vec<Component> = Vec::new();
    let components: Vec<Component> = path.components().collect();
    let mut cut = components.len();
    loop {
        if let Ok(canonical) = fs::canonicalize(&existing) {
            existing = canonical;
            break;
        }
        if cut == 0 {
            existing = PathBuf::new();
            break;
        }
        cut -= 1;
        existing = components[..cut].iter().collect();
    }
    rest.extend(components[cut..].iter().copied());
    for component in rest {
        match component {
            Component::ParentDir => {
                existing.pop();
            }
            Component::CurDir => {}
            other => existing.push(other.as_os_str()),
        }
    }
    existing
}

/// Python `write_bundle`: live-verifies every registered comparison and
/// atomically writes the sorted-key bundle; returns the bundle in Python's
/// insertion order.
pub fn write_bundle(
    root: &Path,
    path: &Path,
    corpus: &Corpus,
    data: &Data,
    exporters: &Exporters,
) -> Result<Ordered, String> {
    let cache = root.join(".cache");
    if is_symlink(path) || is_symlink(&cache) || !resolve(path).starts_with(resolve(&cache)) {
        return Err("strength output must be a regular file inside the clone .cache".into());
    }
    let before = input_manifest(root)?;
    let reports = verify(root, corpus, data, &data.comparisons, exporters)?;
    let after = input_manifest(root)?;
    if before != after {
        return Err("strength inputs changed during verification; discard and rerun".into());
    }
    let bundle = object(vec![
        ("schema_version", Ordered::Int(SCHEMA_VERSION)),
        (
            "producer",
            object(vec![
                ("mode", string("live-verified")),
                ("source_head", string(source_head(root)?)),
                ("input_digest", string(input_digest(&after))),
                ("inputs", manifest_value(&after)),
                ("trust", string(TRUST)),
            ]),
        ),
        ("comparisons", Ordered::Array(reports)),
    ]);
    let parent = path.parent().unwrap_or(root);
    fs::create_dir_all(parent).map_err(|error| os_error(&error, parent))?;
    let name = path
        .file_name()
        .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
    let temporary = parent.join(format!(".{name}.{}.tmp", std::process::id()));
    let written = fs::write(&temporary, sorted_keys(&bundle).dumps(None) + "\n")
        .and_then(|()| fs::rename(&temporary, path));
    let _ = fs::remove_file(&temporary);
    written.map_err(|error| os_error(&error, path))?;
    Ok(bundle)
}

/// Python `read_bundle`: validates a trusted producer artifact, never
/// inferring fresh verification from hashes.
pub fn read_bundle(root: &Path, path: &Path, data: &Data) -> Result<Ordered, String> {
    if is_symlink(path) {
        return Err("strength report symlinks are unsupported".into());
    }
    let content = fs::read_to_string(path).map_err(|error| os_error(&error, path))?;
    let bundle = structure::parse(&content)?;
    let empty = Ordered::Object(Vec::new());
    let producer = bundle.get("producer").unwrap_or(&empty);
    if !get_eq(&bundle, "schema_version", &Ordered::Int(SCHEMA_VERSION))
        || !get_eq(producer, "mode", &string("live-verified"))
        || !get_eq(producer, "trust", &string(TRUST))
    {
        return Err("invalid strength report producer/schema".into());
    }
    let manifest = input_manifest(root)?;
    if !get_eq(producer, "inputs", &manifest_value(&manifest))
        || !get_eq(producer, "input_digest", &string(input_digest(&manifest)))
    {
        return Err("stale strength report: current dependency inputs differ".into());
    }
    let reports = match bundle.get("comparisons") {
        Some(Ordered::Array(reports))
            if reports.len() == data.comparisons.len()
                && reports
                    .iter()
                    .zip(&data.comparisons)
                    .all(|(report, relation)| {
                        get_eq(report, "id", relation.get("id").unwrap_or(&Ordered::Null))
                    }) =>
        {
            reports
        }
        _ => return Err("strength report does not cover exact registered comparisons".into()),
    };
    for (relation, actual) in data.comparisons.iter().zip(reports) {
        let binding = actual.get("binding").unwrap_or(&Ordered::Null);
        validate_binding(relation, data, binding)?;
        if !py_eq(actual, &projection(relation, data, Some(binding), true)?) {
            return Err(format!(
                "{}: strength projection differs from canonical evidence references",
                text(relation, "id")
            ));
        }
    }
    Ok(bundle)
}

/// The bundle as `strength-report --json` prints it: the producer without
/// its `inputs`.
pub fn without_inputs(bundle: &Ordered) -> Ordered {
    match bundle.get("producer") {
        Some(Ordered::Object(entries)) => merged(
            bundle,
            vec![(
                "producer",
                Ordered::Object(
                    entries
                        .iter()
                        .filter(|(key, _)| key != "inputs")
                        .cloned()
                        .collect(),
                ),
            )],
        ),
        _ => bundle.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn python_equality_ignores_key_order_and_numeric_kind() {
        let a = Ordered::parse(r#"{"a": [1, true], "b": {"x": 1.0, "y": null}}"#).unwrap();
        let b = Ordered::parse(r#"{"b": {"y": null, "x": 1}, "a": [1.0, 1]}"#).unwrap();
        assert!(py_eq(&a, &b));
        let c = Ordered::parse(r#"{"b": {"y": null, "x": 2}, "a": [1.0, 1]}"#).unwrap();
        assert!(!py_eq(&a, &c));
        assert!(!py_eq(&string("1"), &Ordered::Int(1)));
    }

    #[test]
    fn digest_is_compact_sorted_ascii_json() {
        let manifest = vec![
            ("b".to_owned(), "2".to_owned()),
            ("a".to_owned(), "1".to_owned()),
        ];
        assert_eq!(
            input_digest(&manifest),
            bind_check::sha256_hex(br#"{"a":"1","b":"2"}"#)
        );
    }

    #[test]
    fn merge_keeps_positions() {
        let base = Ordered::parse(r#"{"role": "x", "bound": true, "theorem": "t"}"#).unwrap();
        let value = merged(
            &base,
            vec![("theorem", string("u")), ("verified", Ordered::Bool(true))],
        );
        assert_eq!(
            value.dumps(None),
            r#"{"role": "x", "bound": true, "theorem": "u", "verified": true}"#
        );
    }
}
