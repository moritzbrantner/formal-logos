//! Configuration cases (#954 slice B2): Python `scripts/configurations.py`
//! `implication_closure` and `configuration_report`, and the text that
//! `corpus.py configurations` prints.
//!
//! Pure corpus logic only. Nothing here runs Lean: the live certificate
//! check (`verify_case`, `verify_compositions`) and the original-theorem
//! binding stay in Python until slice A6, so the CLI offers only the
//! registered projection (`verified = false`). The verified projection is
//! ported too (`configuration_report(.., true, ..)`), for that slice.

use crate::pyfmt::{repr, repr_str};
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap};

type Obj = Map<String, Value>;

/// Records by ID.
pub type Index<'a> = HashMap<&'a str, &'a Obj>;

/// The corpus records a configuration report reads.
pub struct Context<'a> {
    pub statements: Index<'a>,
    pub results: Index<'a>,
    pub arguments: Index<'a>,
    pub models: Index<'a>,
    /// The cases in file order.
    pub cases: Vec<&'a Obj>,
}

impl<'a> Context<'a> {
    pub fn new(corpus: &'a crate::Corpus) -> Self {
        let index = |kind: &str| -> Index<'a> {
            corpus
                .records(kind)
                .into_iter()
                .map(|record| (str_of(record, "id"), record))
                .collect()
        };
        Self {
            statements: index("statements"),
            results: index("results"),
            arguments: index("arguments"),
            models: index("models"),
            cases: corpus.records("configurations"),
        }
    }
}

pub const SCOPE: &str = "Formal encoding and registered model class only; no metaphysical possibility or premise closure follows. Unresolved means unresolved by available certified artifacts, not logical undecidability. Conditional proved/closed labels are never imported as premise-free facts; only selected assumptions and exact verified theorem hypotheses enter composition.";

const CORE_LIMIT: usize = 128;

pub(crate) fn str_of<'v>(record: &'v Obj, field: &str) -> &'v str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

pub(crate) fn strs<'v>(record: &'v Obj, field: &str) -> Vec<&'v str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

/// Python `corpus_ids.order_key`: the legacy id when there is one, else the id.
pub fn order_key<'v>(id: &'v str, record: Option<&'v Obj>) -> &'v str {
    record
        .and_then(|record| record.get("legacy_id"))
        .and_then(Value::as_str)
        .unwrap_or(id)
}

/// `items` sorted by their `order_key` (Python `sorted(..., key=order_key)`).
fn by_order_key<'v>(ids: &[&'v str], results: &Index<'v>) -> Vec<&'v str> {
    let mut ids = ids.to_vec();
    ids.sort_by_key(|id| order_key(id, results.get(id).copied()));
    ids
}

/// Every combination of one option per list, the last list varying fastest
/// (Python `itertools.product`); `visit` returns false to stop.
pub(crate) fn product<T>(lists: &[Vec<T>], mut visit: impl FnMut(&[&T]) -> bool) {
    if lists.iter().any(Vec::is_empty) {
        return;
    }
    let mut indices = vec![0; lists.len()];
    loop {
        let chosen: Vec<&T> = indices
            .iter()
            .zip(lists)
            .map(|(&index, list)| &list[index])
            .collect();
        if !visit(&chosen) {
            return;
        }
        let mut position = lists.len();
        loop {
            if position == 0 {
                return;
            }
            position -= 1;
            indices[position] += 1;
            if indices[position] < lists[position].len() {
                break;
            }
            indices[position] = 0;
        }
    }
}

/// `items` without repeats, first occurrence kept (Python `dict.fromkeys`).
pub(crate) fn unique<'v>(items: impl IntoIterator<Item = &'v str>) -> Vec<&'v str> {
    let mut seen = BTreeSet::new();
    items
        .into_iter()
        .filter(|item| seen.insert(*item))
        .collect()
}

/// One sufficient support of a statement: its assumptions and the rules
/// composed, in order.
#[derive(Clone)]
pub struct Support<'v> {
    pub statements: BTreeSet<&'v str>,
    pub results: Vec<&'v str>,
}

/// Python `implication_closure`'s result.
pub struct Closure<'v> {
    /// Statement ID and its supports, smallest first.
    pub items: Vec<(&'v str, Vec<Support<'v>>)>,
    pub limit: usize,
    pub combinations_checked: usize,
    pub truncated: bool,
}

/// The theorem names of `results`.
fn theorems(results: &[&str], index: &Index) -> Vec<Value> {
    results
        .iter()
        .map(|rid| {
            index
                .get(rid)
                .and_then(|result| result.get("theorem"))
                .cloned()
                .unwrap_or(Value::Null)
        })
        .collect()
}

impl Closure<'_> {
    /// One support as Python lists it.
    fn subset_json(support: &Support, results: &Index) -> Value {
        json!({"statement_ids": support.statements, "result_ids": support.results,
               "theorems": theorems(&support.results, results)})
    }

    /// The Python dictionary.
    pub fn to_json(&self, results: &Index) -> Value {
        let minimality = if self.truncated {
            "minimal among found supports"
        } else {
            "inclusion-minimal for supplied verified rules"
        };
        json!({
            "items": self.items.iter().map(|(sid, supports)| json!({
                "statement_id": sid,
                "sufficient_subsets": supports.iter()
                    .map(|support| Self::subset_json(support, results)).collect::<Vec<_>>(),
                "minimality": minimality,
            })).collect::<Vec<_>>(),
            "limit": self.limit,
            "combinations_checked": self.combinations_checked,
            "truncated": self.truncated,
        })
    }
}

/// Python `implication_closure(assumptions, case, results, arguments,
/// limit, include_assumptions)` with the case's `implication_result_ids`
/// as `rules`: an antichain of sufficient supports per statement, composed
/// only from the named rules; deterministic and explicitly bounded.
pub fn implication_closure<'v>(
    assumptions: &BTreeSet<&'v str>,
    rules: &[&'v str],
    results: &Index<'v>,
    arguments: &Index<'v>,
    limit: usize,
    include_assumptions: bool,
) -> Closure<'v> {
    // Each bucket keeps Python's dict order: deletions drop out, new
    // supports go last, so equal supports keep the first chain found.
    let mut supports: BTreeMap<&'v str, Vec<Support<'v>>> = assumptions
        .iter()
        .map(|sid| {
            (
                *sid,
                vec![Support {
                    statements: BTreeSet::from([*sid]),
                    results: Vec::new(),
                }],
            )
        })
        .collect();
    let rules: Vec<(&str, Vec<&str>, &str)> = by_order_key(rules, results)
        .into_iter()
        .filter_map(|rid| {
            let argument = arguments.get(str_of(results.get(rid)?, "argument_id"))?;
            Some((
                rid,
                strs(argument, "premise_statement_ids"),
                str_of(argument, "conclusion_statement_id"),
            ))
        })
        .collect();
    let mut work = 0;
    let mut truncated = false;
    let mut changed = true;
    while changed && !truncated {
        changed = false;
        for (rid, premises, conclusion) in &rules {
            if premises
                .iter()
                .any(|sid| supports.get(sid).is_none_or(Vec::is_empty))
            {
                continue;
            }
            let options: Vec<Vec<Support>> =
                premises.iter().map(|sid| supports[sid].clone()).collect();
            product(&options, |chosen| {
                work += 1;
                if work > limit {
                    truncated = true;
                    return false;
                }
                let support: BTreeSet<&str> = chosen
                    .iter()
                    .flat_map(|item| item.statements.iter().copied())
                    .collect();
                let chain = unique(
                    chosen
                        .iter()
                        .flat_map(|item| item.results.iter().copied())
                        .chain([*rid]),
                );
                let bucket = supports.entry(conclusion).or_default();
                if bucket
                    .iter()
                    .any(|existing| existing.statements.is_subset(&support))
                {
                    return true;
                }
                bucket.retain(|existing| {
                    !(support.is_subset(&existing.statements) && support != existing.statements)
                });
                bucket.push(Support {
                    statements: support,
                    results: chain,
                });
                changed = true;
                true
            });
            if truncated {
                break;
            }
        }
    }
    let items = supports
        .into_iter()
        .filter(|(sid, _)| include_assumptions || !assumptions.contains(sid))
        .map(|(sid, mut bucket)| {
            bucket.sort_by(|a, b| {
                (a.statements.len(), &a.statements).cmp(&(b.statements.len(), &b.statements))
            });
            (sid, bucket)
        })
        .collect();
    Closure {
        items,
        limit,
        combinations_checked: work.min(limit),
        truncated,
    }
}

/// One profile constant that a model binds differently (Python
/// `model_profile_mismatches`).
pub struct Mismatch {
    pub parameter: String,
    pub expected: Value,
    pub registered: Value,
}

impl Mismatch {
    fn to_json(&self) -> Value {
        json!({"parameter": self.parameter, "expected": self.expected, "registered": self.registered})
    }
}

/// Python `model_profile_mismatches(case, registration, models)`.
pub fn model_profile_mismatches(case: &Obj, registration: &Obj, models: &Index) -> Vec<Mismatch> {
    let empty = Obj::new();
    let constants = case
        .get("semantics")
        .and_then(|semantics| semantics.get("constants"))
        .and_then(Value::as_object)
        .unwrap_or(&empty);
    let model = models.get(str_of(registration, "model_id")).copied();
    let parameters = registration.get("parameters");
    constants
        .iter()
        .filter_map(|(role, term)| {
            let key = parameters
                .and_then(|parameters| parameters.get(role))
                .and_then(Value::as_str)
                .unwrap_or_default();
            let registered = model
                .and_then(|model| model.get("bindings"))
                .and_then(|bindings| bindings.get(key))
                .cloned()
                .unwrap_or(Value::Null);
            (&registered != term).then(|| Mismatch {
                parameter: role.clone(),
                expected: term.clone(),
                registered,
            })
        })
        .collect()
}

fn registrations(case: &Obj) -> Vec<&Obj> {
    case.get("model_bindings")
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_object).collect())
        .unwrap_or_default()
}

/// The `(statement_id, value)` pairs of a model's evaluations.
pub(crate) fn evaluations(model: &Obj) -> Vec<&Obj> {
    model
        .get("evaluations")
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_object).collect())
        .unwrap_or_default()
}

/// Python `configuration_report(case, results, arguments, models, verified=,
/// selection=)`: prune by cores and verified implication supports, without a
/// powerset search. An error is Python's `ValueError` message.
pub fn configuration_report(
    case: &Obj,
    results: &Index,
    arguments: &Index,
    models: &Index,
    verified: bool,
    selection: Option<(&str, Vec<&str>)>,
) -> Result<Value, String> {
    let bindings = registrations(case);
    let applicable: Vec<&Obj> = bindings
        .iter()
        .copied()
        .filter(|registration| model_profile_mismatches(case, registration, models).is_empty())
        .collect();
    let witnesses_for = |assumptions: &BTreeSet<&str>| -> Vec<String> {
        let mut found: Vec<String> = applicable
            .iter()
            .filter_map(|registration| models.get(str_of(registration, "model_id")))
            .filter(|model| {
                let values: HashMap<&str, &Value> = evaluations(model)
                    .into_iter()
                    .map(|item| {
                        (
                            str_of(item, "statement_id"),
                            item.get("value").unwrap_or(&Value::Null),
                        )
                    })
                    .collect();
                assumptions.iter().all(|sid| {
                    values.get(sid).and_then(|value| value.as_str()) == Some("satisfies")
                })
            })
            .map(|model| str_of(model, "id").to_owned())
            .collect();
        found.sort();
        found
    };
    let mut choices: Vec<(&str, Vec<&str>)> = match selection {
        Some(selection) => vec![selection],
        None => case
            .get("configurations")
            .and_then(Value::as_array)
            .map(|items| {
                items
                    .iter()
                    .filter_map(Value::as_object)
                    .map(|choice| (str_of(choice, "id"), strs(choice, "statement_ids")))
                    .collect()
            })
            .unwrap_or_default(),
    };
    choices.sort_by_key(|(id, _)| *id);
    let incompatibilities = by_order_key(&strs(case, "incompatibility_result_ids"), results);
    let rules = strs(case, "implication_result_ids");
    let mut entries = Vec::new();
    for (choice_id, statement_ids) in choices {
        let assumptions: BTreeSet<&str> = statement_ids.into_iter().collect();
        let closure = verified.then(|| {
            implication_closure(&assumptions, &rules, results, arguments, CORE_LIMIT, true)
        });
        let closure_truncated = closure.as_ref().is_some_and(|closure| closure.truncated);
        let supports: HashMap<&str, Vec<Support>> = match &closure {
            Some(closure) => closure.items.iter().cloned().collect(),
            None => assumptions
                .iter()
                .map(|sid| {
                    (
                        *sid,
                        vec![Support {
                            statements: BTreeSet::from([*sid]),
                            results: Vec::new(),
                        }],
                    )
                })
                .collect(),
        };
        let mut candidates: Vec<(BTreeSet<&str>, Value)> = Vec::new();
        let mut work = 0;
        let mut truncated = false;
        for rid in &incompatibilities {
            let Some(argument) = results
                .get(rid)
                .and_then(|result| arguments.get(str_of(result, "argument_id")))
            else {
                continue;
            };
            let premises = strs(argument, "premise_statement_ids");
            if premises.iter().any(|sid| !supports.contains_key(sid)) {
                continue;
            }
            let options: Vec<Vec<Support>> =
                premises.iter().map(|sid| supports[sid].clone()).collect();
            let mut certificate = premises.clone();
            certificate.sort();
            product(&options, |chosen| {
                work += 1;
                if work > CORE_LIMIT {
                    truncated = true;
                    return false;
                }
                let subset: BTreeSet<&str> = chosen
                    .iter()
                    .flat_map(|item| item.statements.iter().copied())
                    .collect();
                let chain = unique(
                    chosen
                        .iter()
                        .flat_map(|item| item.results.iter().copied())
                        .chain([*rid]),
                );
                candidates.push((
                    subset.clone(),
                    json!({"statement_ids": subset, "certificate_statement_ids": certificate,
                           "result_id": rid, "argument_id": argument.get("id"),
                           "theorem": results[rid].get("theorem"),
                           "theorems": theorems(&chain, results), "result_ids": chain}),
                ));
                true
            });
            if truncated {
                break;
            }
        }
        // First certificate per statement set, then the inclusion-minimal ones.
        let mut first: Vec<(BTreeSet<&str>, Value)> = Vec::new();
        for (subset, core) in candidates {
            if !first.iter().any(|(existing, _)| *existing == subset) {
                first.push((subset, core));
            }
        }
        let mut matching: Vec<(BTreeSet<&str>, Value)> = first
            .iter()
            .filter(|(subset, _)| {
                !first
                    .iter()
                    .any(|(other, _)| other.is_subset(subset) && other != subset)
            })
            .cloned()
            .collect();
        matching.sort_by(|(a, x), (b, y)| {
            (a.len(), a, x["result_id"].as_str()).cmp(&(b.len(), b, y["result_id"].as_str()))
        });
        let bounded = truncated || closure_truncated;
        for (subset, core) in &mut matching {
            let removal: Vec<(String, Vec<String>)> = subset
                .iter()
                .map(|sid| {
                    let mut rest = subset.clone();
                    rest.remove(sid);
                    ((*sid).to_owned(), witnesses_for(&rest))
                })
                .collect();
            let minimality = if verified && removal.iter().all(|(_, ids)| !ids.is_empty()) {
                "inclusion-minimal (each single removal has a certified model)"
            } else if bounded {
                "minimal among found certificate compositions (bounded search); proper-subset compatibility unresolved by available witnesses"
            } else {
                "minimal among supplied incompatibility certificates; proper-subset compatibility unresolved by available witnesses"
            };
            core["removal_evidence"] = removal
                .into_iter()
                .map(|(sid, ids)| json!({"removed_statement_id": sid, "model_ids": ids}))
                .collect();
            core["minimality"] = json!(minimality);
        }
        let witnesses = witnesses_for(&assumptions);
        if verified && !matching.is_empty() && !witnesses.is_empty() {
            return Err(
                "verification defect: incompatible core overlaps a model under the same semantics"
                    .into(),
            );
        }
        let status = if !verified {
            "verification required"
        } else if !matching.is_empty() {
            "verified incompatible"
        } else if !witnesses.is_empty() {
            "model witnessed"
        } else {
            "unresolved"
        };
        let consequences = match &closure {
            Some(closure) if matching.is_empty() => {
                let mut value = closure.to_json(results);
                if let Some(items) = value["items"].as_array_mut() {
                    items.retain(|item| {
                        !assumptions.contains(item["statement_id"].as_str().unwrap_or_default())
                    });
                }
                value
            }
            _ => Value::Null,
        };
        let unresolved_reason = (status == "unresolved").then_some(if bounded {
            "No certified core found within the reported search bound and no applicable registered model covers the complete selection."
        } else {
            "No applicable certified core or registered model covers the complete selection in this profile."
        });
        let model_witnesses: Vec<Value> = witnesses
            .iter()
            .map(|mid| {
                let model = models[mid.as_str()];
                json!({"model_id": mid, "lean_declaration": model.get("lean_declaration"),
                       "evaluations": evaluations(model).into_iter()
                           .filter(|item| assumptions.contains(str_of(item, "statement_id")))
                           .collect::<Vec<_>>()})
            })
            .collect();
        entries.push(json!({
            "id": choice_id,
            "statement_ids": assumptions,
            "status": status,
            "incompatible_cores": matching.into_iter().map(|(_, core)| core).collect::<Vec<_>>(),
            "model_ids": witnesses,
            "model_witnesses": model_witnesses,
            "unresolved_reason": unresolved_reason,
            "consequences": consequences,
            "core_composition": {"combinations_checked": work.min(CORE_LIMIT), "limit": CORE_LIMIT,
                                 "truncated": bounded},
        }));
    }
    let inapplicable: Vec<Value> = bindings
        .iter()
        .filter_map(|registration| {
            let mismatches = model_profile_mismatches(case, registration, models);
            (!mismatches.is_empty()).then(|| {
                json!({"model_id": registration.get("model_id"),
                       "profile_mismatches": mismatches.iter().map(Mismatch::to_json).collect::<Vec<_>>()})
            })
        })
        .collect();
    Ok(json!({
        "id": case.get("id"),
        "seed_statement_id": case.get("seed_statement_id"),
        "semantics": case.get("semantics"),
        "verified": verified,
        "configurations": entries,
        "inapplicable_models": inapplicable,
        "scope": SCOPE,
    }))
}

/// Python `repr` of a list of dictionaries whose keys print in `keys` order.
fn repr_records(items: &Value, keys: &[&str]) -> String {
    let items = items.as_array().map(Vec::as_slice).unwrap_or_default();
    let shown: Vec<String> = items
        .iter()
        .map(|item| {
            let fields: Vec<String> = keys
                .iter()
                .map(|key| format!("{}: {}", repr_str(key), repr(&item[*key])))
                .collect();
            format!("{{{}}}", fields.join(", "))
        })
        .collect();
    format!("[{}]", shown.join(", "))
}

fn text(value: &Value) -> String {
    crate::pyfmt::text(value)
}

/// The text `corpus.py configurations` prints for `reports`.
pub fn format_configurations(reports: &[Value]) -> String {
    let mut lines: Vec<String> = Vec::new();
    for report in reports {
        lines.push(format!(
            "{}: semantics {}",
            text(&report["id"]),
            text(&report["semantics"]["id"])
        ));
        lines.push(text(&report["scope"]));
        for model in report["inapplicable_models"]
            .as_array()
            .into_iter()
            .flatten()
        {
            lines.push(format!(
                "  inapplicable model {}: {}",
                text(&model["model_id"]),
                repr_records(
                    &model["profile_mismatches"],
                    &["parameter", "expected", "registered"]
                )
            ));
        }
        for entry in report["configurations"].as_array().into_iter().flatten() {
            lines.push(format!(
                "  {}: {}; premises {}",
                text(&entry["id"]),
                text(&entry["status"]),
                repr(&entry["statement_ids"])
            ));
            for core in entry["incompatible_cores"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "    core {}: {} / {}; {}",
                    repr(&core["statement_ids"]),
                    text(&core["result_id"]),
                    text(&core["theorem"]),
                    text(&core["minimality"])
                ));
                lines.push(format!(
                    "    certificate chain: {}",
                    repr(&core["result_ids"])
                ));
            }
            for model in entry["model_witnesses"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "    model: {} / {}",
                    text(&model["model_id"]),
                    text(&model["lean_declaration"])
                ));
                for evaluation in model["evaluations"].as_array().into_iter().flatten() {
                    lines.push(format!(
                        "      {}: {}",
                        text(&evaluation["statement_id"]),
                        text(&evaluation["theorem"])
                    ));
                }
            }
            if crate::pyfmt::truthy(Some(&entry["unresolved_reason"])) {
                lines.push(format!("    {}", text(&entry["unresolved_reason"])));
            }
            if crate::pyfmt::truthy(Some(&entry["consequences"])) {
                for consequence in entry["consequences"]["items"]
                    .as_array()
                    .into_iter()
                    .flatten()
                {
                    lines.push(format!(
                        "    consequence {}: {}",
                        text(&consequence["statement_id"]),
                        repr_records(
                            &consequence["sufficient_subsets"],
                            &["statement_ids", "result_ids", "theorems"]
                        )
                    ));
                }
            }
        }
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    //! The pure cases of `scripts/test_configurations.py` (its
    //! `ConfigurationTests` fixture), on the verified projection the CLI does
    //! not expose yet.
    use super::*;

    struct Fixture {
        results: Obj,
        arguments: Obj,
        models: Obj,
        case: Obj,
    }

    fn object(value: Value) -> Obj {
        value.as_object().cloned().unwrap()
    }

    fn fixture() -> Fixture {
        let results = object(json!({
            "CORE": {"id": "CORE", "argument_id": "CORE", "theorem": "Fixture.CORE"},
            "LARGER": {"id": "LARGER", "argument_id": "LARGER", "theorem": "Fixture.LARGER"},
            "PQ": {"id": "PQ", "argument_id": "PQ", "theorem": "Fixture.PQ"},
            "QR": {"id": "QR", "argument_id": "QR", "theorem": "Fixture.QR"},
        }));
        let arguments = object(json!({
            "CORE": {"id": "CORE", "premise_statement_ids": ["P", "Q"], "conclusion_statement_id": "False"},
            "LARGER": {"id": "LARGER", "premise_statement_ids": ["P", "Q", "R"], "conclusion_statement_id": "False"},
            "PQ": {"id": "PQ", "premise_statement_ids": ["P"], "conclusion_statement_id": "Q"},
            "QR": {"id": "QR", "premise_statement_ids": ["Q"], "conclusion_statement_id": "R"},
        }));
        let model = |id: &str, sid: &str| {
            json!({"id": id, "vocabulary": "V", "lean_declaration": "Fixture.model",
                   "bindings": {"W": "Bool", "I": "Bool", "F": "Fixture.frame", "present": "Fixture.present", "w": "Bool.false"},
                   "evaluations": [{"statement_id": sid, "arguments": ["W"], "value": "satisfies"}]})
        };
        let models = object(json!({"MP": model("MP", "P"), "MQ": model("MQ", "Q")}));
        let roles = json!({"W": "W", "I": "I", "F": "F", "present": "present", "w": "w"});
        let case = object(json!({
            "id": "7f1b8d1e-0c4a-4d7e-9a51-2f3c6b8e9d10", "seed_statement_id": "P",
            "semantics": {"id": "test", "vocabulary": "V", "applications": {"P": ["W"], "Q": ["W"], "R": ["W"], "S": ["W"]}},
            "configurations": [{"id": "core", "statement_ids": ["P", "Q"]}, {"id": "superset", "statement_ids": ["P", "Q", "R"]},
                               {"id": "control", "statement_ids": ["P"]}, {"id": "unknown", "statement_ids": ["S"]}],
            "incompatibility_result_ids": ["LARGER", "CORE"], "implication_result_ids": [],
            "model_bindings": [{"model_id": "MP", "parameters": roles}, {"model_id": "MQ", "parameters": roles}],
        }));
        Fixture {
            results,
            arguments,
            models,
            case,
        }
    }

    fn index(records: &Obj) -> Index<'_> {
        records
            .iter()
            .map(|(id, record)| (id.as_str(), record.as_object().unwrap()))
            .collect()
    }

    impl Fixture {
        fn report(&self, verified: bool) -> Result<Value, String> {
            configuration_report(
                &self.case,
                &index(&self.results),
                &index(&self.arguments),
                &index(&self.models),
                verified,
                None,
            )
        }

        fn entries(&self) -> BTreeMap<String, Value> {
            self.report(true).unwrap()["configurations"]
                .as_array()
                .unwrap()
                .iter()
                .map(|entry| (entry["id"].as_str().unwrap().to_owned(), entry.clone()))
                .collect()
        }
    }

    #[test]
    fn core_prunes_supersets_not_subsets_with_removal_evidence() {
        let mut fixture = fixture();
        let report = fixture.entries();
        assert_eq!(report["core"]["status"], "verified incompatible");
        assert_eq!(
            report["superset"]["incompatible_cores"][0]["result_id"],
            "CORE"
        );
        assert_eq!(report["control"]["status"], "model witnessed");
        assert_eq!(report["unknown"]["status"], "unresolved");
        let core = &report["core"]["incompatible_cores"][0];
        assert!(
            core["minimality"]
                .as_str()
                .unwrap()
                .starts_with("inclusion-minimal (each single removal")
        );
        assert_eq!(
            core["removal_evidence"],
            json!([{"removed_statement_id": "P", "model_ids": ["MQ"]},
                   {"removed_statement_id": "Q", "model_ids": ["MP"]}])
        );
        fixture.models.remove("MQ");
        fixture.case["model_bindings"]
            .as_array_mut()
            .unwrap()
            .truncate(1);
        let report = fixture.report(true).unwrap();
        assert!(
            report["configurations"][1]["incompatible_cores"][0]["minimality"]
                .as_str()
                .unwrap()
                .starts_with("minimal among supplied incompatibility certificates")
        );
    }

    #[test]
    fn unverified_has_no_certified_status_and_inconsistent_sets_no_consequences() {
        let fixture = fixture();
        let report = fixture.report(false).unwrap();
        assert!(
            report["configurations"]
                .as_array()
                .unwrap()
                .iter()
                .all(|entry| entry["status"] == "verification required")
        );
        assert!(fixture.entries()["core"]["consequences"].is_null());
    }

    #[test]
    fn overlap_is_a_verification_defect() {
        let mut fixture = fixture();
        fixture.models["MP"]["evaluations"]
            .as_array_mut()
            .unwrap()
            .push(json!({"statement_id": "Q", "arguments": ["W"], "value": "satisfies"}));
        assert!(
            fixture
                .report(true)
                .unwrap_err()
                .starts_with("verification defect")
        );
        assert!(fixture.report(false).is_ok());
    }

    #[test]
    fn equal_cores_keep_the_proof_selected_by_legacy_order() {
        let mut fixture = fixture();
        fixture.arguments["LARGER"]["premise_statement_ids"] = json!(["P", "Q"]);
        fixture.case["configurations"] = json!([{"id": "core", "statement_ids": ["P", "Q"]}]);
        let original =
            fixture.report(true).unwrap()["configurations"][0]["incompatible_cores"][0].clone();
        let identities = [
            ("CORE", "ffffffff-ffff-5fff-8fff-ffffffffffff"),
            ("LARGER", "00000000-0000-5000-8000-000000000000"),
        ];
        for (legacy, uuid) in identities {
            let mut result = fixture.results.remove(legacy).unwrap();
            result["id"] = json!(uuid);
            result["legacy_id"] = json!(legacy);
            fixture.results.insert(uuid.into(), result);
        }
        fixture.case["incompatibility_result_ids"] = json!([identities[1].1, identities[0].1]);
        let migrated =
            fixture.report(true).unwrap()["configurations"][0]["incompatible_cores"][0].clone();
        let expected = identities
            .iter()
            .find(|(legacy, _)| original["result_id"] == *legacy)
            .unwrap()
            .1;
        assert_eq!(migrated["result_id"], expected);
        assert_eq!(migrated["theorems"], original["theorems"]);
    }

    #[test]
    fn closure_tracks_exact_supports_and_cycles_add_no_atoms() {
        let fixture = fixture();
        let (results, arguments) = (index(&fixture.results), index(&fixture.arguments));
        let rules = ["PQ", "QR"];
        let closure = implication_closure(
            &BTreeSet::from(["P", "S"]),
            &rules,
            &results,
            &arguments,
            128,
            false,
        );
        let value = closure.to_json(&results);
        assert_eq!(value["items"][1]["statement_id"], "R");
        assert_eq!(
            value["items"][1]["sufficient_subsets"][0]["statement_ids"],
            json!(["P"])
        );
        assert_eq!(
            value["items"][1]["sufficient_subsets"][0]["result_ids"],
            json!(["PQ", "QR"])
        );
        assert_eq!(
            value["items"][1]["sufficient_subsets"][0]["theorems"],
            json!(["Fixture.PQ", "Fixture.QR"])
        );
        assert!(
            implication_closure(
                &BTreeSet::from(["S"]),
                &rules,
                &results,
                &arguments,
                128,
                false
            )
            .items
            .is_empty()
        );
        assert!(
            implication_closure(
                &BTreeSet::from(["P"]),
                &rules,
                &results,
                &arguments,
                1,
                false
            )
            .truncated
        );
    }

    #[test]
    fn composed_cores_and_consequences_follow_the_rules() {
        let mut fixture = fixture();
        fixture.case["implication_result_ids"] = json!(["PQ", "QR"]);
        fixture.case["incompatibility_result_ids"] = json!(["CORE"]);
        fixture.models.clear();
        fixture.case["model_bindings"] = json!([]);
        fixture.case["configurations"] =
            json!([{"id": "p", "statement_ids": ["P"]}, {"id": "q", "statement_ids": ["Q"]}]);
        // P derives Q, so {P} meets the core {P, Q} through the rule PQ; Q
        // derives R. The value Python's `configuration_report` gives.
        let expected: Value = serde_json::from_str(r#"[{"consequences": null, "core_composition": {"combinations_checked": 1, "limit": 128, "truncated": false}, "id": "p", "incompatible_cores": [{"argument_id": "CORE", "certificate_statement_ids": ["P", "Q"], "minimality": "minimal among supplied incompatibility certificates; proper-subset compatibility unresolved by available witnesses", "removal_evidence": [{"model_ids": [], "removed_statement_id": "P"}], "result_id": "CORE", "result_ids": ["PQ", "CORE"], "statement_ids": ["P"], "theorem": "Fixture.CORE", "theorems": ["Fixture.PQ", "Fixture.CORE"]}], "model_ids": [], "model_witnesses": [], "statement_ids": ["P"], "status": "verified incompatible", "unresolved_reason": null}, {"consequences": {"combinations_checked": 2, "items": [{"minimality": "inclusion-minimal for supplied verified rules", "statement_id": "R", "sufficient_subsets": [{"result_ids": ["QR"], "statement_ids": ["Q"], "theorems": ["Fixture.QR"]}]}], "limit": 128, "truncated": false}, "core_composition": {"combinations_checked": 0, "limit": 128, "truncated": false}, "id": "q", "incompatible_cores": [], "model_ids": [], "model_witnesses": [], "statement_ids": ["Q"], "status": "unresolved", "unresolved_reason": "No applicable certified core or registered model covers the complete selection in this profile."}]"#).unwrap();
        assert_eq!(fixture.report(true).unwrap()["configurations"], expected);
    }

    #[test]
    fn adding_a_certificate_changes_only_justified_statuses_and_order_is_stable() {
        let mut fixture = fixture();
        fixture.case["incompatibility_result_ids"] = json!([]);
        let before = fixture.entries();
        fixture.case["incompatibility_result_ids"] = json!(["CORE"]);
        let after = fixture.entries();
        let changed: Vec<&String> = before
            .keys()
            .filter(|id| before[*id]["status"] != after[*id]["status"])
            .collect();
        assert_eq!(changed, ["core", "superset"]);
        let report = fixture.report(true).unwrap();
        fixture.case["configurations"]
            .as_array_mut()
            .unwrap()
            .reverse();
        assert_eq!(report, fixture.report(true).unwrap());
    }

    #[test]
    fn fixed_constants_exclude_and_report_models() {
        let mut fixture = fixture();
        fixture.case["semantics"]["constants"] = json!({"W": "Nat", "I": "Bool"});
        let report = fixture.report(true).unwrap();
        assert_eq!(report["inapplicable_models"].as_array().unwrap().len(), 2);
        assert_eq!(
            report["inapplicable_models"][0]["profile_mismatches"][0],
            json!({"parameter": "W", "expected": "Nat", "registered": "Bool"})
        );
        let text = format_configurations(std::slice::from_ref(&report));
        assert!(text.contains(
            "  inapplicable model MP: [{'parameter': 'W', 'expected': 'Nat', 'registered': 'Bool'}]"
        ));
        let control = fixture.entries()["control"].clone();
        assert_eq!(control["status"], "unresolved");
        assert_eq!(control["model_ids"], json!([]));
    }
}
