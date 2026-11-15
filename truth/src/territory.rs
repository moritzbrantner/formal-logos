//! Emergent positions and the territory matrix (#512): Python
//! `scripts/territory.py` and the `corpus.py territory` command (#954 slice
//! B2). Nothing is hand-authored and no record is written; see the Python
//! module for which records feed which relation.

use crate::configurations::{
    Index, evaluations, implication_closure, product, str_of, strs, unique,
};
use crate::pyfmt::{repr, repr_str, slice_end, text, truthy};
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap};

type Obj = Map<String, Value>;
type Set<'v> = BTreeSet<&'v str>;

pub const FALSE_DECLARATION: &str = "TruthCore.Logic.ConfigurationFalse";
pub const SCOPE: &str = "Computed from registered cores, entailments, models, consistency results and claims only; no position is named or hand-authored and no corpus record is written. Positions are maximal relative to the reported bounded atom universe and certified cores only: absence of a core is not consistency, absence of a witness is not inconsistency. common_ground entries are candidates; marking one still needs #501/#378 evidence.";

/// The report's bounds (Python keyword defaults).
pub struct Bounds {
    pub max_atoms: i64,
    pub closure_limit: usize,
    pub core_combination_limit: usize,
    pub hitting_set_limit: usize,
    pub global_position_limit: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        Self {
            max_atoms: 512,
            closure_limit: 20000,
            core_combination_limit: 4096,
            hitting_set_limit: 1024,
            global_position_limit: 64,
        }
    }
}

/// The records `territory_report` reads.
pub struct Inputs<'v> {
    pub statements: Index<'v>,
    pub arguments: Index<'v>,
    /// Results by ID, in ID order (Python `sorted(results)`).
    pub results: BTreeMap<&'v str, &'v Obj>,
    pub relations: Vec<&'v Obj>,
    pub claims: Vec<&'v Obj>,
    pub sources: Index<'v>,
    pub models: Vec<&'v Obj>,
    pub transcription_results: BTreeSet<String>,
    /// `(statement_id, number of transitive dependent arguments)` of every
    /// frontier item with a path to the root.
    pub seeds: Vec<(String, usize)>,
    /// The frontier's root routes.
    pub routes: Vec<Value>,
}

pub use crate::sha256::sha256_hex;

/// Python `position_id`: `POS-` and the first 12 hex digits (upper case) of
/// the SHA-256 of the sorted atoms joined by newlines.
pub fn position_id<'a>(atoms: impl IntoIterator<Item = &'a str>) -> String {
    let mut atoms: Vec<&str> = atoms.into_iter().collect();
    atoms.sort();
    format!(
        "POS-{}",
        sha256_hex(atoms.join("\n").as_bytes())[..12].to_uppercase()
    )
}

/// A certified incompatible statement set and its evidence.
pub struct Core<'v> {
    pub statement_ids: Vec<&'v str>,
    pub kind: &'static str,
    pub result_id: &'v str,
    pub argument_id: &'v str,
    pub relation_id: Option<&'v str>,
}

fn false_ids<'v>(statements: &Index<'v>) -> BTreeSet<&'v str> {
    statements
        .iter()
        .filter(|(_, record)| {
            record.get("lean_declaration").and_then(Value::as_str) == Some(FALSE_DECLARATION)
        })
        .map(|(sid, _)| *sid)
        .collect()
}

fn sorted_set<'v>(items: impl IntoIterator<Item = &'v str>) -> Vec<&'v str> {
    items.into_iter().collect::<Set>().into_iter().collect()
}

/// Python `certified_cores`.
pub fn certified_cores<'v>(inputs: &Inputs<'v>) -> Vec<Core<'v>> {
    let false_ids = false_ids(&inputs.statements);
    let mut usable: BTreeMap<&str, &str> = BTreeMap::new();
    for (rid, result) in &inputs.results {
        let argument_id = str_of(result, "argument_id");
        if inputs.transcription_results.contains(*rid)
            || !inputs.arguments.contains_key(argument_id)
        {
            continue;
        }
        usable.entry(argument_id).or_insert(rid);
    }
    let mut cores = Vec::new();
    for (argument_id, rid) in &usable {
        let argument = inputs.arguments[argument_id];
        if false_ids.contains(str_of(argument, "conclusion_statement_id")) {
            cores.push(Core {
                statement_ids: sorted_set(strs(argument, "premise_statement_ids")),
                kind: "derives_false",
                result_id: rid,
                argument_id,
                relation_id: None,
            });
        }
    }
    let mut relations = inputs.relations.clone();
    relations.sort_by_key(|relation| str_of(relation, "id"));
    for relation in relations {
        let subject = str_of(relation, "subject_id");
        if relation.get("predicate").and_then(Value::as_str) != Some("refutes")
            || !usable.contains_key(subject)
        {
            continue;
        }
        let argument = inputs.arguments[subject];
        cores.push(Core {
            statement_ids: sorted_set(
                strs(argument, "premise_statement_ids")
                    .into_iter()
                    .chain([str_of(relation, "object_id")]),
            ),
            kind: "refutes",
            result_id: usable[subject],
            argument_id: str_of(argument, "id"),
            relation_id: Some(str_of(relation, "id")),
        });
    }
    cores
}

/// Python `entailment_rules`: one registered non-transcription result per
/// argument; no cores, no consistency results.
pub fn entailment_rules<'v>(inputs: &Inputs<'v>) -> Vec<&'v str> {
    let false_ids = false_ids(&inputs.statements);
    let mut chosen: BTreeMap<&str, &str> = BTreeMap::new();
    for (rid, result) in &inputs.results {
        let Some(argument) = inputs.arguments.get(str_of(result, "argument_id")) else {
            continue;
        };
        if inputs.transcription_results.contains(*rid)
            || truthy(argument.get("commitment_statement_ids"))
            || false_ids.contains(str_of(argument, "conclusion_statement_id"))
        {
            continue;
        }
        chosen.entry(str_of(argument, "id")).or_insert(rid);
    }
    sorted_set(chosen.into_values())
}

/// A certified witness: kind, ID, satisfied and violated statements.
pub struct Witness<'v> {
    pub kind: &'static str,
    pub id: &'v str,
    pub satisfied: Set<'v>,
    pub violated: Set<'v>,
}

/// Python `witnesses`.
pub fn witnesses<'v>(inputs: &Inputs<'v>) -> Vec<Witness<'v>> {
    let mut found = Vec::new();
    let mut models = inputs.models.clone();
    models.sort_by_key(|model| str_of(model, "id"));
    for model in models {
        let values: HashMap<&str, Option<&str>> = evaluations(model)
            .into_iter()
            .map(|item| {
                (
                    str_of(item, "statement_id"),
                    item.get("value").and_then(Value::as_str),
                )
            })
            .collect();
        found.push(Witness {
            kind: "model",
            id: str_of(model, "id"),
            satisfied: values
                .iter()
                .filter(|(_, value)| **value == Some("satisfies"))
                .map(|(sid, _)| *sid)
                .collect(),
            violated: values
                .iter()
                .filter(|(_, value)| **value == Some("violates"))
                .map(|(sid, _)| *sid)
                .collect(),
        });
    }
    let mut seen = BTreeSet::new();
    for (rid, result) in &inputs.results {
        let Some(argument) = inputs.arguments.get(str_of(result, "argument_id")) else {
            continue;
        };
        if inputs.transcription_results.contains(*rid)
            || !truthy(argument.get("commitment_statement_ids"))
            || !seen.insert(str_of(argument, "id"))
        {
            continue;
        }
        found.push(Witness {
            kind: "consistency_result",
            id: rid,
            satisfied: strs(argument, "commitment_statement_ids")
                .into_iter()
                .collect(),
            violated: Set::new(),
        });
    }
    found
}

fn size_order(a: &Set, b: &Set) -> std::cmp::Ordering {
    (a.len(), a).cmp(&(b.len(), b))
}

/// Python `minimal_sets`: the inclusion-minimal distinct sets, smallest first.
pub fn minimal_sets<'v>(sets: impl IntoIterator<Item = Set<'v>>) -> Vec<Set<'v>> {
    let mut unique: Vec<Set> = sets
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    unique.sort_by(size_order);
    let mut kept: Vec<Set> = Vec::new();
    for item in unique {
        if !kept.iter().any(|other| other.is_subset(&item)) {
            kept.push(item);
        }
    }
    kept
}

/// Python `minimal_hitting_sets` (Berge's algorithm, deterministic): the
/// sets and whether the limit cut them off, in which case none is returned.
pub fn minimal_hitting_sets<'v>(conflicts: &[Set<'v>], limit: usize) -> (Vec<Set<'v>>, bool) {
    let mut ordered: Vec<&Set> = conflicts.iter().collect();
    ordered.sort_by(|a, b| size_order(a, b));
    let mut hitting = vec![Set::new()];
    for conflict in ordered {
        let mut grown = Vec::new();
        for current in hitting {
            if current.intersection(conflict).next().is_some() {
                grown.push(current);
            } else {
                for atom in conflict {
                    let mut next = current.clone();
                    next.insert(atom);
                    grown.push(next);
                }
            }
        }
        hitting = minimal_sets(grown);
        if hitting.len() > limit {
            return (Vec::new(), true);
        }
    }
    (hitting, false)
}

/// The evidence of one minimal conflict, with Python's key order kept for
/// the `DEFECT` line.
struct Evidence<'v> {
    statement_ids: Vec<&'v str>,
    core_statement_ids: Vec<&'v str>,
    kind: &'static str,
    relation_id: Option<&'v str>,
    result_ids: Vec<&'v str>,
}

impl Evidence<'_> {
    fn to_json(&self) -> Value {
        json!({"statement_ids": self.statement_ids, "core_statement_ids": self.core_statement_ids,
               "kind": self.kind, "relation_id": self.relation_id, "result_ids": self.result_ids})
    }

    fn repr(&self) -> String {
        format!(
            "{{'statement_ids': {}, 'core_statement_ids': {}, 'kind': {}, 'relation_id': {}, 'result_ids': {}}}",
            repr(&json!(self.statement_ids)),
            repr(&json!(self.core_statement_ids)),
            repr_str(self.kind),
            self.relation_id.map_or("None".to_owned(), repr_str),
            repr(&json!(self.result_ids))
        )
    }
}

/// Python `territory_report`, and the Python `repr` of each defect (which
/// An exact nonnegative integer (little-endian base-2^32 limbs), for the
/// global position count, which Python computes as an unbounded int.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Count(Vec<u32>);

impl Count {
    pub fn one() -> Self {
        Self(vec![1])
    }

    pub fn multiply(&mut self, factor: u32) {
        let mut carry = 0u64;
        for limb in &mut self.0 {
            let product = u64::from(*limb) * u64::from(factor) + carry;
            *limb = product as u32;
            carry = product >> 32;
        }
        if carry > 0 {
            self.0.push(carry as u32);
        }
        while self.0.len() > 1 && self.0.last() == Some(&0) {
            self.0.pop();
        }
    }

    /// The value, when it fits a `u64`.
    pub fn to_u64(&self) -> Option<u64> {
        match self.0.as_slice() {
            [low] => Some(u64::from(*low)),
            [low, high] => Some(u64::from(*low) | (u64::from(*high) << 32)),
            _ => None,
        }
    }

    pub fn exceeds(&self, value: u64) -> bool {
        self.to_u64().is_none_or(|count| count > value)
    }

    /// Decimal digits, as Python prints the int.
    pub fn decimal(&self) -> String {
        let mut limbs = self.0.clone();
        let mut chunks = Vec::new();
        while limbs.iter().any(|limb| *limb != 0) {
            let mut remainder = 0u64;
            for limb in limbs.iter_mut().rev() {
                let value = (remainder << 32) | u64::from(*limb);
                *limb = (value / 1_000_000_000) as u32;
                remainder = value % 1_000_000_000;
            }
            chunks.push(remainder);
        }
        match chunks.split_last() {
            None => "0".into(),
            Some((first, rest)) => {
                let mut text = first.to_string();
                for chunk in rest.iter().rev() {
                    text.push_str(&format!("{chunk:09}"));
                }
                text
            }
        }
    }
}

/// A territory report.
pub struct Territory {
    /// The Python JSON object. Its `global_positions.count` is `null` both
    /// when the count is unknown and when it exceeds `u64`; see
    /// `global_count` and [`Territory::count_unrepresentable`].
    pub report: Value,
    /// The Python `repr` of each defect (which the text's `DEFECT` lines
    /// print, in Python's key order).
    pub defects: Vec<String>,
    /// The exact global position count; `None` when it is unknown (a
    /// component's enumeration was truncated).
    pub global_count: Option<Count>,
}

impl Territory {
    /// Whether the JSON count is `null` only because the exact count does
    /// not fit a `u64`, so the JSON would misreport it.
    pub fn count_unrepresentable(&self) -> bool {
        self.global_count
            .as_ref()
            .is_some_and(|count| count.to_u64().is_none())
    }
}

/// Python `territory_report`.
pub fn territory_report(inputs: &Inputs, bounds: &Bounds) -> Territory {
    let seed_ids: Vec<&str> = sorted_set(inputs.seeds.iter().map(|(sid, _)| sid.as_str()));
    let mut alternatives: HashMap<&str, Set> = HashMap::new();
    for relation in &inputs.relations {
        if relation.get("predicate").and_then(Value::as_str) == Some("alternative_to") {
            let (subject, object) = (
                str_of(relation, "subject_id"),
                str_of(relation, "object_id"),
            );
            alternatives.entry(object).or_default().insert(subject);
            alternatives.entry(subject).or_default().insert(object);
        }
    }
    let rivals: BTreeMap<&str, Vec<&str>> = seed_ids
        .iter()
        .map(|seed| {
            (
                *seed,
                alternatives
                    .get(seed)
                    .map(|set| set.iter().copied().collect())
                    .unwrap_or_default(),
            )
        })
        .collect();
    let seed_set: Set = seed_ids.iter().copied().collect();
    let rival_ids: Vec<&str> = rivals
        .values()
        .flatten()
        .copied()
        .filter(|rival| !seed_set.contains(rival))
        .collect::<Set>()
        .into_iter()
        .collect();
    let cores = certified_cores(inputs);
    let rule_ids = entailment_rules(inputs);
    let results: Index = inputs
        .results
        .iter()
        .map(|(id, record)| (*id, *record))
        .collect();
    let certified_witnesses = witnesses(inputs);

    // Universe: one expansion round from seeds and rivals.
    let base: Set = seed_ids.iter().chain(&rival_ids).copied().collect();
    let reachable: Set = implication_closure(
        &base,
        &rule_ids,
        &results,
        &inputs.arguments,
        bounds.closure_limit,
        true,
    )
    .items
    .into_iter()
    .map(|(sid, _)| sid)
    .collect();
    let added_cores: Vec<&str> = cores
        .iter()
        .filter(|core| core.statement_ids.iter().any(|sid| reachable.contains(sid)))
        .flat_map(|core| core.statement_ids.iter().copied())
        .filter(|sid| !base.contains(sid))
        .collect::<Set>()
        .into_iter()
        .collect();
    let added_core_set: Set = added_cores.iter().copied().collect();
    let added_witness: Vec<&str> = certified_witnesses
        .iter()
        .filter(|witness| {
            witness
                .satisfied
                .union(&witness.violated)
                .any(|sid| base.contains(sid))
        })
        .flat_map(|witness| witness.satisfied.union(&witness.violated).copied())
        .filter(|sid| !base.contains(sid) && !added_core_set.contains(sid))
        .collect::<Set>()
        .into_iter()
        .collect();
    let ordered: Vec<&str> = seed_ids
        .iter()
        .chain(&rival_ids)
        .chain(&added_cores)
        .chain(&added_witness)
        .copied()
        .collect();
    let universe_truncated = (ordered.len() as i64) > bounds.max_atoms;
    let universe: Vec<&str> = ordered[..slice_end(ordered.len(), bounds.max_atoms)].to_vec();
    let atoms: Set = universe.iter().copied().collect();

    let closure = implication_closure(
        &atoms,
        &rule_ids,
        &results,
        &inputs.arguments,
        bounds.closure_limit,
        true,
    );
    let supports: BTreeMap<&str, Vec<Set>> = closure
        .items
        .iter()
        .map(|(sid, options)| {
            (
                *sid,
                options
                    .iter()
                    .map(|option| option.statements.clone())
                    .collect(),
            )
        })
        .collect();
    let chains: HashMap<&str, &Vec<crate::configurations::Support>> = closure
        .items
        .iter()
        .map(|(sid, options)| (*sid, options))
        .collect();
    let unconditional: Vec<&str> = supports
        .iter()
        .filter(|(sid, options)| options.iter().any(Set::is_empty) && !atoms.contains(*sid))
        .map(|(sid, _)| *sid)
        .collect();

    let mut evidence: Vec<(Set, Evidence)> = Vec::new();
    let mut evidence_index: HashMap<Set, usize> = HashMap::new();
    let mut combinations_checked = 0;
    let mut core_truncated = false;
    for core in &cores {
        if core
            .statement_ids
            .iter()
            .any(|sid| !supports.contains_key(sid))
        {
            continue;
        }
        let options: Vec<Vec<crate::configurations::Support>> = core
            .statement_ids
            .iter()
            .map(|sid| chains[sid].clone())
            .collect();
        product(&options, |chosen| {
            combinations_checked += 1;
            if combinations_checked > bounds.core_combination_limit {
                core_truncated = true;
                return false;
            }
            let subset: Set = chosen
                .iter()
                .flat_map(|option| option.statements.iter().copied())
                .collect();
            if !evidence_index.contains_key(&subset) {
                let chain = unique(
                    chosen
                        .iter()
                        .flat_map(|option| option.results.iter().copied())
                        .chain([core.result_id]),
                );
                evidence_index.insert(subset.clone(), evidence.len());
                evidence.push((
                    subset.clone(),
                    Evidence {
                        statement_ids: subset.iter().copied().collect(),
                        core_statement_ids: core.statement_ids.clone(),
                        kind: core.kind,
                        relation_id: core.relation_id,
                        result_ids: chain,
                    },
                ));
            }
            true
        });
        if core_truncated {
            break;
        }
    }
    let of = |conflict: &Set| -> &Evidence { &evidence[evidence_index[conflict]].1 };
    let mut conflicts = minimal_sets(evidence.iter().map(|(subset, _)| subset.clone()));
    let mut defects: Vec<(Value, String)> = Vec::new();
    if conflicts.iter().any(Set::is_empty) {
        let found = of(&Set::new());
        defects.push((
            json!({"kind": "inconsistent_without_atoms", "conflict": found.to_json()}),
            format!(
                "{{'kind': 'inconsistent_without_atoms', 'conflict': {}}}",
                found.repr()
            ),
        ));
        conflicts.retain(|conflict| !conflict.is_empty());
    }
    for witness in &certified_witnesses {
        for conflict in &conflicts {
            if conflict.is_subset(&witness.satisfied) {
                let found = of(conflict);
                defects.push((
                    json!({"kind": "witness_satisfies_conflict",
                           "witness": {"kind": witness.kind, "id": witness.id},
                           "conflict": found.to_json()}),
                    format!(
                        "{{'kind': 'witness_satisfies_conflict', 'witness': {{'kind': {}, 'id': {}}}, 'conflict': {}}}",
                        repr_str(witness.kind),
                        repr_str(witness.id),
                        found.repr()
                    ),
                ));
            }
        }
    }

    // Components: atoms linked by a shared minimal conflict.
    let mut parent: HashMap<&str, &str> = universe.iter().map(|atom| (*atom, *atom)).collect();
    fn find<'v>(parent: &mut HashMap<&'v str, &'v str>, mut atom: &'v str) -> &'v str {
        while parent[atom] != atom {
            let grand = parent[parent[atom]];
            parent.insert(atom, grand);
            atom = grand;
        }
        atom
    }
    for conflict in &conflicts {
        let mut members = conflict.iter();
        let Some(first) = members.next() else {
            continue;
        };
        for atom in members {
            let (a, b) = (find(&mut parent, first), find(&mut parent, atom));
            if a != b {
                parent.insert(a.max(b), a.min(b));
            }
        }
    }
    let mut groups: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for atom in &universe {
        let root = find(&mut parent, atom);
        groups.entry(root).or_default().push(atom);
    }
    let mut groups: Vec<Vec<&str>> = groups
        .into_values()
        .map(|mut members| {
            members.sort();
            members
        })
        .collect();
    groups.sort();

    let author_of: HashMap<&str, String> = inputs
        .sources
        .iter()
        .map(|(sid, record)| {
            let author = record.get("author");
            let name = if truthy(author) {
                text(author.unwrap_or(&Value::Null))
            } else {
                "unknown".to_owned()
            };
            (*sid, name)
        })
        .collect();
    let mut claims = inputs.claims.clone();
    claims.sort_by_key(|claim| str_of(claim, "id"));
    let mut claims_by_statement: HashMap<&str, Vec<&Obj>> = HashMap::new();
    for claim in claims {
        claims_by_statement
            .entry(str_of(claim, "statement_id"))
            .or_default()
            .push(claim);
    }
    // (`attested_by`, `stating_authors` rows) of a set of atoms.
    let attestation = |position: &[&str]| -> (Vec<String>, Vec<Value>) {
        let mut by_author: BTreeMap<String, (Set, Vec<&str>, Set)> = BTreeMap::new();
        let mut sorted = position.to_vec();
        sorted.sort();
        for sid in sorted {
            for claim in claims_by_statement.get(sid).into_iter().flatten() {
                let source = str_of(claim, "source_id");
                let author = author_of
                    .get(source)
                    .cloned()
                    .unwrap_or_else(|| "unknown".to_owned());
                let entry = by_author.entry(author).or_default();
                entry.0.insert(source);
                entry.1.push(str_of(claim, "id"));
                entry.2.insert(sid);
            }
        }
        let wanted: Set = position.iter().copied().collect();
        let mut attested = Vec::new();
        let rows = by_author
            .into_iter()
            .map(|(author, (sources, mut claims, statements))| {
                claims.sort();
                let covers = statements == wanted;
                if covers {
                    attested.push(author.clone());
                }
                json!({"author": author, "source_ids": sources, "claim_ids": claims,
                       "statement_ids": statements, "covers_all": covers})
            })
            .collect();
        (attested, rows)
    };
    let witnessing = |position: &[&str]| -> Vec<Value> {
        let wanted: Set = position.iter().copied().collect();
        certified_witnesses
            .iter()
            .filter(|witness| wanted.is_subset(&witness.satisfied))
            .map(|witness| json!({"kind": witness.kind, "id": witness.id}))
            .collect()
    };
    let entailed = |position: &[&str]| -> Vec<&str> {
        let chosen: Set = position.iter().copied().collect();
        supports
            .iter()
            .filter(|(sid, options)| {
                !chosen.contains(*sid)
                    && options
                        .iter()
                        .any(|option| !option.is_empty() && option.is_subset(&chosen))
            })
            .map(|(sid, _)| *sid)
            .collect()
    };

    struct Component<'v> {
        atoms: Vec<&'v str>,
        position_ids: Vec<String>,
        eliminated: Vec<&'v str>,
        truncated: bool,
        json: Value,
    }
    let mut components: Vec<Component> = Vec::new();
    let mut local_positions: BTreeMap<String, Value> = BTreeMap::new();
    let mut position_atoms_of: HashMap<String, Vec<&str>> = HashMap::new();
    let mut position_component: HashMap<String, usize> = HashMap::new();
    let mut hitting_truncated = false;
    for (index, members) in groups.into_iter().enumerate() {
        let member_set: Set = members.iter().copied().collect();
        let local: Vec<Set> = conflicts
            .iter()
            .filter(|conflict| conflict.is_subset(&member_set))
            .cloned()
            .collect();
        let (hitting, truncated) = minimal_hitting_sets(&local, bounds.hitting_set_limit);
        hitting_truncated |= truncated;
        let mut ids = Vec::new();
        for removed in &hitting {
            let position: Vec<&str> = member_set.difference(removed).copied().collect();
            let pid = position_id(position.iter().copied());
            let found = witnessing(&position);
            let (attested, rows) = attestation(&position);
            local_positions.insert(
                pid.clone(),
                json!({"id": pid, "atom_ids": position, "excluded_atom_ids": removed,
                       "entailed_statement_ids": entailed(&position),
                       "status": if found.is_empty() { "not_known_inconsistent" } else { "witnessed" },
                       "witnesses": found, "attested_by": attested, "stating_authors": rows}),
            );
            position_atoms_of.insert(pid.clone(), position);
            position_component.insert(pid.clone(), index);
            ids.push(pid);
        }
        ids.sort();
        let in_some: Set = ids
            .iter()
            .flat_map(|pid| position_atoms_of[pid].iter().copied())
            .collect();
        let eliminated: Vec<&str> = if truncated {
            Vec::new()
        } else {
            member_set.difference(&in_some).copied().collect()
        };
        let json = json!({"index": index, "atom_ids": members, "position_ids": ids,
                          "conflicts": local.iter().map(|conflict| of(conflict).to_json()).collect::<Vec<_>>(),
                          "eliminated_atom_ids": eliminated, "hitting_sets_truncated": truncated});
        components.push(Component {
            atoms: members,
            position_ids: ids,
            eliminated,
            truncated,
            json,
        });
    }
    let eliminated_atoms: Set = components
        .iter()
        .flat_map(|component| component.eliminated.iter().copied())
        .collect();

    // A truncated component has withheld positions, so the global count is
    // unknown. Python's product is an unbounded int: count exactly.
    let global_count: Option<Count> = (!hitting_truncated).then(|| {
        let mut count = Count::one();
        for component in &components {
            count.multiply(component.position_ids.len() as u32);
        }
        count
    });
    let mut global_positions: Vec<Value> = Vec::new();
    if !hitting_truncated {
        let lists: Vec<Vec<String>> = components
            .iter()
            .map(|component| component.position_ids.clone())
            .collect();
        product(&lists, |chosen| {
            if global_positions.len() >= bounds.global_position_limit {
                return false;
            }
            let mut position: Vec<&str> = chosen
                .iter()
                .flat_map(|pid| position_atoms_of[pid.as_str()].iter().copied())
                .collect();
            position.sort();
            let found = witnessing(&position);
            let mut local_ids: Vec<&str> = chosen.iter().map(|pid| pid.as_str()).collect();
            local_ids.sort();
            global_positions.push(json!({
                "id": position_id(position.iter().copied()), "local_position_ids": local_ids,
                "atom_count": position.len(),
                "status": if found.is_empty() { "not_known_inconsistent" } else { "witnessed" },
                "witnesses": found, "attested_by": attestation(&position).0,
            }));
            true
        });
    }

    let verified_routes: Vec<&Value> = inputs
        .routes
        .iter()
        .filter(|route| truthy(route.get("verified")))
        .collect();
    let dependents: HashMap<&str, usize> = inputs
        .seeds
        .iter()
        .map(|(sid, count)| (sid.as_str(), *count))
        .collect();
    let component_of: HashMap<&str, usize> = components
        .iter()
        .enumerate()
        .flat_map(|(index, component)| component.atoms.iter().map(move |atom| (*atom, index)))
        .collect();
    let rival_class = |seed: &str, rival: &str| -> &'static str {
        let pair: Set = [seed, rival].into_iter().collect();
        if conflicts
            .iter()
            .any(|conflict| conflict.is_subset(&pair) && conflict.contains(rival))
        {
            "certified_incompatible"
        } else {
            "uncertified"
        }
    };
    struct Row {
        statement_id: String,
        classification: &'static str,
        routes: usize,
        dependents: usize,
        json: Value,
    }
    let mut rows: Vec<Row> = Vec::new();
    for seed in &seed_ids {
        let seed_dependents = dependents.get(seed).copied().unwrap_or(0);
        let Some(&component_index) = component_of.get(seed) else {
            rows.push(Row {
                statement_id: (*seed).to_owned(),
                classification: "outside_bound",
                routes: 0,
                dependents: seed_dependents,
                json: json!({"statement_id": seed, "classification": "outside_bound", "values": {},
                             "in_position_ids": [], "out_position_ids": [], "routes": 0,
                             "cheapest_route_cost": null, "transitive_dependents": seed_dependents,
                             "rivals": [], "stating_authors": []}),
            });
            continue;
        };
        let component = &components[component_index];
        let mut values = Map::new();
        let (mut in_ids, mut out_ids) = (Vec::new(), Vec::new());
        for pid in local_positions.keys() {
            let value = if position_component[pid] != component_index {
                "undetermined"
            } else if position_atoms_of[pid].contains(seed) {
                in_ids.push(pid.clone());
                "in"
            } else {
                out_ids.push(pid.clone());
                "out"
            };
            values.insert(pid.clone(), json!(value));
        }
        let witnessed_in: Vec<&String> = in_ids
            .iter()
            .filter(|pid| local_positions[*pid]["status"] == "witnessed")
            .collect();
        let recorded: Vec<(&str, &str)> = rivals[seed]
            .iter()
            .map(|rival| (*rival, rival_class(seed, rival)))
            .collect();
        let classification = if component.truncated {
            "enumeration_truncated"
        } else if in_ids.is_empty() {
            "eliminated"
        } else if !out_ids.is_empty() {
            "split"
        } else if !recorded.is_empty()
            && recorded
                .iter()
                .all(|(rival, _)| eliminated_atoms.contains(rival))
        {
            "rivals_eliminated"
        } else if !recorded.is_empty() {
            "contested_uncertified"
        } else if !witnessed_in.is_empty() {
            "common_ground_candidate"
        } else {
            "unwitnessed"
        };
        let on_routes: Vec<&&Value> = verified_routes
            .iter()
            .filter(|route| {
                route["open_premise_statement_ids"]
                    .as_array()
                    .is_some_and(|ids| ids.iter().any(|id| id == seed))
            })
            .collect();
        let cheapest = on_routes
            .iter()
            .map(|route| &route["cost"])
            .min_by(|a, b| {
                a.as_f64()
                    .partial_cmp(&b.as_f64())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .cloned()
            .unwrap_or(Value::Null);
        let excluding: Vec<Value> = conflicts
            .iter()
            .filter(|conflict| conflict.contains(seed))
            .map(|conflict| of(conflict).to_json())
            .collect();
        let stating: Vec<Value> = attestation(&[seed])
            .1
            .into_iter()
            .map(|row| row["author"].clone())
            .collect();
        rows.push(Row {
            statement_id: (*seed).to_owned(),
            classification,
            routes: on_routes.len(),
            dependents: seed_dependents,
            json: json!({"statement_id": seed, "classification": classification, "values": values,
                         "in_position_ids": in_ids, "out_position_ids": out_ids,
                         "witnessed_in_position_ids": witnessed_in, "excluding_conflicts": excluding,
                         "routes": on_routes.len(), "cheapest_route_cost": cheapest,
                         "transitive_dependents": seed_dependents,
                         "rivals": recorded.iter().map(|(rival, class)| json!({"statement_id": rival, "class": class})).collect::<Vec<_>>(),
                         "stating_authors": stating}),
        });
    }
    let mut splits: Vec<&Row> = rows
        .iter()
        .filter(|row| row.classification == "split")
        .collect();
    splits.sort_by(|a, b| {
        (
            std::cmp::Reverse(a.routes),
            std::cmp::Reverse(a.dependents),
            &a.statement_id,
        )
            .cmp(&(
                std::cmp::Reverse(b.routes),
                std::cmp::Reverse(b.dependents),
                &b.statement_id,
            ))
    });
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for row in &rows {
        *counts.entry(row.classification).or_default() += 1;
    }
    let enumerated = global_positions.len();
    let report = json!({
        "scope": SCOPE,
        "bounds": {
            "universe": "one expansion round: root-path open premises, their recorded rivals, atoms of certified cores derivable from those, statements of models/consistency results that evaluate or commit to one of them",
            "max_atoms": bounds.max_atoms, "atom_count": universe.len(), "universe_truncated": universe_truncated,
            "closure_limit": bounds.closure_limit, "closure_truncated": closure.truncated,
            "core_combination_limit": bounds.core_combination_limit,
            "core_combinations_checked": combinations_checked.min(bounds.core_combination_limit),
            "core_combinations_truncated": core_truncated,
            "hitting_set_limit": bounds.hitting_set_limit, "hitting_sets_truncated": hitting_truncated,
            "global_position_limit": bounds.global_position_limit,
            "enumeration": "minimal conflicts via verified-entailment supports; components by shared conflicts; local positions = complements of minimal hitting sets (Berge); global positions = products",
        },
        "inputs": {
            "seed_statement_ids": seed_ids, "rival_statement_ids": rival_ids,
            "core_atom_statement_ids": added_cores, "witness_atom_statement_ids": added_witness,
            "certified_cores": cores.len(), "entailment_result_ids": rule_ids.len(),
            "witnesses": certified_witnesses.len(),
            "unconditionally_entailed_statement_ids": unconditional,
        },
        "universe": universe,
        "conflicts": conflicts.iter().map(|conflict| of(conflict).to_json()).collect::<Vec<_>>(),
        "components": components.iter().map(|component| component.json.clone()).collect::<Vec<_>>(),
        "positions": local_positions.values().collect::<Vec<_>>(),
        "global_positions": {
            // A count beyond u64 has no exact JSON number here (`null`); the
            // returned `Territory::global_count` keeps it exactly.
            "count": global_count.as_ref().and_then(Count::to_u64), "enumerated": enumerated,
            "truncated": global_count.as_ref().is_none_or(|count| count.exceeds(enumerated as u64)),
            "positions": global_positions,
        },
        "matrix": rows.iter().map(|row| row.json.clone()).collect::<Vec<_>>(),
        "common_ground_candidates": rows.iter()
            .filter(|row| row.classification == "common_ground_candidate")
            .map(|row| row.statement_id.clone()).collect::<Vec<_>>(),
        "territories": splits.iter().map(|row| json!({
            "statement_id": row.statement_id, "routes": row.routes,
            "transitive_dependents": row.dependents,
            "in_position_ids": row.json["in_position_ids"], "out_position_ids": row.json["out_position_ids"],
        })).collect::<Vec<_>>(),
        "classification_counts": counts,
        "defects": defects.iter().map(|(value, _)| value.clone()).collect::<Vec<_>>(),
    });
    Territory {
        report,
        defects: defects.into_iter().map(|(_, shown)| shown).collect(),
        global_count,
    }
}

/// Python `format_territory` of a [`territory_report`] (whose `report` may
/// carry other fields, such as the command's `root`).
pub fn format_territory(territory: &Territory) -> String {
    let (report, defects) = (&territory.report, &territory.defects);
    let array = |value: &Value| {
        value
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default()
            .to_vec()
    };
    let bounds = &report["bounds"];
    let components = array(&report["components"]);
    let constrained: Vec<&Value> = components
        .iter()
        .filter(|component| truthy(component.get("conflicts")))
        .collect();
    let positions = array(&report["positions"]);
    let witnessed = positions
        .iter()
        .filter(|position| position["status"] == "witnessed")
        .count();
    let global = &report["global_positions"];
    let global_witnessed = array(&global["positions"])
        .iter()
        .filter(|position| position["status"] == "witnessed")
        .count();
    let counts: Vec<String> = report["classification_counts"]
        .as_object()
        .into_iter()
        .flatten()
        .map(|(key, value)| format!("{key} {}", text(value)))
        .collect();
    let mut lines = vec![
        text(&report["scope"]),
        String::new(),
        format!(
            "Universe: {} atoms (max {}{}); {} minimal conflicts from {} certified cores; {} witnesses.",
            text(&bounds["atom_count"]),
            text(&bounds["max_atoms"]),
            if bounds["universe_truncated"] == true {
                ", truncated"
            } else {
                ""
            },
            array(&report["conflicts"]).len(),
            text(&report["inputs"]["certified_cores"]),
            text(&report["inputs"]["witnesses"])
        ),
        format!(
            "Components: {} ({} constrained by a conflict); local positions: {} ({} witnessed, {} not known inconsistent).",
            components.len(),
            constrained.len(),
            positions.len(),
            witnessed,
            positions.len() - witnessed
        ),
        format!(
            "Global positions: {} (enumerated {}, limit {}); witnessed: {}.",
            territory
                .global_count
                .as_ref()
                .map_or_else(|| "None".to_owned(), Count::decimal),
            text(&global["enumerated"]),
            text(&bounds["global_position_limit"]),
            global_witnessed
        ),
        format!("Root-path rows: {}", counts.join(", ")),
        String::new(),
    ];
    for component in &constrained {
        let atoms: Vec<String> = array(&component["atom_ids"]).iter().map(text).collect();
        lines.push(format!(
            "Component {}: {}",
            text(&component["index"]),
            atoms.join(", ")
        ));
        for conflict in array(&component["conflicts"]) {
            let results: Vec<String> = array(&conflict["result_ids"]).iter().map(text).collect();
            lines.push(format!(
                "  conflict {} ({}; {})",
                repr(&conflict["statement_ids"]),
                text(&conflict["kind"]),
                results.join(", ")
            ));
        }
        for pid in array(&component["position_ids"]) {
            let Some(position) = positions.iter().find(|item| item["id"] == pid) else {
                continue;
            };
            let authors: Vec<String> = array(&position["attested_by"]).iter().map(text).collect();
            let attested = if authors.is_empty() {
                "no author covers all atoms".to_owned()
            } else {
                authors.join(", ")
            };
            lines.push(format!(
                "  {} [{}] {}; attested by: {}",
                text(&pid),
                text(&position["status"]),
                repr(&position["atom_ids"]),
                attested
            ));
        }
    }
    let territories = array(&report["territories"]);
    if territories.is_empty() {
        lines.push(String::new());
        lines
            .push("Territories: none (no certified conflict separates root-path premises).".into());
    } else {
        lines.push(String::new());
        lines.push("Territories (split rows, by routes then dependents):".into());
        for row in &territories {
            lines.push(format!(
                "  {}: routes {}, dependents {}, in {}, out {}",
                text(&row["statement_id"]),
                text(&row["routes"]),
                text(&row["transitive_dependents"]),
                array(&row["in_position_ids"]).len(),
                array(&row["out_position_ids"]).len()
            ));
        }
    }
    let matrix = array(&report["matrix"]);
    let candidates = array(&report["common_ground_candidates"]);
    if !candidates.is_empty() {
        lines.push(String::new());
        lines.push("common_ground candidates (in every position of their component, witnessed, no recorded rival; no recorded rival usually means unexamined, not agreed):".into());
        for sid in &candidates {
            let stated: Vec<String> = matrix
                .iter()
                .rev()
                .find(|row| row["statement_id"] == *sid)
                .map(|row| array(&row["stating_authors"]).iter().map(text).collect())
                .unwrap_or_default();
            lines.push(format!(
                "  {} (stated by: {})",
                text(sid),
                if stated.is_empty() {
                    "no claim".to_owned()
                } else {
                    stated.join(", ")
                }
            ));
        }
    }
    let contested: Vec<&Value> = matrix
        .iter()
        .filter(|row| row["classification"] == "contested_uncertified")
        .collect();
    if !contested.is_empty() {
        lines.push(String::new());
        lines
            .push("Contested without certified incompatibility (recorded rivals, no core):".into());
        for row in contested {
            let rivals: Vec<String> = array(&row["rivals"])
                .iter()
                .map(|item| format!("{} ({})", text(&item["statement_id"]), text(&item["class"])))
                .collect();
            lines.push(format!(
                "  {}: {}",
                text(&row["statement_id"]),
                rivals.join(", ")
            ));
        }
    }
    for (defect, shown) in array(&report["defects"]).iter().zip(defects) {
        lines.push(format!("DEFECT {}: {shown}", text(&defect["kind"])));
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    //! The fixture of `scripts/test_territory.py` with the reports Python's
    //! `territory_report` and `format_territory` give for it
    //! (`testdata/territory-fixture.json`), and its assertions.
    use super::*;

    fn data() -> Value {
        serde_json::from_str(include_str!("testdata/territory-fixture.json")).unwrap()
    }

    fn index(value: &Value) -> Index<'_> {
        value
            .as_object()
            .unwrap()
            .iter()
            .map(|(id, record)| (id.as_str(), record.as_object().unwrap()))
            .collect()
    }

    fn objects(value: &Value) -> Vec<&Obj> {
        value
            .as_array()
            .unwrap()
            .iter()
            .map(|item| item.as_object().unwrap())
            .collect()
    }

    fn inputs(fixture: &Value) -> Inputs<'_> {
        Inputs {
            statements: index(&fixture["statements"]),
            arguments: index(&fixture["arguments"]),
            results: index(&fixture["results"]).into_iter().collect(),
            relations: objects(&fixture["relations"]),
            claims: objects(&fixture["claims"]),
            sources: index(&fixture["sources"]),
            models: objects(&fixture["models"]),
            transcription_results: ["TRANSCRIBED-CORE".to_owned()].into(),
            seeds: fixture["seeds"]
                .as_array()
                .unwrap()
                .iter()
                .map(|seed| {
                    (
                        seed["statement_id"].as_str().unwrap().to_owned(),
                        seed["transitive_dependent_arguments"]
                            .as_array()
                            .unwrap()
                            .len(),
                    )
                })
                .collect(),
            routes: fixture["routes"].as_array().unwrap().clone(),
        }
    }

    #[test]
    fn sha256_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(&[b'a'; 1000]),
            "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
        );
        assert_eq!(position_id(["R", "Q"]), position_id(["Q", "R"]));
    }

    #[test]
    fn matches_python_on_the_fixture() {
        let data = data();
        let fixture = inputs(&data["fixture"]);
        let territory = territory_report(&fixture, &Bounds::default());
        assert_eq!(territory.report, data["default"]);
        assert_eq!(format_territory(&territory), data["default_text"]);
        let bounds = Bounds {
            hitting_set_limit: 1,
            global_position_limit: 1,
            ..Bounds::default()
        };
        assert_eq!(
            territory_report(&fixture, &bounds).report,
            data["truncated"]
        );
    }

    #[test]
    fn python_assertions() {
        let data = data();
        let report = territory_report(&inputs(&data["fixture"]), &Bounds::default()).report;
        let conflicts: Vec<&Value> = report["conflicts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|conflict| &conflict["statement_ids"])
            .collect();
        // Q entails R, so Q with P also meets the certified core; the transcription is no core.
        assert_eq!(
            conflicts,
            [&json!(["P", "Q"]), &json!(["P", "R"]), &json!(["W", "Y"])]
        );
        let rows: HashMap<&str, &Value> = report["matrix"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| (row["statement_id"].as_str().unwrap(), row))
            .collect();
        assert_eq!(rows["P"]["classification"], "split");
        assert_eq!(rows["T"]["classification"], "common_ground_candidate");
        assert_eq!(rows["U"]["classification"], "contested_uncertified");
        assert_eq!(report["territories"][0]["statement_id"], "Q");
        assert_eq!(report["territories"][1]["statement_id"], "P");
    }

    #[test]
    fn witness_of_a_conflict_is_a_defect_with_python_repr() {
        let data = data();
        let fixture = &data["fixture"];
        let mut changed = fixture.clone();
        changed["models"][0]["evaluations"]
            .as_array_mut()
            .unwrap()
            .push(json!({"statement_id": "R", "value": "satisfies"}));
        changed["relations"]
            .as_array_mut()
            .unwrap()
            .push(json!({"id": "REL-R-ALT-P", "predicate": "alternative_to", "subject_id": "R", "object_id": "P"}));
        let bounds = Bounds {
            max_atoms: 9,
            ..Bounds::default()
        };
        let territory = territory_report(&inputs(&changed), &bounds);
        assert_eq!(territory.report, data["defect"]);
        assert_eq!(format_territory(&territory), data["defect_text"]);
    }

    #[test]
    fn count_is_exact_beyond_u64() {
        let mut count = Count::one();
        assert_eq!(count.decimal(), "1");
        for _ in 0..64 {
            count.multiply(2);
        }
        assert_eq!(count.to_u64(), None);
        assert_eq!(count.decimal(), "18446744073709551616");
        let mut fits = Count::one();
        for _ in 0..63 {
            fits.multiply(2);
        }
        assert_eq!(fits.to_u64(), Some(1 << 63));
        assert!(!fits.exceeds(1 << 63) && fits.exceeds((1 << 63) - 1));
        for _ in 0..192 {
            count.multiply(2);
        }
        // 2^256, as Python prints it.
        assert_eq!(
            count.decimal(),
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        );
        let mut zero = Count::one();
        zero.multiply(0);
        assert_eq!((zero.decimal(), zero.to_u64()), ("0".to_owned(), Some(0)));
    }

    #[test]
    fn global_count_beyond_u64_is_not_saturated() {
        // 64 independent two-atom conflicts within the default bounds give
        // 2^64 global positions (the review's case): never u64::MAX.
        let mut statements = Map::new();
        let mut arguments = Map::new();
        let mut results = Map::new();
        statements.insert(
            "FALSE".into(),
            json!({"id": "FALSE", "lean_declaration": FALSE_DECLARATION}),
        );
        let mut seeds = Vec::new();
        for index in 0..64 {
            let (seed, rival, id) = (
                format!("S{index:02}"),
                format!("R{index:02}"),
                format!("CORE{index:02}"),
            );
            for sid in [&seed, &rival] {
                statements.insert(sid.clone(), json!({"id": sid}));
            }
            arguments.insert(id.clone(), json!({"id": id, "premise_statement_ids": [seed, rival], "conclusion_statement_id": "FALSE"}));
            results.insert(id.clone(), json!({"id": id, "argument_id": id}));
            seeds.push((seed, 0));
        }
        let statements = Value::Object(statements);
        let arguments = Value::Object(arguments);
        let results = Value::Object(results);
        let rivals: Vec<Value> = (0..64)
            .map(|index| json!({"id": format!("REL{index:02}"), "predicate": "alternative_to",
                                "subject_id": format!("R{index:02}"), "object_id": format!("S{index:02}")}))
            .collect();
        let inputs = Inputs {
            statements: index(&statements),
            arguments: index(&arguments),
            results: index(&results).into_iter().collect(),
            relations: rivals
                .iter()
                .map(|relation| relation.as_object().unwrap())
                .collect(),
            claims: Vec::new(),
            sources: Index::new(),
            models: Vec::new(),
            transcription_results: BTreeSet::new(),
            seeds,
            routes: Vec::new(),
        };
        let territory = territory_report(&inputs, &Bounds::default());
        assert_eq!(territory.report["components"].as_array().unwrap().len(), 64);
        assert_eq!(
            territory.global_count.as_ref().unwrap().decimal(),
            "18446744073709551616"
        );
        assert!(territory.count_unrepresentable());
        assert!(territory.report["global_positions"]["count"].is_null());
        assert_eq!(territory.report["global_positions"]["truncated"], true);
        assert!(
            format_territory(&territory)
                .contains("Global positions: 18446744073709551616 (enumerated 64, limit 64)")
        );
    }
}
