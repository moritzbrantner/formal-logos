//! `truth connectivity`: how the statements of the corpus connect to the
//! frontier root, a diagnostic for the cohesive-graph goal (owner direction,
//! 2026-11-26).
//!
//! Two measures are reported. *Reaching the root* follows argument chains
//! upward: every premise or commitment of an argument reaches its
//! conclusion, whatever the argument's verification status. The *root
//! component* is the undirected connected component of the root over every
//! recorded contact between statements:
//!
//! - an argument joins each premise and commitment to its conclusion;
//! - an inference step of an argument joins its inputs, assumptions and
//!   discharged statements to its output, and its output to the argument's
//!   conclusion (these also count for reaching the root);
//! - a relation of any predicate (including `tests`) joins its endpoints, an
//!   endpoint standing for statements: a statement for itself, a claim for
//!   its statement, an argument for its conclusion and premises, a result
//!   for its argument's; `background_statement_ids` join the object;
//! - a `strength_comparison` or `strengthens` relation also joins its object
//!   to the statements it certifies: its delta and remainder statements and
//!   the statements of the results it names as evidence (implication,
//!   equivalence, separator, strictness);
//! - an attempt joins the statements it names.
//!
//! The method is that of the cohesive-graph measurement script
//! (`connectivity.py`), extended only by the `result` endpoint that `tests`
//! relations may use. Counts describe the shape of the graph; they are not a
//! score of research progress or philosophical merit, and contact is not
//! warrant: nothing here closes, supports or attacks a statement.
//!
//! [`gate`] (`truth connectivity --base REV`) turns the measure into a check
//! on *new* disconnection over the root's *typed* component: every edge above
//! except attempt co-citation, which records research activity rather than a
//! typed contact. A statement added since the base, moved out of that
//! component since the base, or planned at the base must be in the component
//! at the head or carry a `connection_plan` (docs/corpus-model.md) whose
//! target is in it. A plan is a record of intended work, not an edge: it never
//! joins the component. Typed contact is not the substantive root-route
//! obligation either: the gate checks that work is linked, not that a bridge
//! is proved. The report lists every recorded plan.

use crate::Corpus;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

type Obj = Map<String, Value>;

/// The classes of a statement outside the root component, in report order.
pub const CLASSES: [(&str, &str); 5] = [
    (
        "premise_free_result",
        "premise-free result (control/model/consistency)",
    ),
    ("source_reading", "source reading (has claims)"),
    (
        "conclusion_off_root",
        "conclusion of an argument (premises off-root)",
    ),
    ("only_in_attempt", "only in an attempt"),
    ("unused", "bare statement, unused"),
];

fn text<'a>(record: &'a Obj, key: &str) -> &'a str {
    record.get(key).and_then(Value::as_str).unwrap_or_default()
}

fn list<'a>(record: &'a Obj, key: &str) -> Vec<&'a str> {
    record
        .get(key)
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect()
}

/// The undirected contact graph over statements and the directed argument
/// graph (premise to conclusion).
struct Graph<'a> {
    statements: BTreeSet<&'a str>,
    undirected: HashMap<&'a str, BTreeSet<&'a str>>,
    /// Conclusion to the premises and commitments that reach it.
    premises_of: HashMap<&'a str, BTreeSet<&'a str>>,
}

impl<'a> Graph<'a> {
    fn link(&mut self, a: &'a str, b: &'a str) {
        if a != b && self.statements.contains(a) && self.statements.contains(b) {
            self.undirected.entry(a).or_default().insert(b);
            self.undirected.entry(b).or_default().insert(a);
        }
    }

    /// Join `premise` to `conclusion` and record that it reaches it.
    fn reach(&mut self, premise: &'a str, conclusion: &'a str) {
        self.link(premise, conclusion);
        if premise != conclusion
            && self.statements.contains(premise)
            && self.statements.contains(conclusion)
        {
            self.premises_of
                .entry(conclusion)
                .or_default()
                .insert(premise);
        }
    }

    /// The graph over every edge listed in the module documentation; without
    /// `attempts`, attempt co-citation is left out (the gate's typed contact).
    fn build(corpus: &'a Corpus, attempts: bool) -> Self {
        let statements: BTreeSet<&str> = corpus
            .records_by_id("statements")
            .map(|(id, _)| id)
            .collect();
        let mut graph = Self {
            statements,
            undirected: HashMap::new(),
            premises_of: HashMap::new(),
        };
        let arguments = corpus.records("arguments");
        let mut argument_statements: HashMap<&str, Vec<&str>> = HashMap::new();
        for argument in &arguments {
            let conclusion = text(argument, "conclusion_statement_id");
            let premises = list(argument, "premise_statement_ids");
            for premise in premises
                .iter()
                .copied()
                .chain(list(argument, "commitment_statement_ids"))
            {
                graph.link(premise, conclusion);
                if graph.statements.contains(premise) && graph.statements.contains(conclusion) {
                    graph
                        .premises_of
                        .entry(conclusion)
                        .or_default()
                        .insert(premise);
                }
            }
            argument_statements.insert(
                text(argument, "id"),
                std::iter::once(conclusion).chain(premises).collect(),
            );
        }
        // Inference steps of registered arguments: each input, assumption and
        // discharged statement joins (and reaches) the step's output, and the
        // output joins (and reaches) the argument's conclusion. Intermediate
        // statements are part of the argument graph.
        for argument in &arguments {
            let conclusion = text(argument, "conclusion_statement_id");
            for id in list(argument, "inference_ids") {
                let Some(step) = corpus.get("inferences", id).map(|record| &record.fields) else {
                    continue;
                };
                let output = text(step, "output_statement_id");
                graph.reach(output, conclusion);
                for input in list(step, "input_statement_ids")
                    .into_iter()
                    .chain(list(step, "assumption_statement_ids"))
                    .chain(list(step, "discharged_statement_ids"))
                {
                    graph.reach(input, output);
                }
            }
        }
        let claim_statement: HashMap<&str, &str> = corpus
            .records("claims")
            .into_iter()
            .map(|claim| (text(claim, "id"), text(claim, "statement_id")))
            .collect();
        let result_argument: HashMap<&str, &str> = corpus
            .records("results")
            .into_iter()
            .map(|result| (text(result, "id"), text(result, "argument_id")))
            .collect();
        let endpoint = |kind: &str, id: &'a str| -> Vec<&'a str> {
            let argument = |id: &str| argument_statements.get(id).cloned().unwrap_or_default();
            match kind {
                "statement" => vec![id],
                "claim" => claim_statement.get(id).copied().into_iter().collect(),
                "argument" => argument(id),
                "result" => result_argument
                    .get(id)
                    .map(|id| argument(id))
                    .unwrap_or_default(),
                _ => Vec::new(),
            }
        };
        for relation in corpus.records("relations") {
            let subjects = endpoint(text(relation, "subject_kind"), text(relation, "subject_id"));
            let objects = endpoint(text(relation, "object_kind"), text(relation, "object_id"));
            for &a in &subjects {
                for &b in &objects {
                    graph.link(a, b);
                }
            }
            for background in list(relation, "background_statement_ids") {
                graph.link(text(relation, "object_id"), background);
            }
            // A strength registration or comparison is typed contact for the
            // statements it certifies: the delta and remainder statements of
            // a `strength_comparison`, and the statements of the results a
            // `strength_comparison` or `strengthens` record names as its
            // evidence (implication, equivalence, separator, strictness).
            if matches!(
                text(relation, "predicate"),
                "strength_comparison" | "strengthens"
            ) {
                let object = text(relation, "object_id");
                let mut certified: Vec<&str> = ["delta_statement_id", "remainder_statement_id"]
                    .into_iter()
                    .map(|field| text(relation, field))
                    .filter(|id| !id.is_empty())
                    .collect();
                let mut results: Vec<&str> = ["verification_result_id", "strictness_result_id"]
                    .into_iter()
                    .map(|field| text(relation, field))
                    .collect();
                if let Some(evidence) = relation
                    .get("evidence_result_ids")
                    .and_then(Value::as_object)
                {
                    results.extend(evidence.values().filter_map(Value::as_str));
                }
                if let Some(separator) = relation.get("separator").and_then(Value::as_object) {
                    results.extend(separator.get("result_id").and_then(Value::as_str));
                }
                for result in results.into_iter().filter(|id| !id.is_empty()) {
                    certified.extend(endpoint("result", result));
                }
                for statement in certified {
                    graph.link(object, statement);
                }
            }
        }
        for attempt in corpus.records("attempts").into_iter().filter(|_| attempts) {
            let named: Vec<&str> = list(attempt, "statement_ids")
                .into_iter()
                .filter(|id| graph.statements.contains(id))
                .collect();
            if let Some((&first, rest)) = named.split_first() {
                for &other in rest {
                    graph.link(first, other);
                }
            }
        }
        graph
    }

    fn neighbours(&self, id: &str) -> impl Iterator<Item = &'a str> + '_ {
        self.undirected.get(id).into_iter().flatten().copied()
    }

    fn component(&self, start: &'a str) -> BTreeSet<&'a str> {
        let mut seen = BTreeSet::from([start]);
        let mut queue = VecDeque::from([start]);
        while let Some(node) = queue.pop_front() {
            for next in self.neighbours(node) {
                if seen.insert(next) {
                    queue.push_back(next);
                }
            }
        }
        seen
    }

    fn reaching(&self, root: &'a str) -> BTreeSet<&'a str> {
        let mut seen = BTreeSet::from([root]);
        let mut queue = VecDeque::from([root]);
        while let Some(node) = queue.pop_front() {
            for &premise in self.premises_of.get(node).into_iter().flatten() {
                if seen.insert(premise) {
                    queue.push_back(premise);
                }
            }
        }
        seen
    }
}

/// The class of a statement outside the root component (first match wins).
struct Classifier<'a> {
    premise_free: HashSet<&'a str>,
    claimed: HashSet<&'a str>,
    concluded: HashSet<&'a str>,
    in_attempt: HashSet<&'a str>,
}

impl<'a> Classifier<'a> {
    fn new(corpus: &'a Corpus) -> Self {
        let mut classifier = Self {
            premise_free: HashSet::new(),
            claimed: HashSet::new(),
            concluded: HashSet::new(),
            in_attempt: HashSet::new(),
        };
        for argument in corpus.records("arguments") {
            let conclusion = text(argument, "conclusion_statement_id");
            classifier.concluded.insert(conclusion);
            if list(argument, "premise_statement_ids").is_empty() {
                classifier.premise_free.insert(conclusion);
            }
        }
        for claim in corpus.records("claims") {
            classifier.claimed.insert(text(claim, "statement_id"));
        }
        for attempt in corpus.records("attempts") {
            classifier.in_attempt.extend(list(attempt, "statement_ids"));
        }
        classifier
    }

    fn class(&self, id: &str) -> &'static str {
        if self.premise_free.contains(id) {
            CLASSES[0].0
        } else if self.claimed.contains(id) {
            CLASSES[1].0
        } else if self.concluded.contains(id) {
            CLASSES[2].0
        } else if self.in_attempt.contains(id) {
            CLASSES[3].0
        } else {
            CLASSES[4].0
        }
    }

    fn counts<'s>(&self, ids: impl Iterator<Item = &'s str>) -> Value {
        let mut counts: BTreeMap<&str, usize> = CLASSES.iter().map(|(key, _)| (*key, 0)).collect();
        for id in ids {
            *counts.entry(self.class(id)).or_default() += 1;
        }
        json!(counts)
    }
}

/// The connectivity report for `root`. `list_isolated` isolated statements
/// are listed with their class (premise-free results first, then by label).
pub fn report(corpus: &Corpus, root: &str, list_isolated: usize) -> Value {
    let graph = Graph::build(corpus, true);
    let Some(&root) = graph.statements.get(root) else {
        return json!({"root": root, "root_known": false});
    };
    let plans = plans(corpus, &owned_component(corpus, root));
    let label = |id: &str| -> String {
        corpus
            .get("statements", id)
            .map(|record| text(&record.fields, "label").to_owned())
            .unwrap_or_default()
    };
    let reaching = graph.reaching(root);
    let component = graph.component(root);
    let isolated: Vec<&str> = graph
        .statements
        .iter()
        .copied()
        .filter(|id| graph.undirected.get(id).is_none_or(BTreeSet::is_empty))
        .collect();
    let islands: Vec<&str> = graph
        .statements
        .iter()
        .copied()
        .filter(|id| !component.contains(id) && graph.undirected.contains_key(id))
        .collect();
    let mut seen: HashSet<&str> = HashSet::new();
    let mut components: Vec<BTreeSet<&str>> = Vec::new();
    for &id in &islands {
        if seen.contains(id) {
            continue;
        }
        let members = graph.component(id);
        seen.extend(members.iter().copied());
        components.push(members);
    }
    // Largest first; ties by their first statement id.
    components.sort_by(|a, b| {
        b.len()
            .cmp(&a.len())
            .then_with(|| a.first().cmp(&b.first()))
    });
    let classifier = Classifier::new(corpus);
    let mut listed: Vec<(usize, String, &str)> = isolated
        .iter()
        .map(|&id| {
            let class = classifier.class(id);
            let rank = CLASSES.iter().position(|(key, _)| *key == class);
            (rank.unwrap_or(CLASSES.len()), label(id), id)
        })
        .collect();
    listed.sort();
    listed.truncate(list_isolated);
    json!({
        "root": root,
        "root_known": true,
        "statements": graph.statements.len(),
        "reaching_root": reaching.len(),
        "root_component": component.len(),
        "in_other_components": islands.len(),
        "isolated": isolated.len(),
        "other_components": components.iter().map(|members| json!({
            "size": members.len(),
            "example": members.first().map(|id| json!({"id": id, "label": label(id)})),
            "statement_ids": members,
        })).collect::<Vec<_>>(),
        "classes": {
            "isolated": classifier.counts(isolated.iter().copied()),
            "other_components": classifier.counts(islands.iter().copied()),
        },
        "isolated_listed": listed.iter().map(|(_, label, id)| json!({
            "id": id, "label": label, "class": classifier.class(id),
        })).collect::<Vec<_>>(),
        "plans": plans,
    })
}

/// Every recorded `connection_plan`, judged against `component` (the root's
/// typed component, [`owned_component`]): `outstanding` while its statement is
/// outside it, `ready_for_plan_review` once it has joined. Joining shows a
/// contact, not that the named bridge was delivered.
fn plans(corpus: &Corpus, component: &BTreeSet<String>) -> Vec<Value> {
    let label = |id: &str| -> String {
        corpus
            .get("statements", id)
            .map(|record| text(&record.fields, "label").to_owned())
            .unwrap_or_default()
    };
    corpus
        .records_by_id("statements")
        .filter_map(|(id, record)| {
            let plan = record.fields.get("connection_plan")?.as_object()?;
            let target = text(plan, "target_statement_id");
            Some(json!({
                "id": id,
                "label": label(id),
                "status": if component.contains(id) { "ready_for_plan_review" } else { "outstanding" },
                "target": {"id": target, "label": label(target),
                           "in_root_component": component.contains(target)},
                "missing_bridge": text(plan, "missing_bridge"),
                "blocker": text(plan, "blocker"),
            }))
        })
        .collect()
}

fn format_plans(plans: &[Value], lines: &mut Vec<String>) {
    let named = |entry: &Value| {
        format!(
            "{} [{}]",
            clip(entry["label"].as_str().unwrap_or_default(), 100),
            short(entry["id"].as_str().unwrap_or_default())
        )
    };
    for (status, title) in [
        (
            "outstanding",
            "outstanding connection plans (outside the root's typed component):",
        ),
        (
            "ready_for_plan_review",
            "connection plans ready for plan review (the statement joined the root's typed component; \
             check that the named bridge was delivered before removing the plan):",
        ),
    ] {
        let listed: Vec<&Value> = plans
            .iter()
            .filter(|plan| plan["status"] == status)
            .collect();
        if listed.is_empty() {
            continue;
        }
        lines.push(title.into());
        for plan in listed {
            lines.push(format!("  {} -> {}", named(plan), named(&plan["target"])));
            lines.push(format!(
                "    missing bridge: {}",
                plan["missing_bridge"].as_str().unwrap_or_default()
            ));
            lines.push(format!(
                "    blocker: {}",
                plan["blocker"].as_str().unwrap_or_default()
            ));
        }
    }
}

fn class_line(name: &str, counts: &Value) -> String {
    let parts: Vec<String> = CLASSES
        .iter()
        .map(|(key, title)| format!("{title}: {}", counts[*key].as_u64().unwrap_or(0)))
        .collect();
    format!("{name}: {}", parts.join("; "))
}

fn short(id: &str) -> &str {
    id.get(..8).unwrap_or(id)
}

fn clip(label: &str, width: usize) -> String {
    label.chars().take(width).collect()
}

/// The text form of [`report`].
pub fn format(report: &Value) -> String {
    let root = report["root"].as_str().unwrap_or_default();
    if report["root_known"] != true {
        return format!("unknown root statement {root}");
    }
    let number = |key: &str| report[key].as_u64().unwrap_or(0);
    let components = report["other_components"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let sizes: Vec<String> = components
        .iter()
        .take(10)
        .map(|component| component["size"].to_string())
        .collect();
    let mut lines = vec![
        format!("Connectivity of the corpus graph to {root} (diagnostic; contact is not warrant)"),
        format!("statements: {}", number("statements")),
        format!(
            "reach root via argument chains: {}",
            number("reaching_root")
        ),
        format!(
            "in root's component via any edge (arguments, relations, attempts): {}",
            number("root_component")
        ),
        format!(
            "in other components (connected among themselves, not to root): {}",
            number("in_other_components")
        ),
        format!("isolated (no edge at all): {}", number("isolated")),
        format!(
            "non-root components: {}; largest sizes: [{}]",
            components.len(),
            sizes.join(", ")
        ),
    ];
    for component in components.iter().take(5) {
        let example = &component["example"];
        lines.push(format!(
            "  size {}: e.g. {} [{}]",
            component["size"],
            clip(example["label"].as_str().unwrap_or_default(), 90),
            short(example["id"].as_str().unwrap_or_default())
        ));
    }
    lines.push(class_line("isolated", &report["classes"]["isolated"]));
    lines.push(class_line(
        "islands",
        &report["classes"]["other_components"],
    ));
    let listed = report["isolated_listed"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    if !listed.is_empty() {
        lines.push("isolated statements:".into());
        for entry in &listed {
            lines.push(format!(
                "  {} [{}] ({})",
                clip(entry["label"].as_str().unwrap_or_default(), 100),
                short(entry["id"].as_str().unwrap_or_default()),
                entry["class"].as_str().unwrap_or_default()
            ));
        }
    }
    format_plans(
        report["plans"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default(),
        &mut lines,
    );
    lines.join("\n")
}

/// The statement a statement's `connection_plan` targets, when it records one
/// (`truth check` validates the plan's shape and that the target resolves).
pub fn plan_target(statement: &Obj) -> Option<&str> {
    statement
        .get("connection_plan")
        .and_then(Value::as_object)
        .map(|plan| text(plan, "target_statement_id"))
        .filter(|target| !target.is_empty())
}

/// The root's *typed* component as owned statement ids (empty for an unknown
/// root): every edge of the report except attempt co-citation. An attempt
/// that names two statements records research activity, not a typed contact,
/// so the gate never accepts it as a path to the root.
fn owned_component(corpus: &Corpus, root: &str) -> BTreeSet<String> {
    let graph = Graph::build(corpus, false);
    match graph.statements.get(root) {
        Some(&root) => graph
            .component(root)
            .into_iter()
            .map(str::to_owned)
            .collect(),
        None => BTreeSet::new(),
    }
}

/// The connectivity gate (owner direction, 2026-11-26: disconnected work must
/// not accumulate again), over the root's typed component ([`owned_component`],
/// without attempt co-citation) at both revisions. It judges each statement
/// of `head` outside that component that is new since `base` (present at the
/// head, absent at the base), was in the component at the base, or carried a
/// `connection_plan` at the base. Each passes only with a `connection_plan`
/// whose target statement is in the head's typed component. Statements
/// outside it at the base that never had a plan are not judged. Both corpora
/// are judged by this binary's rules ("head rules on base data");
/// `base_label` names the base in the report.
pub fn gate(head: &Corpus, base: &Corpus, root: &str, base_label: &str) -> Value {
    let component = owned_component(head, root);
    let base_component = owned_component(base, root);
    let base_statements: HashSet<&str> =
        base.records_by_id("statements").map(|(id, _)| id).collect();
    let head_statements: HashSet<&str> =
        head.records_by_id("statements").map(|(id, _)| id).collect();
    let base_planned: HashSet<&str> = base
        .records_by_id("statements")
        .filter(|(_, record)| plan_target(&record.fields).is_some())
        .map(|(id, _)| id)
        .collect();
    let label = |id: &str| -> String {
        head.get("statements", id)
            .map(|record| text(&record.fields, "label").to_owned())
            .unwrap_or_default()
    };
    let mut new_count = 0;
    let mut judged: Vec<Value> = Vec::new();
    let mut review: Vec<Value> = Vec::new();
    for (id, record) in head.records_by_id("statements") {
        let is_new = !base_statements.contains(id);
        new_count += usize::from(is_new);
        let inside = component.contains(id);
        let target = plan_target(&record.fields);
        if inside {
            if target.is_some() {
                review.push(json!({"id": id, "label": label(id)}));
            }
            continue;
        }
        let change = if is_new {
            "new"
        } else if base_component.contains(id) {
            "moved_out"
        } else if base_planned.contains(id) {
            "previously_planned"
        } else {
            continue;
        };
        // A plan counts only when it is well formed by `truth check`'s rule,
        // so the gate does not depend on `check` having run first.
        let invalid =
            crate::check::validate_connection_plan(&record.fields, &head_statements).err();
        let (status, target) = match (target, &invalid) {
            (None, None) => ("no_plan", Value::Null),
            (target, Some(_)) => (
                "invalid_plan",
                target.map_or(
                    Value::Null,
                    |target| json!({"id": target, "label": label(target)}),
                ),
            ),
            (Some(target), None) => (
                if component.contains(target) {
                    "planned"
                } else {
                    "plan_target_off_root"
                },
                json!({"id": target, "label": label(target)}),
            ),
        };
        judged.push(json!({
            "id": id, "label": label(id), "change": change,
            "status": status, "plan_target": target, "plan_error": invalid,
        }));
    }
    let offending: Vec<&Value> = judged
        .iter()
        .filter(|entry| entry["status"] != "planned")
        .collect();
    json!({
        "root": root,
        "root_known": head.get("statements", root).is_some(),
        "base": base_label,
        "passed": offending.is_empty() && head.get("statements", root).is_some(),
        "new_statements": new_count,
        "judged": judged,
        "offending": offending,
        "ready_for_plan_review": review,
    })
}

/// [`gate`] against a Git revision of `checkout`, read from its committed
/// corpus ([`crate::frontier::base_tree`]), never by running its tooling.
pub fn revision_gate(
    checkout: &std::path::Path,
    head: &Corpus,
    revision: &str,
    root: &str,
) -> Result<Value, String> {
    let tree = crate::frontier::base_tree(checkout, revision)?;
    let base = Corpus::load(tree.path()).map_err(|error| {
        format!(
            "corpus at {revision} failed: {}: {}",
            error.path, error.message
        )
    })?;
    Ok(gate(head, &base, root, revision))
}

/// The text form of [`gate`].
pub fn format_gate(report: &Value) -> String {
    let root = report["root"].as_str().unwrap_or_default();
    let base = report["base"].as_str().unwrap_or_default();
    if report["root_known"] != true {
        return format!("unknown root statement {root}");
    }
    let entries = |key: &str| report[key].as_array().cloned().unwrap_or_default();
    let named = |entry: &Value| {
        format!(
            "{} [{}]",
            clip(entry["label"].as_str().unwrap_or_default(), 100),
            short(entry["id"].as_str().unwrap_or_default())
        )
    };
    let judged = entries("judged");
    let count = |change: &str, planned: bool| {
        judged
            .iter()
            .filter(|entry| entry["change"] == change && (entry["status"] == "planned") == planned)
            .count()
    };
    let verdict = if report["passed"] == true {
        "passed"
    } else {
        "FAILED"
    };
    let mut lines = vec![
        format!(
            "Connectivity gate against {base} (root {root}; typed contact, attempt co-citation excluded): {verdict}"
        ),
        format!(
            "new statements: {}; outside the root component: {} with a valid connection plan, {} without",
            report["new_statements"],
            count("new", true),
            count("new", false)
        ),
        format!(
            "statements moved out of the root component: {} with a valid connection plan, {} without",
            count("moved_out", true),
            count("moved_out", false)
        ),
        format!(
            "previously planned statements still outside it: {} with a valid connection plan, {} without",
            count("previously_planned", true),
            count("previously_planned", false)
        ),
    ];
    let offending = entries("offending");
    if !offending.is_empty() {
        lines.push(
            "Each statement below must join the root's typed component (an argument or inference \
             step that uses it, or a relation such as `tests` whose endpoint is it or a claim, \
             argument or result about it; an attempt naming it does not count) or record a \
             `connection_plan` naming a root-component target statement, the missing bridge and \
             its blocker (docs/corpus-model.md; AGENTS.md, \"Connect every library to the case\"):"
                .into(),
        );
        for entry in &offending {
            let change = match entry["change"].as_str() {
                Some("new") => "new statement outside the root component",
                Some("moved_out") => "moved out of the root component",
                _ => "planned at the base and still outside the root component",
            };
            let reason = match entry["status"].as_str() {
                Some("no_plan") => "no connection plan".to_owned(),
                Some("invalid_plan") => format!(
                    "invalid connection plan: {}",
                    entry["plan_error"].as_str().unwrap_or_default()
                ),
                _ => format!(
                    "its plan target {} is outside the root component",
                    named(&entry["plan_target"])
                ),
            };
            lines.push(format!("  {}: {change}; {reason}", named(entry)));
        }
    }
    let planned: Vec<&Value> = judged
        .iter()
        .filter(|entry| entry["status"] == "planned")
        .collect();
    if !planned.is_empty() {
        lines.push("outside the root component with a valid connection plan (outstanding):".into());
        for entry in planned {
            lines.push(format!(
                "  {} -> {}",
                named(entry),
                named(&entry["plan_target"])
            ));
        }
    }
    let review = entries("ready_for_plan_review");
    if !review.is_empty() {
        lines.push(
            "connection plans ready for plan review (the statement joined the root's typed \
             component; joining does not show that the named bridge was delivered: check it \
             before removing the plan):"
                .into(),
        );
        for entry in &review {
            lines.push(format!("  {}", named(entry)));
        }
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs, path::PathBuf};

    struct Checkout(PathBuf);

    impl Checkout {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir()
                .join(format!("truth-connectivity-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&path);
            fs::create_dir_all(path.join("corpus")).unwrap();
            Self(path)
        }

        fn write(&self, kind: &str, record: Value) {
            let directory = self.0.join("corpus").join(kind);
            fs::create_dir_all(&directory).unwrap();
            let id = record["id"].as_str().unwrap().to_owned();
            fs::write(directory.join(format!("{id}.json")), record.to_string()).unwrap();
        }
    }

    impl Drop for Checkout {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn statement(id: &str) -> Value {
        json!({"id": id, "label": id, "paraphrase": id})
    }

    /// ROOT <- P (argument); a premise-free control C tests P only once a
    /// `tests` relation names it; Q is a source reading on an island with R
    /// (an attempt names both); U is unused.
    #[test]
    fn components_classes_and_the_tests_endpoint() {
        let checkout = Checkout::new("components");
        for id in ["ROOT", "P", "C", "Q", "R", "U"] {
            checkout.write("statements", statement(id));
        }
        checkout.write(
            "arguments",
            json!({"id": "ARG-ROOT", "premise_statement_ids": ["P"],
                   "conclusion_statement_id": "ROOT", "meaning": "m", "inference_ids": ["I"]}),
        );
        checkout.write(
            "arguments",
            json!({"id": "ARG-C", "premise_statement_ids": [],
                   "conclusion_statement_id": "C", "meaning": "m", "inference_ids": ["I"]}),
        );
        checkout.write(
            "claims",
            json!({"id": "CL-Q", "statement_id": "Q", "source_id": "S", "locator": "1",
                   "interpretation": "i", "status": "s"}),
        );
        checkout.write(
            "attempts",
            json!({"id": "ATT", "statement_ids": ["Q", "R"]}),
        );
        let corpus = Corpus::load(&checkout.0).unwrap();
        let first = report(&corpus, "ROOT", 10);
        assert_eq!(first["reaching_root"], 2);
        assert_eq!(first["root_component"], 2);
        assert_eq!(first["in_other_components"], 2);
        assert_eq!(first["isolated"], 2);
        assert_eq!(first["other_components"][0]["size"], 2);
        assert_eq!(first["classes"]["isolated"]["premise_free_result"], 1);
        assert_eq!(first["classes"]["isolated"]["unused"], 1);
        assert_eq!(first["classes"]["other_components"]["source_reading"], 1);
        assert_eq!(first["classes"]["other_components"]["only_in_attempt"], 1);
        assert_eq!(first["isolated_listed"][0]["id"], "C");
        assert_eq!(first["isolated_listed"][1]["id"], "U");

        checkout.write(
            "results",
            json!({"id": "RES-C", "argument_id": "ARG-C", "challenge_module": "c",
                   "solution_module": "s", "theorem": "t", "comparator_config": "f",
                   "status": "verified"}),
        );
        checkout.write(
            "relations",
            json!({"id": "REL", "subject_kind": "result", "subject_id": "RES-C",
                   "predicate": "tests", "object_kind": "statement", "object_id": "P"}),
        );
        let corpus = Corpus::load(&checkout.0).unwrap();
        let second = report(&corpus, "ROOT", 0);
        // Contact, not derivation: C joins the component but does not reach.
        assert_eq!(second["reaching_root"], 2);
        assert_eq!(second["root_component"], 3);
        assert_eq!(second["isolated"], 1);
        assert_eq!(second["isolated_listed"], json!([]));
    }

    /// ROOT <- W (argument). S strengthens W; a `strength_comparison` of S
    /// over W names the delta D, an equivalence result concluding E and a
    /// separator result concluding X; a `strengthens` record names the
    /// strictness result concluding K. All of them join the root component
    /// without a `tests` edge; an unrelated Z does not.
    #[test]
    fn strength_records_are_typed_contact_for_their_certificates() {
        let checkout = Checkout::new("strength");
        for id in ["ROOT", "W", "S", "D", "E", "X", "K", "Z"] {
            checkout.write("statements", statement(id));
        }
        checkout.write("arguments", argument("ARG-ROOT", &["W"], "ROOT"));
        for (argument_id, conclusion) in [("ARG-E", "E"), ("ARG-X", "X"), ("ARG-K", "K")] {
            checkout.write("arguments", argument(argument_id, &[], conclusion));
            checkout.write(
                "results",
                json!({"id": format!("RES-{conclusion}"), "argument_id": argument_id,
                       "challenge_module": "c", "solution_module": "s", "theorem": "t",
                       "comparator_config": "f", "status": "verified"}),
            );
        }
        let corpus = Corpus::load(&checkout.0).unwrap();
        assert_eq!(report(&corpus, "ROOT", 0)["root_component"], 2);
        checkout.write(
            "relations",
            json!({"id": "CMP", "subject_kind": "statement", "subject_id": "S",
                   "predicate": "strength_comparison", "object_kind": "statement",
                   "object_id": "W", "delta_statement_id": "D",
                   "background_statement_ids": [],
                   "evidence_result_ids": {"equivalence": "RES-E"},
                   "separator": {"setting": "s", "result_id": "RES-X"}}),
        );
        checkout.write(
            "relations",
            json!({"id": "STR", "subject_kind": "statement", "subject_id": "S",
                   "predicate": "strengthens", "object_kind": "statement", "object_id": "W",
                   "strictness_result_id": "RES-K"}),
        );
        let corpus = Corpus::load(&checkout.0).unwrap();
        let after = report(&corpus, "ROOT", 0);
        // ROOT, W, S, D, E, X, K: contact, not derivation.
        assert_eq!(after["root_component"], 7);
        assert_eq!(after["reaching_root"], 2);
        assert_eq!(after["isolated"], 1);
    }

    fn argument(id: &str, premises: &[&str], conclusion: &str) -> Value {
        json!({"id": id, "premise_statement_ids": premises,
               "conclusion_statement_id": conclusion, "meaning": "m", "inference_ids": ["NONE"]})
    }

    fn planned(id: &str, target: &str) -> Value {
        json!({"id": id, "label": id, "paraphrase": id, "connection_plan": {
            "target_statement_id": target, "missing_bridge": "b", "blocker": "x"}})
    }

    fn ids(report: &Value, key: &str) -> Vec<String> {
        report[key]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["id"].as_str().unwrap().to_owned())
            .collect()
    }

    /// BASE: ROOT <- P <- M (arguments); O is an island that never had a
    /// plan; Q1 and Q2 are islands planned at the base. HEAD drops the
    /// argument M -> P (M moves out), keeps Q1's plan, drops Q2's, and adds:
    /// N1 joined by an inference step, N2 by a `tests` relation, N3
    /// unconnected, N4 planned towards P, N5 planned towards the island O, N6
    /// joined to P only by an attempt that names both.
    #[test]
    fn the_gate_judges_new_moved_out_and_planned_statements_by_typed_contact() {
        let base = Checkout::new("gate-base");
        for id in ["ROOT", "P", "M", "O"] {
            base.write("statements", statement(id));
        }
        base.write("statements", planned("Q1", "P"));
        base.write("statements", planned("Q2", "P"));
        base.write("arguments", argument("ARG-ROOT", &["P"], "ROOT"));
        base.write("arguments", argument("ARG-P", &["M"], "P"));
        let head = Checkout::new("gate-head");
        for id in ["ROOT", "P", "M", "O", "N1", "N2", "N3", "N6", "Q2"] {
            head.write("statements", statement(id));
        }
        head.write("statements", planned("N4", "P"));
        head.write("statements", planned("N5", "O"));
        head.write("statements", planned("Q1", "P"));
        head.write(
            "arguments",
            json!({"id": "ARG-ROOT", "premise_statement_ids": ["P"],
                   "conclusion_statement_id": "ROOT", "meaning": "m", "inference_ids": ["I"]}),
        );
        head.write(
            "inferences",
            json!({"id": "I", "rule": "r", "meaning": "m", "input_statement_ids": ["N1"],
                   "assumption_statement_ids": [], "discharged_statement_ids": [],
                   "output_statement_id": "P"}),
        );
        head.write("arguments", argument("ARG-N2", &[], "N2"));
        head.write(
            "results",
            json!({"id": "RES-N2", "argument_id": "ARG-N2", "challenge_module": "c",
                   "solution_module": "s", "theorem": "t", "comparator_config": "f",
                   "status": "verified"}),
        );
        head.write(
            "relations",
            json!({"id": "REL", "subject_kind": "result", "subject_id": "RES-N2",
                   "predicate": "tests", "object_kind": "statement", "object_id": "P"}),
        );
        head.write(
            "attempts",
            json!({"id": "ATT", "statement_ids": ["P", "N6"]}),
        );
        let base_corpus = Corpus::load(&base.0).unwrap();
        let head_corpus = Corpus::load(&head.0).unwrap();

        // The diagnostic counts the attempt as contact; the gate does not.
        // (ROOT, P, N1, N2 and N6 there; N6 is judged below.)
        let diagnostic = report(&head_corpus, "ROOT", 0);
        assert_eq!(diagnostic["root_component"], 5);
        assert_eq!(owned_component(&head_corpus, "ROOT").len(), 4);

        let report = gate(&head_corpus, &base_corpus, "ROOT", "BASE");
        assert_eq!(report["new_statements"], 6);
        assert_eq!(report["passed"], false);
        assert_eq!(
            ids(&report, "judged"),
            ["M", "N3", "N4", "N5", "N6", "Q1", "Q2"]
        );
        assert_eq!(ids(&report, "offending"), ["M", "N3", "N5", "N6", "Q2"]);
        let status = |id: &str| {
            report["judged"]
                .as_array()
                .unwrap()
                .iter()
                .find(|entry| entry["id"] == id)
                .map(|entry| (entry["change"].clone(), entry["status"].clone()))
                .unwrap()
        };
        assert_eq!(status("M"), (json!("moved_out"), json!("no_plan")));
        assert_eq!(status("N4"), (json!("new"), json!("planned")));
        assert_eq!(status("N5"), (json!("new"), json!("plan_target_off_root")));
        assert_eq!(status("N6"), (json!("new"), json!("no_plan")));
        assert_eq!(
            status("Q1"),
            (json!("previously_planned"), json!("planned"))
        );
        assert_eq!(
            status("Q2"),
            (json!("previously_planned"), json!("no_plan"))
        );
        let text = format_gate(&report);
        assert!(text.contains("FAILED"), "{text}");
        for line in [
            "  N3 [N3]: new statement outside the root component; no connection plan",
            "  N6 [N6]: new statement outside the root component; no connection plan",
            "  M [M]: moved out of the root component; no connection plan",
            "  Q2 [Q2]: planned at the base and still outside the root component; no connection plan",
            "  N5 [N5]: new statement outside the root component; its plan target O [O] is outside the root component",
            "  Q1 [Q1] -> P [P]",
        ] {
            assert!(text.contains(line), "{line}\n{text}");
        }

        // Valid plans pass the gate; a plan on a statement that has joined
        // the typed component is ready for plan review, not settled.
        for id in ["M", "N3", "N5", "N6", "Q2", "N1"] {
            head.write("statements", planned(id, "P"));
        }
        let head_corpus = Corpus::load(&head.0).unwrap();
        let report = gate(&head_corpus, &base_corpus, "ROOT", "BASE");
        assert_eq!(report["passed"], true, "{}", format_gate(&report));
        assert_eq!(ids(&report, "offending"), Vec::<String>::new());
        assert_eq!(ids(&report, "ready_for_plan_review"), ["N1"]);
        assert!(format_gate(&report).contains("ready for plan review"));

        // The ordinary report lists every plan with its target, bridge and
        // blocker.
        let diagnostic = super::report(&head_corpus, "ROOT", 0);
        assert_eq!(
            ids(&diagnostic, "plans"),
            ["M", "N1", "N3", "N4", "N5", "N6", "Q1", "Q2"]
        );
        let plans = diagnostic["plans"].as_array().unwrap();
        assert_eq!(plans[1]["status"], "ready_for_plan_review");
        assert!(
            plans
                .iter()
                .skip(2)
                .all(|plan| plan["status"] == "outstanding")
        );
        assert_eq!(plans[0]["target"]["id"], "P");
        let text = format(&diagnostic);
        for line in [
            "outstanding connection plans (outside the root's typed component):",
            "  M [M] -> P [P]",
            "    missing bridge: b",
            "    blocker: x",
            "connection plans ready for plan review",
        ] {
            assert!(text.contains(line), "{line}\n{text}");
        }

        // Against itself nothing is new, moved or planned: the gate passes.
        let report = gate(&base_corpus, &base_corpus, "ROOT", "BASE");
        assert_eq!(report["new_statements"], 0);
        assert_eq!(ids(&report, "judged"), ["Q1", "Q2"]);
        assert_eq!(report["passed"], true);
    }
}
