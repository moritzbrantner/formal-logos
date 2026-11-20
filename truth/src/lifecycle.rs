//! Explicit, scoped research currentness and revision reassessment. These are
//! recorded judgments and work dispositions, never proof or acceptance gates.
use crate::{
    Corpus,
    evidence_graph::{Edge, EvidenceGraph},
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::Path,
};

fn text<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key].as_str().unwrap_or_default()
}

/// Canonical attempt extension; legacy attempts remain valid and unmarked.
pub fn validate(
    attempt: &serde_json::Map<String, Value>,
    statements: &HashSet<&str>,
) -> Result<(), String> {
    let Some(current) = attempt.get("current_assessment") else {
        if attempt.get("revisions").is_some() {
            return Err("revisions require a scoped current_assessment".into());
        }
        return Ok(());
    };
    for field in [
        "date",
        "scope",
        "assessment",
        "next_test",
        "note",
        "reviewed_revision",
        "review",
        "publication",
        "supersedes",
        "evidence",
    ] {
        if text(current, field).trim().is_empty() {
            return Err(format!("current_assessment.{field} must be nonempty"));
        }
    }
    if !["unreviewed", "accepted_qualified", "changes_requested"].contains(&text(current, "review"))
    {
        return Err("invalid current_assessment.review".into());
    }
    if !["unpublished", "published", "merged"].contains(&text(current, "publication")) {
        return Err("invalid current_assessment.publication".into());
    }
    let revision = text(current, "reviewed_revision");
    if revision.len() != 40 || !revision.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("reviewed_revision must be a full commit hash".into());
    }
    let ids = current["statement_ids"]
        .as_array()
        .ok_or("current assessment needs statement_ids")?;
    if ids
        .iter()
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>()
        .len()
        != ids.len()
    {
        return Err("current statement_ids must be unique strings".into());
    }
    if ids.is_empty()
        || ids.iter().any(|id| {
            !id.as_str().is_some_and(|id| {
                statements.contains(id)
                    && attempt["statement_ids"]
                        .as_array()
                        .is_some_and(|all| all.contains(&json!(id)))
            })
        })
    {
        return Err("current assessment scope must name statements in its attempt".into());
    }
    if let Some(changes) = attempt.get("revisions") {
        let mut revisions = BTreeSet::new();
        for change in changes.as_array().ok_or("revisions must be an array")? {
            if !["meaning", "premise_warrant", "judgment"].contains(&text(change, "kind"))
                || text(change, "reason").trim().is_empty()
                || text(change, "revision").trim().is_empty()
                || text(change, "previous").trim().is_empty()
            {
                return Err(
                    "revision needs kind (meaning/premise_warrant/judgment), revision, previous evidence locator and reason"
                        .into(),
                );
            }
            if !revisions.insert(text(change, "revision")) {
                return Err("revision identifiers must be unique within an attempt".into());
            }
            let targets = change["statement_ids"]
                .as_array()
                .ok_or("revision needs statement_ids")?;
            if targets
                .iter()
                .filter_map(Value::as_str)
                .collect::<BTreeSet<_>>()
                .len()
                != targets.len()
                || targets.is_empty()
                || targets.iter().any(|id| !ids.contains(id))
            {
                return Err("revision targets must be within current assessment scope".into());
            }
            if let Some(dispositions) = change.get("reassessments") {
                for d in dispositions
                    .as_array()
                    .ok_or("reassessments must be an array")?
                {
                    validate_reassessment(d)?;
                }
            }
        }
    }
    Ok(())
}

pub fn current(corpus: &Corpus, ids: &BTreeSet<String>) -> Vec<Value> {
    let mut out = Vec::new();
    for record in corpus.entries("attempts") {
        let Some(current) = record.fields.get("current_assessment") else {
            continue;
        };
        if current["statement_ids"].as_array().is_some_and(|scope| {
            scope
                .iter()
                .any(|id| id.as_str().is_some_and(|id| ids.contains(id)))
        }) {
            let mut entry = current.clone();
            entry["attempt_id"] = record.fields["id"].clone();
            entry["path"] = json!(record.path);
            out.push(entry);
        }
    }
    out.sort_by(|a, b| {
        text(b, "date")
            .cmp(text(a, "date"))
            .then_with(|| text(a, "attempt_id").cmp(text(b, "attempt_id")))
    });
    out
}

// Targets and review ledgers register work, rather than consuming its warrant.
// Keep substantive prose (including the selected assessment) in other attempts.
fn attempt_use(field: &str) -> bool {
    let mut parts = field.trim_start_matches('/').split('/');
    match parts.next() {
        Some("statement_ids" | "revisions") => false,
        Some("current_assessment") => {
            matches!(parts.next(), Some("assessment" | "scope" | "next_test"))
        }
        _ => true,
    }
}

/// Consumer tiers, strongest first. `premise_use` and `import` are the formal
/// channel and propagate transitively; `reference` and `prose` are one-hop
/// mentions of the changed target or of a formal-channel consumer.
pub const TIERS: [&str; 4] = ["premise_use", "import", "reference", "prose"];
/// Tiers that a single `group` disposition may cover. A registered premise
/// consumer or argument-conclusion propagation always needs its own disposition.
const GROUPABLE: [&str; 3] = ["import", "reference", "prose"];
/// Acknowledged consumers beyond the scoped set (legacy per-consumer entries
/// for a transitive mention chain) remain listed under this label.
const TRANSITIVE: &str = "transitive_mention";

/// Registered premise, commitment, inference and result-of-argument fields.
/// These are the declared formal channel, not proof-term use evidence.
fn formal_field(kind: &str, field: &str) -> bool {
    let first = field.trim_start_matches('/').split('/').next();
    match kind {
        "arguments" => matches!(
            first,
            Some("premise_statement_ids" | "commitment_statement_ids" | "inference_ids")
        ),
        "inferences" => matches!(
            first,
            Some("input_statement_ids" | "assumption_statement_ids" | "discharged_statement_ids")
        ),
        "results" => field == "/argument_id",
        _ => false,
    }
}

/// How a consumer was reached; `via` is its reached predecessor.
#[derive(Clone)]
struct Reach {
    tier: &'static str,
    via: String,
    field: String,
    how: String,
    import_source: Option<String>,
}
impl Reach {
    fn new(tier: &'static str, via: &str, field: &str, how: &str) -> Self {
        Self {
            tier,
            via: via.into(),
            field: field.into(),
            how: how.into(),
            import_source: None,
        }
    }
}

/// Whether `key` explicitly mentions a node still carrying the change.
fn mentions_live(
    key: &str,
    forward: &BTreeMap<&str, Vec<&Edge>>,
    expanding: &BTreeSet<&String>,
    admissible: &dyn Fn(&Edge) -> bool,
) -> bool {
    forward
        .get(key)
        .into_iter()
        .flatten()
        .any(|e| expanding.contains(&e.to) && admissible(e))
}

fn group_of(d: &Value) -> Option<&str> {
    d.get("group").and_then(Value::as_str)
}

/// Validate a reassessment entry's addressing: exactly one of `consumer` or
/// `group` (`tier:<import|reference|prose>` or `path:<repository path>`).
fn validate_reassessment(d: &Value) -> Result<(), String> {
    let consumer = d.get("consumer").and_then(Value::as_str);
    let group = group_of(d);
    let addressed = match (consumer, group) {
        (Some(c), None) => !c.is_empty(),
        (None, Some(g)) => match g.split_once(':') {
            Some(("tier", tier)) => GROUPABLE.contains(&tier),
            Some(("path", path)) => !path.trim().is_empty(),
            _ => false,
        },
        _ => false,
    };
    if !addressed
        || text(d, "reason").trim().is_empty()
        || !["pending", "retained", "revised", "not_applicable"].contains(&text(d, "disposition"))
    {
        return Err(
            "reassessment needs one consumer or group (tier:import|reference|prose or path:<path>), explicit disposition and reason"
                .into(),
        );
    }
    Ok(())
}

/// Reverse explicit references expose potential uses, not semantic equivalence.
/// The formal channel (registered premise use, argument/result conclusion
/// propagation and Lean import discovery) is followed transitively. Structured
/// references and prose mentions are reported one hop from the changed target
/// or a formal-channel consumer; longer mention chains are counted, not listed.
/// No result's formal status is changed, even for unresolved uses.
pub fn impacts(root: &Path, corpus: &Corpus, ids: &BTreeSet<String>) -> Result<Vec<Value>, String> {
    let changes: Vec<_> = corpus
        .entries("attempts")
        .into_iter()
        .flat_map(|r| {
            r.fields
                .get("revisions")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .map(move |c| (r, c))
        })
        .collect();
    if changes.is_empty() {
        return Ok(Vec::new());
    }
    let graph = EvidenceGraph::build(root, corpus, None)?;
    let mut reverse: BTreeMap<&str, Vec<&Edge>> = BTreeMap::new();
    let mut forward: BTreeMap<&str, Vec<&Edge>> = BTreeMap::new();
    for edge in graph.edges() {
        // Producers of a reached conclusion are alternative support, not
        // consumers of the changed upstream premise.
        if !matches!(
            edge.provenance.field.as_str(),
            "/conclusion_statement_id" | "/output_statement_id"
        ) {
            reverse.entry(edge.to.as_str()).or_default().push(edge);
            forward.entry(edge.from.as_str()).or_default().push(edge);
        }
    }
    // Reuse context's source-level import parser. Imports expose possible
    // semantic consumers; only Lean proof-use inspection can establish use.
    let lean = crate::context::Lean::new(root);
    let results = corpus.entries("results");
    let producer_conclusions: BTreeMap<String, String> = results
        .iter()
        .filter_map(|r| {
            let argument = corpus.get("arguments", r.fields["argument_id"].as_str()?)?;
            Some((
                format!("results:{}", r.fields["id"].as_str()?),
                format!(
                    "statements:{}",
                    argument.fields["conclusion_statement_id"].as_str()?
                ),
            ))
        })
        .collect();
    let mut imports = Vec::new();
    for consumer in &results {
        let module = consumer
            .fields
            .get("solution_module")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if module.is_empty() {
            continue;
        }
        let closure = lean.closure(module);
        for source in &results {
            if source.fields["id"] != consumer.fields["id"]
                && source
                    .fields
                    .get("solution_module")
                    .and_then(Value::as_str)
                    .is_some_and(|m| closure.iter().any(|(imported, _)| imported == m))
            {
                imports.push((
                    format!(
                        "results:{}",
                        consumer.fields["id"].as_str().unwrap_or_default()
                    ),
                    format!(
                        "results:{}",
                        source.fields["id"].as_str().unwrap_or_default()
                    ),
                ));
            }
        }
    }
    let conclusion_of = |key: &str| -> Option<String> {
        let node = graph.nodes().get(key)?;
        let id = match node.kind.as_str() {
            "arguments" => node.content["conclusion_statement_id"].as_str()?,
            "results" => corpus
                .get("arguments", node.content["argument_id"].as_str()?)?
                .fields["conclusion_statement_id"]
                .as_str()?,
            _ => return None,
        };
        Some(format!("statements:{id}"))
    };

    // Formal channel: registered premise use and conclusion propagation first,
    // then import discovery onward, each to a fixed point. Nodes in `stop`
    // (consumers individually reassessed as unchanged) are reached, not expanded.
    let formal_closure = |seeds: &BTreeSet<String>,
                          admissible: &dyn Fn(&Edge) -> bool,
                          stop: &BTreeSet<String>|
     -> BTreeMap<String, Reach> {
        let mut seen = seeds.clone();
        let mut reached = BTreeMap::new();
        for (tier, with_imports) in [("premise_use", false), ("import", true)] {
            let mut frontier: Vec<String> = seen
                .iter()
                .filter(|k| !stop.contains(*k))
                .cloned()
                .collect();
            while !frontier.is_empty() {
                let mut next = Vec::new();
                for key in &frontier {
                    for edge in reverse.get(key.as_str()).into_iter().flatten() {
                        let kind = edge.from.split(':').next().unwrap_or_default();
                        if formal_field(kind, &edge.provenance.field) && admissible(edge) {
                            next.push((
                                edge.from.clone(),
                                Reach::new(tier, key, &edge.provenance.field, "registered"),
                            ));
                        }
                    }
                    if let Some(target) = conclusion_of(key) {
                        next.push((
                            target,
                            Reach::new(tier, key, "/conclusion_statement_id", "conclusion"),
                        ));
                    }
                }
                if with_imports {
                    let live = |k: &String| seen.contains(k) && !stop.contains(k);
                    for (consumer, source) in &imports {
                        // A producer is an import-discovery source even when only
                        // its conclusion is reached; it is not thereby affected.
                        let parent = if live(source) {
                            Some(source)
                        } else {
                            producer_conclusions.get(source).filter(|c| live(c))
                        };
                        if let Some(parent) = parent {
                            let mut reach =
                                Reach::new(tier, parent, "/solution_module", "lean_import");
                            reach.import_source = Some(source.clone());
                            next.push((consumer.clone(), reach));
                        }
                    }
                }
                frontier.clear();
                for (key, reach) in next {
                    if seen.insert(key.clone()) {
                        if !stop.contains(&key) {
                            frontier.push(key.clone());
                        }
                        reached.insert(key, reach);
                    }
                }
            }
        }
        reached
    };

    let mut out = Vec::new();
    for (attempt, change) in changes {
        let seeds: BTreeSet<String> = change["statement_ids"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(|id| format!("statements:{id}"))
            .collect();
        let declaring_attempt = format!(
            "attempts:{}",
            attempt.fields["id"].as_str().unwrap_or_default()
        );
        // Lifecycle metadata is an assessment record, not its own consumer.
        let admissible = |edge: &Edge| {
            edge.from != declaring_attempt
                && (!edge.from.starts_with("attempts:") || attempt_use(&edge.provenance.field))
        };
        let mut reached = formal_closure(&seeds, &admissible, &BTreeSet::new());
        let mut seen: BTreeSet<String> = seeds.iter().chain(reached.keys()).cloned().collect();
        // One-hop mentions of the target or of a formal-channel consumer. A
        // structured id reference outranks a prose mention of the same record.
        let mut mentions: BTreeMap<String, Reach> = BTreeMap::new();
        for key in &seen {
            for edge in reverse.get(key.as_str()).into_iter().flatten() {
                if seen.contains(&edge.from) || !admissible(edge) {
                    continue;
                }
                let tier = if edge.provenance.how == "exact" && !edge.from.starts_with("notes:") {
                    "reference"
                } else {
                    "prose"
                };
                if !mentions
                    .get(&edge.from)
                    .is_some_and(|old| old.tier == "reference" || tier == "prose")
                {
                    mentions.insert(
                        edge.from.clone(),
                        Reach::new(tier, key, &edge.provenance.field, &edge.provenance.how),
                    );
                }
            }
        }
        for (key, reach) in mentions {
            seen.insert(key.clone());
            reached.insert(key, reach);
        }
        // Longer reference chains (and the conclusions/imports they would
        // reach) are not uses of the change; count them so nothing silently vanishes.
        let mut transitive: BTreeMap<String, String> = BTreeMap::new();
        let mut frontier: Vec<String> = seen.iter().cloned().collect();
        while !frontier.is_empty() {
            let mut next = Vec::new();
            for key in &frontier {
                for edge in reverse.get(key.as_str()).into_iter().flatten() {
                    if admissible(edge) {
                        next.push((edge.from.clone(), key.clone()));
                    }
                }
                if let Some(target) = conclusion_of(key) {
                    next.push((target, key.clone()));
                }
            }
            for (consumer, source) in &imports {
                if transitive.contains_key(source)
                    || producer_conclusions
                        .get(source)
                        .is_some_and(|c| transitive.contains_key(c))
                {
                    next.push((consumer.clone(), source.clone()));
                }
            }
            frontier.clear();
            for (key, via) in next {
                if !seen.contains(&key) && !transitive.contains_key(&key) {
                    transitive.insert(key.clone(), via);
                    frontier.push(key);
                }
            }
        }
        if !seeds
            .iter()
            .chain(seen.iter())
            .any(|key| ids.iter().any(|id| key == &format!("statements:{id}")))
        {
            continue;
        }
        let path_of = |key: &str| graph.nodes().get(key).map(|n| n.path.clone());
        let mut individual = BTreeMap::new();
        let mut groups = BTreeMap::new();
        for d in change["reassessments"].as_array().into_iter().flatten() {
            if let Some(group) = group_of(d) {
                if groups.insert(group.to_owned(), d).is_some() {
                    return Err(format!(
                        "revision reassessment names duplicate or unaffected group: {group}"
                    ));
                }
                continue;
            }
            let consumer = text(d, "consumer");
            if !(reached.contains_key(consumer) || transitive.contains_key(consumer))
                || individual.insert(consumer.to_owned(), d).is_some()
            {
                return Err(format!(
                    "revision reassessment names duplicate or unaffected consumer: {consumer}"
                ));
            }
            if let Some(via) = transitive.get(consumer) {
                reached.insert(
                    consumer.to_owned(),
                    Reach::new(TRANSITIVE, via, "", "mention_chain"),
                );
            }
        }
        // A formal consumer individually reassessed as unchanged screens what
        // lies downstream only through it; screened consumers stay listed.
        let stop: BTreeSet<String> = individual
            .iter()
            .filter(|(k, d)| {
                reached
                    .get(*k)
                    .is_some_and(|r| matches!(r.tier, "premise_use" | "import"))
                    && ["retained", "not_applicable"].contains(&text(d, "disposition"))
            })
            .map(|(k, _)| k.clone())
            .collect();
        let live: BTreeSet<String> = if stop.is_empty() {
            reached.keys().cloned().collect()
        } else {
            let formal_live = formal_closure(&seeds, &admissible, &stop);
            // A consumer still live past the screen is reported by its live
            // route: when that route now runs through import discovery, it is
            // an import-tier consumer rather than a registered premise use.
            for (key, reach) in &formal_live {
                reached.insert(key.clone(), reach.clone());
            }
            let expanding: BTreeSet<&String> = seeds
                .iter()
                .chain(formal_live.keys())
                .filter(|k| !stop.contains(*k))
                .collect();
            let mut live: BTreeSet<String> = formal_live.keys().cloned().collect();
            for (key, reach) in &reached {
                if matches!(reach.tier, "reference" | "prose")
                    && mentions_live(key, &forward, &expanding, &admissible)
                {
                    live.insert(key.clone());
                }
            }
            live
        };
        // A group must cover at least one consumer of its tier or path.
        for group in groups.keys() {
            let covers = reached.iter().any(|(key, reach)| {
                GROUPABLE.contains(&reach.tier)
                    && match group.split_once(':') {
                        Some(("tier", t)) => t == reach.tier,
                        Some(("path", p)) => path_of(key).as_deref() == Some(p),
                        _ => false,
                    }
            });
            if !covers {
                return Err(format!(
                    "revision reassessment names duplicate or unaffected group: {group}"
                ));
            }
        }
        let screened_by = |key: &str| -> Option<String> {
            let mut cursor = reached.get(key)?.via.clone();
            loop {
                if stop.contains(&cursor) {
                    return Some(cursor);
                }
                cursor = reached.get(&cursor)?.via.clone();
            }
        };
        // An inference shares the disposition its containing arguments agree on;
        // a result shares the disposition of the argument it verifies.
        let mut containing: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for key in reached.keys() {
            let Some(node) = graph.nodes().get(key) else {
                continue;
            };
            match node.kind.as_str() {
                "arguments" => {
                    for id in node.content["inference_ids"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_str)
                    {
                        containing
                            .entry(format!("inferences:{id}"))
                            .or_default()
                            .push(key.clone());
                    }
                }
                "results" => {
                    if let Some(id) = node.content["argument_id"].as_str() {
                        let argument = format!("arguments:{id}");
                        if reached.contains_key(&argument) {
                            containing.entry(key.clone()).or_default().push(argument);
                        }
                    }
                }
                _ => {}
            }
        }
        let mut tiers = serde_json::Map::new();
        for tier in TIERS.iter().chain([&TRANSITIVE]) {
            tiers.insert(
                (*tier).into(),
                json!({"consumers":0,"pending":0,"screened":0}),
            );
        }
        let mut consumers = Vec::new();
        for (key, reach) in &reached {
            let path = path_of(key);
            let inherited = containing.get(key).and_then(|args| {
                let ds: Vec<_> = args.iter().map(|a| individual.get(a)).collect();
                (ds.iter().all(Option::is_some)
                    && ds.windows(2).all(|w| {
                        text(w[0].unwrap(), "disposition") == text(w[1].unwrap(), "disposition")
                    }))
                .then(|| (ds[0].unwrap(), args[0].clone()))
            });
            let (disposition, by): (Option<&Value>, Value) = if let Some(d) = individual.get(key) {
                (Some(*d), json!("consumer"))
            } else if let Some((d, argument)) = inherited {
                (Some(d), json!(argument))
            } else if !GROUPABLE.contains(&reach.tier) {
                (None, Value::Null)
            } else if let Some((g, d)) = path
                .as_deref()
                .and_then(|p| groups.get_key_value(&format!("path:{p}")))
            {
                (Some(*d), json!(g))
            } else if let Some((g, d)) = groups.get_key_value(&format!("tier:{}", reach.tier)) {
                (Some(*d), json!(g))
            } else {
                (None, Value::Null)
            };
            let screen = (disposition.is_none() && !live.contains(key))
                .then(|| screened_by(key))
                .flatten();
            let disposition_text = match (disposition, &screen) {
                (Some(d), _) => text(d, "disposition"),
                (None, Some(_)) => "screened",
                (None, None) => "pending",
            };
            let count = &mut tiers[reach.tier];
            count["consumers"] = json!(count["consumers"].as_u64().unwrap_or(0) + 1);
            if matches!(disposition_text, "pending" | "screened") {
                count[disposition_text] = json!(count[disposition_text].as_u64().unwrap_or(0) + 1);
            }
            consumers.push(json!({"consumer":key,"tier":reach.tier,"via":reach.via,"field":reach.field,"how":reach.how,"path":path,
                "import_source":reach.import_source,"disposition":disposition_text,"disposition_by":by,"screened_by":screen,
                "reason":disposition.map(|d| &d["reason"])}));
        }
        let mut beyond = BTreeMap::<String, usize>::new();
        for key in transitive.keys().filter(|k| !reached.contains_key(*k)) {
            *beyond
                .entry(key.split(':').next().unwrap_or_default().to_owned())
                .or_default() += 1;
        }
        let beyond_total: usize = beyond.values().sum();
        out.push(json!({"attempt_id":attempt.fields["id"],"change":change,"tiers":tiers,"consumers":consumers,
            "transitive_mentions":{"count":beyond_total,"by_kind":beyond,"boundary":"records reached only through a chain of two or more reference/prose mentions (and conclusions or imports beyond them); counted, not listed, and not consumers of the change"},
            "boundary":"premise_use: registered argument/inference premise fields and conclusion propagation; import: source-level Lean import discovery (potential, not proof-term use); reference/prose: one-hop explicit mentions (potential uses); screened: downstream only through a consumer reassessed as unchanged. Pending reassessment does not invalidate any formal theorem or accept a judgment"}));
    }
    Ok(out)
}

pub fn lines(current: &[Value], impacts: &[Value]) -> Vec<String> {
    let mut lines = Vec::new();
    for c in current {
        lines.push(format!(
            "Current recorded assessment [{}; {}]: {}",
            text(c, "review"),
            text(c, "publication"),
            text(c, "assessment")
        ));
        lines.push(format!(
            "  scope: {}; reviewed revision: {}; evidence: {}",
            text(c, "scope"),
            text(c, "reviewed_revision"),
            text(c, "note")
        ));
        lines.push(format!(
            "  review/publication evidence: {}",
            text(c, "evidence")
        ));
        lines.push(format!("  supersedes: {}", text(c, "supersedes")));
        lines.push(format!("  next test: {}", text(c, "next_test")));
    }
    for impact in impacts {
        lines.push(format!(
            "Declared {} revision {} — downstream reassessment (formal validity unchanged):",
            text(&impact["change"], "kind"),
            text(&impact["change"], "revision")
        ));
        lines.push(format!(
            "  change: {}; prior evidence: {}",
            text(&impact["change"], "reason"),
            text(&impact["change"], "previous")
        ));
        let tiers = &impact["tiers"];
        lines.push(format!(
            "  tiers (consumers/pending/screened): {}; transitive mentions not listed: {}",
            TIERS
                .iter()
                .chain([&TRANSITIVE])
                .filter(|t| tiers[**t]["consumers"].as_u64().unwrap_or(0) > 0)
                .map(|t| format!(
                    "{t} {}/{}/{}",
                    tiers[*t]["consumers"].as_u64().unwrap_or(0),
                    tiers[*t]["pending"].as_u64().unwrap_or(0),
                    tiers[*t]["screened"].as_u64().unwrap_or(0)
                ))
                .collect::<Vec<_>>()
                .join(", "),
            impact["transitive_mentions"]["count"].as_u64().unwrap_or(0)
        ));
        // List registered premise use and individually reassessed consumers;
        // the groupable tiers are summarized here and listed in full in --json.
        for consumer in impact["consumers"].as_array().into_iter().flatten() {
            let tier = text(consumer, "tier");
            if tier != "premise_use" && consumer["disposition_by"] != "consumer" {
                continue;
            }
            lines.push(format!(
                "  [{tier}] {}: {}{}",
                text(consumer, "consumer"),
                text(consumer, "disposition"),
                consumer["reason"]
                    .as_str()
                    .map(|s| format!(" — {s}"))
                    .unwrap_or_default()
            ));
        }
    }
    lines
}
