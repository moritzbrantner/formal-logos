//! Bottleneck premises (owner direction, 2026-11-26).
//!
//! `docs/systematic-corpus-loop.md`, "When several arguments stop at the same
//! premise", makes the negation of such a premise the next research question.
//! [`report`] lists them from a computed reaching-root frontier report
//! (`frontier::current_frontier`): for each open premise, the distinct
//! arguments that consume it, the root routes (`routes.routes`) and stage
//! routes (the verified derivations of a stage conclusion) that need it, its
//! transitive dependent statements, its stages, its frontier support class,
//! its recorded rivals and objections, and the models that authored attempts
//! on it (`workers::authors`).
//!
//! A route's open premises are the leaves of the frontier's expanded route.
//! A stated or supported premise stays a leaf even when it is proved from
//! open premises (`proved_unestablished`), so most open premises sit below
//! such leaves. A route **needs** a premise when it is a leaf or when every
//! verified derivation (`support_options`) of a proved leaf needs it; it
//! **uses it in some proof** when some chain of verified derivations does.
//! Ranking and `--min-routes` use the routes that need the premise, so that
//! its negation would defeat each of them as recorded.
//!
//! The premises are the frontier's open items; a premise proved from open
//! premises is closed there, so its own open premises are listed instead. It
//! reuses the frontier's closure, routes and classification and computes
//! none of its own; it writes nothing and establishes nothing. The counts
//! diagnose shared dependency, not philosophical merit.

use crate::frontier;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The `truth bottlenecks` filters.
#[derive(Debug, Clone)]
pub struct Filter {
    /// Keep premises reaching at least one of these stages (none: any).
    pub stages: BTreeSet<u64>,
    /// Keep premises consumed by at least this many distinct arguments.
    pub min_arguments: usize,
    /// Keep premises on at least this many root routes.
    pub min_routes: usize,
    /// Keep premises whose recorded attempt authors are exactly this model.
    pub authored_only_by: Option<String>,
    /// Show at most this many premises (after ranking).
    pub limit: Option<usize>,
}

impl Default for Filter {
    fn default() -> Self {
        Self {
            stages: BTreeSet::new(),
            min_arguments: 2,
            min_routes: 0,
            authored_only_by: None,
            limit: None,
        }
    }
}

fn ids(value: &Value) -> BTreeSet<&str> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect()
}

/// The premises a route's proof uses. A route's open premises stop at proved
/// premises that rest on open ones (`proved_unestablished`); this follows
/// their verified derivations (`support_options`) down to the open premises.
struct Uses<'a> {
    /// Each verified, non-transcription derivation of a premise: its premises.
    derivations: BTreeMap<&'a str, Vec<BTreeSet<&'a str>>>,
    /// The open premises: a route may assume them directly, so their own
    /// derivations are alternatives, never requirements.
    open: BTreeSet<&'a str>,
    required: BTreeMap<&'a str, BTreeSet<&'a str>>,
}

impl<'a> Uses<'a> {
    /// `start` with the premises of every verified derivation of a member,
    /// transitively: what some way of proving `start` uses.
    fn any(&self, start: &BTreeSet<&'a str>) -> BTreeSet<&'a str> {
        let mut reached = start.clone();
        let mut pending: Vec<&str> = reached.iter().copied().collect();
        while let Some(statement) = pending.pop() {
            for bundle in self.derivations.get(statement).into_iter().flatten() {
                for &premise in bundle {
                    if reached.insert(premise) {
                        pending.push(premise);
                    }
                }
            }
        }
        reached
    }

    /// What every way of proving `start` uses: each member and, for a proved
    /// premise that is not open, what all of its verified derivations use.
    fn all(&mut self, start: &BTreeSet<&'a str>) -> BTreeSet<&'a str> {
        let mut used = BTreeSet::new();
        for &statement in start {
            used.extend(self.required(statement, &mut BTreeSet::new()));
        }
        used
    }

    fn required(
        &mut self,
        statement: &'a str,
        visiting: &mut BTreeSet<&'a str>,
    ) -> BTreeSet<&'a str> {
        if let Some(found) = self.required.get(statement) {
            return found.clone();
        }
        let mut used = BTreeSet::from([statement]);
        let bundles = self.derivations.get(statement).cloned().unwrap_or_default();
        if self.open.contains(statement) || bundles.is_empty() || !visiting.insert(statement) {
            return used;
        }
        let mut common: Option<BTreeSet<&str>> = None;
        for bundle in bundles {
            let mut through = BTreeSet::new();
            for premise in bundle {
                through.extend(self.required(premise, visiting));
            }
            common = Some(match common {
                None => through,
                Some(common) => common.intersection(&through).copied().collect(),
            });
        }
        visiting.remove(statement);
        used.extend(common.unwrap_or_default());
        self.required.insert(statement, used.clone());
        used
    }
}

/// Routes by id, each with a set of premises.
type Routes<'a> = Vec<(&'a str, BTreeSet<&'a str>)>;

/// The ids of the `routes` whose premise set contains `id`.
fn containing<'a>(routes: &[(&'a str, BTreeSet<&str>)], id: &str) -> Vec<&'a str> {
    routes
        .iter()
        .filter(|(_, premises)| premises.contains(id))
        .map(|(route, _)| *route)
        .collect()
}

/// The bottleneck view of a reaching-root `frontier` report. `label` names a
/// statement for the JSON; `authors` maps a statement to the models that
/// authored attempts on it. Premises are ranked by root routes, then the
/// stage routes of the selected stages (every stage when none is selected),
/// then consuming arguments, then transitive dependent statements (all
/// descending), then id. Stage routes break ties because the root routes all
/// rest on the same stage conclusions, so most premises lie on every one.
pub fn report(
    frontier: &Value,
    label: &dyn Fn(&str) -> Option<String>,
    authors: &BTreeMap<String, BTreeSet<String>>,
    filter: &Filter,
) -> Value {
    let mut uses = Uses {
        derivations: BTreeMap::new(),
        open: BTreeSet::new(),
        required: BTreeMap::new(),
    };
    for option in frontier["support_options"]["items"]
        .as_array()
        .into_iter()
        .flatten()
    {
        if let Some(id) = option["statement_id"].as_str() {
            uses.derivations.insert(
                id,
                option["verified_alternative_bundles"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|bundle| ids(&bundle["premise_statement_ids"]))
                    .collect(),
            );
        }
    }
    let items: Vec<&Value> = frontier["items"].as_array().into_iter().flatten().collect();
    uses.open = items
        .iter()
        .filter_map(|item| item["statement_id"].as_str())
        .collect();
    // A route's premises (`open_premise_statement_ids`), and every verified
    // derivation of a stage conclusion as one route of that stage: the root
    // routes all rest on the stage conclusions.
    let mut route_starts: Vec<(Option<u64>, &str, BTreeSet<&str>)> = frontier["routes"]["routes"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|route| {
            (
                None,
                route["argument_id"].as_str().unwrap_or_default(),
                ids(&route["open_premise_statement_ids"]),
            )
        })
        .collect();
    for stage in frontier["stages"].as_array().into_iter().flatten() {
        let (Some(number), Some(conclusion)) =
            (stage["stage"].as_u64(), stage["statement_id"].as_str())
        else {
            continue;
        };
        for bundle in uses
            .derivations
            .get(conclusion)
            .cloned()
            .unwrap_or_default()
        {
            route_starts.push((Some(number), conclusion, bundle));
        }
    }
    // Per stage (`None`: the root): the routes with the premises every proof
    // needs, and with the premises some proof uses.
    let mut grouped: BTreeMap<Option<u64>, (Routes, Routes)> = BTreeMap::new();
    for (stage, id, start) in route_starts {
        let (every, some) = grouped.entry(stage).or_default();
        every.push((id, uses.all(&start)));
        some.push((id, uses.any(&start)));
    }
    let (root_routes, root_routes_any) = grouped.remove(&None).unwrap_or_default();
    let stage_routes: Vec<(u64, Routes, Routes)> = grouped
        .into_iter()
        .filter_map(|(stage, (every, some))| Some((stage?, every, some)))
        .collect();
    let no_authors = BTreeSet::new();
    let mut rows: Vec<Value> = Vec::new();
    for item in items {
        let id = item["statement_id"].as_str().unwrap_or_default();
        let stages: Vec<u64> = frontier["statement_stages"][id]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_u64)
            .collect();
        if !filter.stages.is_empty() && !stages.iter().any(|s| filter.stages.contains(s)) {
            continue;
        }
        let arguments = ids(&item["dependent_arguments"]);
        let on_routes = containing(&root_routes, id);
        if arguments.len() < filter.min_arguments || on_routes.len() < filter.min_routes {
            continue;
        }
        let authored = authors.get(id).unwrap_or(&no_authors);
        if let Some(model) = &filter.authored_only_by
            && !crate::workers::authored_only_by(authored, model)
        {
            continue;
        }
        let rivals = item["alternatives"].as_array().cloned().unwrap_or_default();
        let refuted = rivals
            .iter()
            .filter(|rival| rival["refuted"] == true)
            .count();
        let derivations = uses.derivations.get(id).map_or(0, Vec::len);
        let mut on_stage_routes = BTreeMap::new();
        let mut on_stage_routes_any = BTreeMap::new();
        let mut selected_stage_routes = 0;
        for (stage, every, some) in &stage_routes {
            let count = containing(every, id).len();
            if count > 0 {
                on_stage_routes.insert(stage.to_string(), count);
                if filter.stages.is_empty() || filter.stages.contains(stage) {
                    selected_stage_routes += count;
                }
            }
            let count = containing(some, id).len();
            if count > 0 {
                on_stage_routes_any.insert(stage.to_string(), count);
            }
        }
        rows.push(json!({
            "statement_id": id,
            "label": label(id),
            "stages": stages,
            "consuming_argument_ids": arguments,
            "consuming_arguments": arguments.len(),
            "route_argument_ids": on_routes,
            "routes": on_routes.len(),
            "routes_using_it_in_some_proof": containing(&root_routes_any, id).len(),
            "stage_routes": on_stage_routes,
            "stage_routes_using_it_in_some_proof": on_stage_routes_any,
            "selected_stage_routes": selected_stage_routes,
            "transitive_dependent_statements": ids(&item["transitive_dependent_statements"]).len(),
            "support": frontier::item_depth(item),
            "stating_claims": ids(&item["stating_claims"]).len(),
            "supporting_claims": ids(&item["supporting_claims"]).len(),
            "conditional_derivation": derivations > 0,
            "verified_alternative_bundles": derivations,
            "rivals": rivals.len(),
            "refuted_rivals": refuted,
            "objections": ids(&item["objections"]).len(),
            "authored_by": authored,
        }));
    }
    let key = |row: &Value, field: &str| row[field].as_u64().unwrap_or(0);
    let rank = |row: &Value| {
        [
            "routes",
            "selected_stage_routes",
            "consuming_arguments",
            "transitive_dependent_statements",
        ]
        .map(|field| key(row, field))
    };
    rows.sort_by(|a, b| {
        rank(b)
            .cmp(&rank(a))
            .then(a["statement_id"].as_str().cmp(&b["statement_id"].as_str()))
    });
    let matching = rows.len();
    if let Some(limit) = filter.limit {
        rows.truncate(limit);
    }
    json!({
        "root": frontier["root"],
        "route_count": root_routes.len(),
        "stage_route_counts": stage_routes.iter()
            .map(|(stage, every, _)| (stage.to_string(), every.len()))
            .collect::<BTreeMap<_, _>>(),
        "filter": {
            "stages": filter.stages,
            "min_arguments": filter.min_arguments,
            "min_routes": filter.min_routes,
            "authored_only_by": filter.authored_only_by,
            "limit": filter.limit,
        },
        "matching": matching,
        "premises": rows,
    })
}

/// The text of [`report`]: a header and one line per premise, its uuid
/// last for `Aliases::humanize` to render as `label [uuid8]`.
pub fn format(report: &Value) -> String {
    let rows = report["premises"].as_array().cloned().unwrap_or_default();
    let filter = &report["filter"];
    let mut filters = vec![format!(
        "at least {} consuming arguments",
        filter["min_arguments"]
    )];
    if filter["min_routes"].as_u64().unwrap_or(0) > 0 {
        filters.push(format!("at least {} routes", filter["min_routes"]));
    }
    let stages: Vec<String> = filter["stages"]
        .as_array()
        .into_iter()
        .flatten()
        .map(Value::to_string)
        .collect();
    if !stages.is_empty() {
        filters.push(format!("stage {}", stages.join(" or ")));
    }
    if let Some(model) = filter["authored_only_by"].as_str() {
        filters.push(format!("authored only by {model}"));
    }
    let pairs = |value: &Value| {
        let pairs: Vec<String> = value
            .as_object()
            .into_iter()
            .flatten()
            .map(|(stage, count)| format!("{stage}:{count}"))
            .collect();
        if pairs.is_empty() {
            "-".to_owned()
        } else {
            pairs.join(",")
        }
    };
    let mut lines = vec![
        format!(
            "Bottleneck premises: open premises reaching {} where several arguments or routes stop \
             ({} of {} shown; {}; {} root routes; stage routes {}).",
            report["root"].as_str().unwrap_or_default(),
            rows.len(),
            report["matching"],
            filters.join(", "),
            report["route_count"],
            pairs(&report["stage_route_counts"]),
        ),
        "Counts diagnose shared dependency for choosing negation-side review, not philosophical merit."
            .to_owned(),
        "routes  stage routes  args  reach  stages  support            rivals  objections  authors  premise"
            .to_owned(),
    ];
    for row in &rows {
        let list = |field: &str| {
            let names: Vec<String> = row[field]
                .as_array()
                .into_iter()
                .flatten()
                .map(|value| {
                    value
                        .as_str()
                        .map_or_else(|| value.to_string(), str::to_owned)
                })
                .collect();
            if names.is_empty() {
                "-".to_owned()
            } else {
                names.join(",")
            }
        };
        let mut support = row["support"].as_str().unwrap_or_default().to_owned();
        if row["conditional_derivation"] == true {
            support.push_str("+derivation");
        }
        let count = |field: &str| row[field].as_u64().unwrap_or(0);
        let rivals = match count("refuted_rivals") {
            0 => count("rivals").to_string(),
            refuted => format!("{} ({refuted} ref.)", count("rivals")),
        };
        lines.push(format!(
            "{:>6}  {:<12}  {:>4}  {:>5}  {:<6}  {:<17}  {:>6}  {:>10}  {:<7}  {}",
            count("routes"),
            pairs(&row["stage_routes"]),
            count("consuming_arguments"),
            count("transitive_dependent_statements"),
            list("stages"),
            support,
            rivals,
            count("objections"),
            list("authored_by"),
            row["statement_id"].as_str().unwrap_or_default(),
        ));
    }
    if rows.is_empty() {
        lines.push("  none".into());
    }
    lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontier::Fixture;

    /// TOP has two root routes, A1 (P, Q) and A2 (P, R); A3 (Q, unverified)
    /// concludes R. X is a rival of P and an objection attacks Q; a claim
    /// states P.
    fn fixture() -> Value {
        let argument = |id: &str, premises: &[&str], conclusion: &str| {
            json!({"id": id, "premise_statement_ids": premises,
                   "conclusion_statement_id": conclusion, "inference_ids": [], "meaning": id})
        };
        let statements: Vec<Value> = ["TOP", "P", "Q", "R", "X"]
            .iter()
            .map(|id| json!({"id": id, "paraphrase": id}))
            .collect();
        json!({
            "statements": statements,
            "arguments": [
                argument("A1", &["P", "Q"], "TOP"),
                argument("A2", &["P", "R"], "TOP"),
                argument("A3", &["Q"], "R"),
            ],
            "results": [{"id": "R1", "argument_id": "A1"}, {"id": "R2", "argument_id": "A2"}],
            "relations": [
                {"id": "REL-ALT", "subject_kind": "statement", "subject_id": "X",
                 "predicate": "alternative_to", "object_kind": "statement", "object_id": "P"},
                {"id": "REL-ATT", "subject_kind": "claim", "subject_id": "CL-O",
                 "predicate": "attacks", "object_kind": "statement", "object_id": "Q"},
            ],
            "claims": [{"id": "CL-P", "statement_id": "P", "source_id": "SRC", "locator": "1",
                        "interpretation": "States P."}],
        })
    }

    fn frontier() -> Value {
        let mut report = Fixture::parse(&fixture())
            .unwrap()
            .report("TOP", true, false);
        // The fixture has no stage conclusions; give Q stage 2 and P stages 1, 2.
        report["statement_stages"] = json!({"P": [1, 2], "Q": [2]});
        report
    }

    fn statements_of(report: &Value) -> Vec<&str> {
        report["premises"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["statement_id"].as_str().unwrap())
            .collect()
    }

    #[test]
    fn ranks_by_routes_then_arguments_and_reports_classes() {
        let frontier = frontier();
        let authors = BTreeMap::from([(
            "P".to_owned(),
            BTreeSet::from(["sol".to_owned(), "astra".to_owned()]),
        )]);
        let label = |id: &str| Some(format!("label {id}"));
        let all = report(
            &frontier,
            &label,
            &authors,
            &Filter {
                min_arguments: 1,
                ..Filter::default()
            },
        );
        assert_eq!(statements_of(&all), ["P", "Q", "R"], "{all:#}");
        let p = &all["premises"][0];
        assert_eq!(p["routes"], 2);
        assert_eq!(p["route_argument_ids"], json!(["A1", "A2"]));
        assert_eq!(p["consuming_arguments"], 2);
        assert_eq!(p["support"], "stated");
        assert_eq!(p["rivals"], 1);
        assert_eq!(p["stages"], json!([1, 2]));
        assert_eq!(p["authored_by"], json!(["astra", "sol"]));
        assert_eq!(p["label"], "label P");
        let q = &all["premises"][1];
        assert_eq!(
            (q["routes"].clone(), q["consuming_arguments"].clone()),
            (json!(1), json!(2))
        );
        assert_eq!(q["consuming_argument_ids"], json!(["A1", "A3"]));
        assert_eq!(q["support"], "bare");
        assert_eq!(q["objections"], 1);
        assert_eq!(all["route_count"], 2);

        // The default --min-arguments 2 drops R; --min-routes 2 keeps only P.
        let default = report(&frontier, &label, &authors, &Filter::default());
        assert_eq!(statements_of(&default), ["P", "Q"]);
        let routes = Filter {
            min_routes: 2,
            ..Filter::default()
        };
        assert_eq!(
            statements_of(&report(&frontier, &label, &authors, &routes)),
            ["P"]
        );

        let text = format(&default);
        assert!(
            text.contains(
                "(2 of 2 shown; at least 2 consuming arguments; 2 root routes; stage routes -)"
            ),
            "{text}"
        );
        assert!(text.contains("not philosophical merit"), "{text}");
        assert!(text.lines().nth(3).unwrap().ends_with("  P"), "{text}");
        assert!(text.contains("astra,sol"), "{text}");
    }

    /// A verified derivation that leaves its conclusion open (here, R proved
    /// from Q and Q from R: an ungrounded cycle, #1476) is a conditional
    /// support option of an open premise. A premise proved from open
    /// premises is closed, so it is not listed; its open premises are.
    #[test]
    fn a_verified_derivation_marks_a_conditional_support_option() {
        let mut input = fixture();
        input["arguments"].as_array_mut().unwrap().push(json!({
            "id": "A4", "premise_statement_ids": ["R"], "conclusion_statement_id": "Q",
            "inference_ids": [], "meaning": "A4"}));
        let results = input["results"].as_array_mut().unwrap();
        results.push(json!({"id": "R3", "argument_id": "A3"}));
        results.push(json!({"id": "R4", "argument_id": "A4"}));
        let mut frontier = Fixture::parse(&input).unwrap().report("TOP", true, false);
        // Make R a stage conclusion: its one verified derivation is a stage route.
        frontier["stages"] = json!([{"stage": 2, "statement_id": "R"}]);
        let all = report(
            &frontier,
            &|_| None,
            &BTreeMap::new(),
            &Filter {
                min_arguments: 1,
                ..Filter::default()
            },
        );
        let row = |id: &str| {
            all["premises"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["statement_id"] == id)
                .unwrap_or_else(|| panic!("{id} stays an open premise: {all:#}"))
                .clone()
        };
        let r = row("R");
        assert_eq!(r["conditional_derivation"], true, "{all:#}");
        assert_eq!(r["verified_alternative_bundles"], 1);
        // Route A2 may assume the open R directly, so it needs Q only in the
        // proof that derives R from Q.
        let q = row("Q");
        assert_eq!(q["route_argument_ids"], json!(["A1"]), "{all:#}");
        assert_eq!(q["routes_using_it_in_some_proof"], 2);
        assert_eq!(q["stage_routes"], json!({"2": 1}));
        assert_eq!(all["stage_route_counts"], json!({"2": 1}));
        let text = format(&all);
        assert!(text.contains("bare+derivation"), "{text}");
        assert!(text.contains("stage routes 2:1)"), "{text}");
    }

    /// A route stops at M, proved but resting on open premises (a stated
    /// premise stays a route leaf until established). M has two verified
    /// derivations, from P and S and from S and U: every proof of the route
    /// uses S, only some use U.
    #[test]
    fn a_route_needs_what_every_derivation_of_a_proved_premise_uses() {
        let argument = |id: &str, premises: &[&str], conclusion: &str| {
            json!({"id": id, "premise_statement_ids": premises,
                   "conclusion_statement_id": conclusion, "inference_ids": [], "meaning": id})
        };
        let statements: Vec<Value> = ["TOP", "M", "P", "S", "U"]
            .iter()
            .map(|id| json!({"id": id, "paraphrase": id}))
            .collect();
        let input = json!({
            "statements": statements,
            "arguments": [
                argument("A1", &["P", "M"], "TOP"),
                argument("B1", &["P", "S"], "M"),
                argument("B2", &["S", "U"], "M"),
            ],
            "results": [{"id": "R1", "argument_id": "A1"}, {"id": "RB1", "argument_id": "B1"},
                        {"id": "RB2", "argument_id": "B2"}],
            "claims": [{"id": "CL-M", "statement_id": "M", "source_id": "SRC", "locator": "1",
                        "interpretation": "States M."}],
        });
        let frontier = Fixture::parse(&input).unwrap().report("TOP", true, false);
        let all = report(
            &frontier,
            &|_| None,
            &BTreeMap::new(),
            &Filter {
                min_arguments: 1,
                ..Filter::default()
            },
        );
        assert_eq!(statements_of(&all), ["P", "S", "U"], "{all:#}");
        let routes: Vec<(u64, u64)> = all["premises"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["routes"].as_u64().unwrap(),
                    row["routes_using_it_in_some_proof"].as_u64().unwrap(),
                )
            })
            .collect();
        assert_eq!(routes, [(1, 1), (1, 1), (0, 1)]);
    }

    #[test]
    fn filters_by_stage_author_and_limit() {
        let frontier = frontier();
        let label = |_: &str| None;
        let authors = BTreeMap::from([
            (
                "P".to_owned(),
                BTreeSet::from(["sol".to_owned(), "astra".to_owned()]),
            ),
            ("Q".to_owned(), BTreeSet::from(["sol".to_owned()])),
        ]);
        let stage1 = Filter {
            stages: BTreeSet::from([1]),
            ..Filter::default()
        };
        assert_eq!(
            statements_of(&report(&frontier, &label, &authors, &stage1)),
            ["P"]
        );
        let sole = Filter {
            authored_only_by: Some("sol".into()),
            ..Filter::default()
        };
        assert_eq!(
            statements_of(&report(&frontier, &label, &authors, &sole)),
            ["Q"]
        );
        let limited = report(
            &frontier,
            &label,
            &authors,
            &Filter {
                limit: Some(1),
                ..Filter::default()
            },
        );
        assert_eq!(statements_of(&limited), ["P"]);
        assert_eq!(limited["matching"], 2);
        let none = Filter {
            stages: BTreeSet::from([5]),
            ..Filter::default()
        };
        assert!(format(&report(&frontier, &label, &authors, &none)).ends_with("  none\n"));
    }
}
