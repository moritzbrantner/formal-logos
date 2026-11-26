//! Replay a selected argument with only its recorded inputs. A withheld input
//! can be recovered by another rule. Never seed or expand the target as a fact
//! while finding its producers: a target-to-premise cycle cannot support it.
use super::{
    format_result_witness, investigation_example, previous_investigations, result_witness,
};
use crate::{
    Corpus, Record,
    thickness::{list, text},
};
use serde::Serialize;
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

struct Rule<'a> {
    id: &'a str,
    conclusion: &'a str,
    inputs: Vec<&'a str>,
}

#[derive(Serialize)]
struct Scenario<'a> {
    withheld: BTreeSet<&'a str>,
    recovered_inputs: Vec<&'a str>,
    missing_selected_inputs: Vec<&'a str>,
    selected_applicable: bool,
    reachable: bool,
    supporting_arguments: Vec<&'a str>,
    derivation: Vec<&'a str>,
}

fn replay<'a>(
    rules: &[Rule<'a>],
    selected: &str,
    target: &str,
    inputs: &BTreeSet<&'a str>,
    withheld: BTreeSet<&'a str>,
) -> Scenario<'a> {
    let mut reached: BTreeSet<_> = inputs
        .difference(&withheld)
        .copied()
        .filter(|&s| s != target)
        .collect();
    let mut parent = BTreeMap::new();
    let mut discovery = Vec::new();
    loop {
        let mut next = BTreeMap::new();
        for rule in rules {
            if rule.conclusion != target
                && !reached.contains(rule.conclusion)
                && rule.inputs.iter().all(|s| reached.contains(s))
            {
                next.entry(rule.conclusion).or_insert(rule);
            }
        }
        if next.is_empty() {
            break;
        }
        for (s, rule) in next {
            reached.insert(s);
            parent.insert(s, rule);
            discovery.push(rule);
        }
    }
    let producers: Vec<_> = rules
        .iter()
        .filter(|r| r.conclusion == target && r.inputs.iter().all(|s| reached.contains(s)))
        .collect();
    let supporting_arguments: Vec<_> = producers.iter().map(|r| r.id).collect();
    let selected_applicable = supporting_arguments.contains(&selected);
    let mut derivation = Vec::new();
    if let Some(producer) = producers
        .iter()
        .find(|r| r.id == selected)
        .or(producers.first())
    {
        let mut needed = BTreeSet::new();
        let mut todo = producer.inputs.clone();
        while let Some(id) = todo.pop() {
            if needed.insert(id)
                && let Some(rule) = parent.get(id)
            {
                todo.extend(&rule.inputs);
            }
        }
        derivation.extend(
            discovery
                .iter()
                .filter(|r| needed.contains(r.conclusion))
                .map(|r| r.id),
        );
        derivation.push(producer.id);
    }
    Scenario {
        recovered_inputs: withheld.intersection(&reached).copied().collect(),
        missing_selected_inputs: inputs.difference(&reached).copied().collect(),
        reachable: !producers.is_empty(),
        withheld,
        selected_applicable,
        supporting_arguments,
        derivation,
    }
}

pub fn report(
    root: &Path,
    corpus: &Corpus,
    argument: &Record,
    selected_result: Option<&str>,
    without: &[String],
    compare: bool,
    limit: usize,
) -> Result<(Value, String), String> {
    let id = text(&argument.fields, "id");
    let label = text(&argument.fields, "label");
    let target = text(&argument.fields, "conclusion_statement_id");
    let meaning = text(&argument.fields, "meaning");
    let mut inputs = Vec::new();
    let mut selected = BTreeSet::new();
    for (role, key) in [
        ("premise", "premise_statement_ids"),
        ("commitment", "commitment_statement_ids"),
    ] {
        for sid in list(&argument.fields, key) {
            let s = corpus
                .get("statements", sid)
                .ok_or_else(|| format!("missing statement {sid}"))?;
            inputs.push(json!({"id":sid, "role":role, "label":s.fields["label"],"paraphrase":s.fields["paraphrase"]}));
            selected.insert(sid);
        }
    }
    let withheld: BTreeSet<_> = without.iter().map(String::as_str).collect();
    if let Some(s) = withheld.difference(&selected).next() {
        return Err(format!("{s} is not an input of argument {id}"));
    }

    let mut backed = BTreeSet::new();
    let mut results = Vec::new();
    for (result_id, record) in corpus.records_by_id("results") {
        let aid = text(&record.fields, "argument_id");
        if matches!(
            text(&record.fields, "status"),
            "solution-present" | "verified"
        ) {
            backed.insert(aid);
        }
        if aid == id && selected_result.is_none_or(|selected| selected == result_id) {
            results.push(result_witness(root, record));
        }
    }
    let rules: Vec<_> = corpus
        .records_by_id("arguments")
        .filter(|(id, _)| backed.contains(id))
        .map(|(id, a)| {
            let mut inputs = list(&a.fields, "premise_statement_ids");
            inputs.extend(list(&a.fields, "commitment_statement_ids"));
            Rule {
                id,
                inputs,
                conclusion: text(&a.fields, "conclusion_statement_id"),
            }
        })
        .collect();
    let scenario = replay(&rules, id, target, &selected, withheld);
    let mut output = vec![format!("{label}\n{meaning}")];
    output.extend(results.iter().take(limit).map(format_result_witness));
    let scope = "Conditional reachability uses the selected argument’s retained premises and commitments plus registered rules with solutions. The target cannot support its own inputs. Withholding an input leaves its negation open. Each graph step matches statement IDs; joint Lean instantiation and actual-world warrant require their own evidence.";
    output.push(scope.into());
    for input in &inputs {
        let sid = input["id"].as_str().unwrap_or_default();
        let role = input["role"].as_str().unwrap_or_default();
        let status = if sid == target {
            "excluded target"
        } else if scenario.recovered_inputs.contains(&sid) {
            "rederived"
        } else if scenario.withheld.contains(sid) {
            "withheld"
        } else {
            "supplied"
        };
        output.push(format!(
            "{role} ({status}) — {}\n  truth synthesis {sid}",
            input["label"].as_str().unwrap_or(sid)
        ));
    }
    output.push(format!(
        "Selected argument applicable: {}. Conclusion reachable in this comparison: {}.",
        scenario.selected_applicable, scenario.reachable
    ));
    if !scenario.derivation.is_empty() {
        output.push("One derivation, in dependency order".into());
        for arg in &scenario.derivation {
            let name = corpus
                .get("arguments", arg)
                .map(|a| text(&a.fields, "label"))
                .unwrap_or(arg);
            output.push(format!("  {name} — truth context {arg}"));
        }
    }
    let alternatives: Vec<_> = scenario
        .supporting_arguments
        .iter()
        .filter(|&&aid| aid != id)
        .collect();
    for &aid in alternatives.iter().take(limit) {
        if let Some(a) = corpus.get("arguments", aid) {
            output.push(format!(
                "Other applicable argument — {}\n  truth synthesis {aid}",
                text(&a.fields, "label")
            ));
        }
    }
    let reviewed_inputs = crate::lifecycle::current(corpus, &without.iter().cloned().collect());
    for record in reviewed_inputs.iter().take(limit) {
        let field = |key: &str| record[key].as_str().unwrap_or_default();
        output.push(format!(
            "Assessment covering a withheld input ({}) — {}\n{}\nRevision test — {}\n{}",
            field("review"),
            field("scope"),
            field("assessment"),
            field("next_test"),
            field("note")
        ));
    }
    let investigations = previous_investigations(corpus, &scenario.withheld, selected_result);
    if let Some(result_id) = selected_result {
        let mut cited: Vec<_> = investigations
            .iter()
            .filter(|entry| entry.evidence.contains(&result_id))
            .collect();
        cited.sort_by_key(|entry| entry.assessment_of(target).is_none());
        for entry in cited.into_iter().take(limit) {
            if let Some(assessment) = entry.assessment_of(target) {
                let field = |key: &str| assessment[key].as_str().unwrap_or_default();
                output.push(format!(
                    "Assessment of the conclusion ({}, {}) — {}\n{}\nRevision test — {}\n{}",
                    field("review"),
                    field("publication"),
                    field("scope"),
                    field("assessment"),
                    field("next_test"),
                    field("note")
                ));
            } else {
                output.push(format!("Investigation citing this result — {}\n{}\nUse --json for its full finding and evidence.", entry.label, entry.path));
            }
        }
    }
    if let Some(example) =
        investigation_example(&investigations, |sid| scenario.withheld.contains(sid))
    {
        output.push(example);
    }
    let mut json = serde_json::to_value(&scenario).map_err(|e| e.to_string())?;
    json["schema_version"] = json!(1);
    json["input_identity"] = json!(corpus.input_identity());
    json["mode"] = json!("argument");
    json["scope"] = json!(scope);
    json["argument"] = json!({"argument_id":id,"label":label,"meaning":meaning,"conclusion_statement_id":target,"path":argument.path});
    json["results"] = json!(results);
    if let Some(result_id) = selected_result {
        json["selected_result_id"] = json!(result_id);
    }
    json["inputs"] = json!(inputs);
    json["withheld_assessments"] = json!(reviewed_inputs);
    json["previous_investigations"] = json!(investigations);
    if compare {
        let mut comparisons = Vec::new();
        for &sid in &selected {
            let s = replay(&rules, id, target, &selected, BTreeSet::from([sid]));
            output.push(format!(
                "Withhold {sid} — selected argument applicable: {}, conclusion reachable: {}.",
                s.selected_applicable, s.reachable
            ));
            comparisons.push(s);
        }
        json["comparisons"] = json!(comparisons);
    }
    Ok((json, output.join("\n\n")))
}
