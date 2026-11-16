//! `truth novelty`: an advisory check whether a proposed claim,
//! connection or investigation is already recorded.
//!
//! It searches exact record IDs, the Lean declarations of corpus statements
//! (structural: which formalized statements use the claim's identifiers),
//! note paragraphs (with each note's own notation), record prose and, when
//! supplied, an offline issue/PR snapshot. Each hit says which query items
//! it contains and what kind of evidence it is. The classification is a
//! retrieval summary, never a verdict: `already-recorded` means some unit
//! contains every query item (lexical containment is not equivalence), and
//! `no-match-found` never means "novel".

use super::{Inputs, retrieval};
use crate::notes;
use retrieval::{Issues, Query};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub const CLASSIFICATIONS: &str = "already-recorded: some unit contains every query item (at least two), \
     or the text names a record exactly; partially-recorded: some unit contains at least half of the items \
     and half of the words and identifiers (operators alone are weak); no-match-found: neither";

pub const NOVELTY_BOUNDARY: &str = "advisory retrieval: a hit shows where the query's words, identifiers and \
     operators occur, not that the texts are equivalent; a note or issue is not a certified entailment; \
     no-match-found is not evidence of novelty";

/// One hit: its evidence kind, reference, coverage and why it matched.
struct Hit {
    covered: usize,
    /// At least half of all items and of the content items (not operators).
    substantial: bool,
    rank: u8,
    key: String,
    value: Value,
}

fn evidence_kind(kind: &str) -> &'static str {
    match kind {
        "note" => "research note paragraph (uncertified text)",
        "statements" => "statement record (its formal status is the frontier's)",
        "results" => "verification result (a checked consequence of its premises only)",
        "issue" | "pull_request" => "issue/PR text (workflow history, not warrant)",
        "attempts" => "attempt record (research history)",
        _ => "corpus record",
    }
}

/// The novelty report for `text`. `exclude` is the statement a
/// `--statement` query was built from, which never counts as prior work.
pub fn novelty(
    inputs: &Inputs,
    db: &rusqlite::Connection,
    index_state: Value,
    text: &str,
    exclude: Option<&str>,
    limit: usize,
) -> Result<Value, String> {
    let query = Query::parse(text);
    let total = query.items.len();
    let none = BTreeMap::new();
    let mut hits: Vec<Hit> = Vec::new();
    let lookup = notes::Lookup::of_corpus(inputs.corpus);
    // 1. Exact record IDs, legacy IDs, labels or paths in the text.
    let probe = notes::Section {
        anchor: String::new(),
        heading: String::new(),
        level: 0,
        line: 1,
        body: text.to_owned(),
    };
    let mut named: BTreeSet<String> = BTreeSet::new();
    for link in lookup.links(&probe).0 {
        if Some(link.id.as_str()) == exclude || !named.insert(format!("{}:{}", link.kind, link.id))
        {
            continue;
        }
        hits.push(Hit {
            substantial: true,
            covered: usize::MAX,
            rank: 0,
            key: format!("0:{}:{}", link.kind, link.id),
            value: json!({
                "kind": link.kind,
                "evidence": evidence_kind(&link.kind),
                "ref": inputs.reference(&link.kind, &link.id),
                "via": format!("exact {} {}", link.how.as_str(), link.mention),
            }),
        });
    }
    // 2. Statements whose Lean declaration uses the query's identifiers.
    let identifiers = query.identifiers();
    let mut structural: Vec<(usize, String)> = Vec::new();
    let mut lean = retrieval::LeanSource::new(inputs.root);
    let mut declarations_read = 0usize;
    if !identifiers.is_empty() {
        for record in inputs.corpus.entries("statements") {
            let fields = &record.fields;
            let id = fields.get("id").and_then(Value::as_str).unwrap_or_default();
            let Some(declaration) = fields.get("lean_declaration").and_then(Value::as_str) else {
                continue;
            };
            if Some(id) == exclude {
                continue;
            }
            let Some((file, line, block)) = lean.block(declaration) else {
                continue;
            };
            declarations_read += 1;
            let block_words: BTreeSet<&str> = retrieval::words(&block).into_iter().collect();
            let used: Vec<&str> = identifiers
                .iter()
                .copied()
                .filter(|name| block_words.contains(name))
                .collect();
            if used.is_empty() {
                continue;
            }
            let matched = query.matched(&block, &none);
            let covered = retrieval::coverage(&matched).0;
            structural.push((covered, id.to_owned()));
            hits.push(Hit {
                substantial: query.substantial(&matched),
                covered,
                rank: 1,
                key: format!("1:{id}"),
                value: json!({
                    "kind": "statements",
                    "evidence": evidence_kind("statements"),
                    "ref": inputs.reference("statements", id),
                    "via": format!("structural: Lean declaration {declaration} uses {}", used.join(", ")),
                    "location": format!("{file} line {line}"),
                    "coverage": [covered, total],
                    "matched": retrieval::matched_items(&query, &matched),
                    "excerpt": retrieval::excerpt(&block, 300),
                    "formal_state": inputs.formal_state(id)["state"],
                }),
            });
        }
    }
    structural.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    structural.truncate(8);
    let structural_ids: BTreeSet<&str> = structural.iter().map(|(_, id)| id.as_str()).collect();
    // Arguments and results built on the structurally matched statements.
    for argument in inputs.corpus.entries("arguments") {
        let fields = &argument.fields;
        let premises: Vec<&str> = fields
            .get("premise_statement_ids")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        let used: Vec<&str> = premises
            .iter()
            .copied()
            .filter(|p| structural_ids.contains(p))
            .collect();
        if used.len() < 2 {
            continue;
        }
        let id = fields.get("id").and_then(Value::as_str).unwrap_or_default();
        hits.push(Hit {
            substantial: false,
            covered: used.len().min(total),
            rank: 2,
            key: format!("2:{id}"),
            value: json!({
                "kind": "arguments",
                "evidence": "argument record using several structurally matched statements together as premises",
                "ref": inputs.reference("arguments", id),
                "via": format!("premises {}", used.iter().map(|p| inputs.aliases.show(p)).collect::<Vec<_>>().join(", ")),
                "conclusion": inputs.reference("statements", fields.get("conclusion_statement_id").and_then(Value::as_str).unwrap_or_default()),
            }),
        });
    }
    // 3. Note paragraphs: the index's best notes and the notes naming the
    // structurally matched statements, each read with its own notation.
    let mention_ids: BTreeSet<&str> = structural_ids.iter().copied().take(4).collect();
    let mut naming_notes: Vec<String> = Vec::new();
    for entry in notes::mentioning(inputs.root, &lookup, &mention_ids)? {
        if let Some(path) = entry["path"].as_str()
            && !naming_notes.iter().any(|known| known == path)
        {
            naming_notes.push(path.to_owned());
        }
    }
    let (paths, record_candidates) = super::candidate_notes(db, &query, &naming_notes)?;
    for score in super::score_notes(inputs.root, &query, &paths) {
        let mut paragraphs: Vec<&super::ParagraphHit> = score.paragraphs.iter().collect();
        // Substantial paragraphs first, so operator-only matches cannot
        // crowd out the qualifying one before classification.
        paragraphs.sort_by(|a, b| {
            (query.substantial(&b.matched), b.covered())
                .cmp(&(query.substantial(&a.matched), a.covered()))
                .then(a.line.cmp(&b.line))
        });
        for hit in paragraphs.into_iter().take(2) {
            let mut value = super::paragraph_json(&query, hit);
            value["kind"] = json!("note");
            value["evidence"] = json!(evidence_kind("note"));
            value["path"] = json!(hit.path);
            value["note_date"] = json!(retrieval::latest_date(&score.raw));
            if naming_notes.contains(&hit.path) {
                value["via"] = json!("note names a structurally matched statement");
            }
            hits.push(Hit {
                substantial: query.substantial(&hit.matched),
                covered: hit.covered(),
                rank: 3,
                key: format!("3:{}:{:08}", hit.path, hit.line),
                value,
            });
        }
    }
    // 4. Records by prose.
    for record in super::record_hits(inputs, &query, &record_candidates, limit * 3) {
        let kind = record["kind"].as_str().unwrap_or_default().to_owned();
        let id = record["id"].as_str().unwrap_or_default().to_owned();
        if Some(id.as_str()) == exclude {
            continue;
        }
        let covered = record["coverage"][0].as_u64().unwrap_or_default() as usize;
        // A statement found structurally keeps one hit: the better-covered
        // evidence, with the other named in `via`.
        let mut via = "record prose".to_owned();
        if let Some(position) = hits.iter().position(|hit| hit.key == format!("1:{id}")) {
            if hits[position].covered >= covered {
                continue;
            }
            let structural = hits.remove(position);
            via = format!(
                "record prose (also {})",
                structural.value["via"].as_str().unwrap_or("structural")
            );
        }
        let mut value = record;
        value["evidence"] = json!(evidence_kind(&kind));
        value["via"] = json!(via);
        hits.push(Hit {
            substantial: value["substantial"] == true,
            covered,
            rank: 4,
            key: format!("4:{kind}:{id}"),
            value,
        });
    }
    // 5. Issues and PRs.
    if let Some(snapshot) = inputs.issues.snapshot() {
        for issue in &snapshot.issues {
            let number = issue
                .get("number")
                .and_then(Value::as_u64)
                .unwrap_or_default();
            let mut best: (usize, String, String, Vec<bool>) =
                (0, String::new(), String::new(), Vec::new());
            let mut names = BTreeSet::new();
            for (place, unit) in retrieval::issue_units(issue) {
                let matched = query.matched(&unit, &none);
                let covered = retrieval::coverage(&matched).0;
                // A substantial unit beats an operator-only one of equal or
                // higher coverage, so paragraph order cannot hide it.
                if (query.substantial(&matched), covered) > (query.substantial(&best.3), best.0) {
                    best = (
                        covered,
                        place.clone(),
                        retrieval::excerpt(&unit, 240),
                        matched,
                    );
                }
                let section = notes::Section {
                    anchor: String::new(),
                    heading: String::new(),
                    level: 0,
                    line: 1,
                    body: unit,
                };
                for link in lookup.links(&section).0 {
                    if structural_ids.contains(link.id.as_str()) {
                        names.insert(link.id.clone());
                    }
                }
            }
            if !query.substantial(&best.3) && names.is_empty() {
                continue;
            }
            let mut value = retrieval::issue_header(issue);
            retrieval::attach_successors(&mut value, issue, snapshot);
            let kind = value["kind"].as_str().unwrap_or_default().to_owned();
            value["evidence"] = json!(evidence_kind(&kind));
            value["coverage"] = json!([best.0, total]);
            value["matched"] = json!(retrieval::matched_items(&query, &best.3));
            value["where"] = json!(best.1);
            value["excerpt"] = json!(best.2);
            value["names_structural_statements"] = json!(
                names
                    .iter()
                    .map(|id| inputs.reference("statements", id))
                    .collect::<Vec<_>>()
            );
            // Within equal coverage: more named structural statements, then newer.
            let key = format!(
                "5:{:04}:{:08}",
                9999usize.saturating_sub(names.len()),
                u64::MAX / 2 - number
            );
            hits.push(Hit {
                substantial: query.substantial(&best.3),
                covered: best.0,
                rank: 5,
                key,
                value,
            });
        }
    }
    // Rank: exact IDs, then coverage, then evidence kind, then key.
    hits.sort_by(|a, b| {
        b.covered
            .cmp(&a.covered)
            .then(a.rank.cmp(&b.rank))
            .then_with(|| a.key.cmp(&b.key))
    });
    let best = hits
        .iter()
        .filter(|hit| hit.rank != 0 && hit.rank != 2)
        .map(|hit| hit.covered)
        .max()
        .unwrap_or(0);
    let exact = hits.iter().any(|hit| hit.rank == 0);
    let full = total >= 2 && best == total;
    let classification = if exact || full {
        "already-recorded"
    } else if hits
        .iter()
        .any(|hit| hit.substantial && hit.rank != 0 && hit.rank != 2)
    {
        "partially-recorded"
    } else {
        "no-match-found"
    };
    let full_kinds: BTreeSet<String> = hits
        .iter()
        .filter(|hit| hit.rank != 0 && total >= 2 && hit.covered == total)
        .map(|hit| hit.value["kind"].as_str().unwrap_or_default().to_owned())
        .collect();
    let mut reading = match classification {
        "already-recorded" if exact => {
            "the text names existing records exactly; read them before treating the proposal as new".to_owned()
        }
        "already-recorded" => format!(
            "some unit ({}) contains every query item; read it before claiming novelty — containment is not equivalence",
            full_kinds.iter().cloned().collect::<Vec<_>>().join(", ")
        ),
        "partially-recorded" => {
            "units contain at least half of the query items: related prior work exists; compare it before claiming novelty".to_owned()
        }
        _ => "no unit contains half of the query items (and half of its words and identifiers); \
              this is not evidence of novelty"
            .to_owned(),
    };
    if !full_kinds.is_empty()
        && full_kinds
            .iter()
            .all(|kind| kind == "note" || kind == "issue" || kind == "pull_request")
    {
        reading.push_str("; recorded only in notes or issues, so not a certified entailment");
    }
    let mut searched = vec![
        "exact record IDs, legacy IDs, labels and paths in the text".to_owned(),
        format!(
            "Lean declarations of {declarations_read} corpus statements (when the text has identifiers)"
        ),
        format!(
            "{} notes, every paragraph, each with its own notation",
            paths.len()
        ),
        format!(
            "{} record candidates from the index",
            record_candidates.len()
        ),
    ];
    let mut caveats = Vec::new();
    match inputs.issues {
        Issues::Snapshot(snapshot) => {
            searched.push(format!("{} snapshot issues/PRs", snapshot.items));
            if !snapshot.includes_closed {
                caveats.push("the issue snapshot has no closed or merged items: finished work is not searched".to_owned());
            }
            if snapshot.older_than_checkout == Some(true) {
                caveats.push("the issue snapshot predates the checkout's HEAD commit: later issue activity is unknown".to_owned());
            }
        }
        Issues::Missing { .. } => caveats.push(retrieval::MISSING_ISSUES.to_owned()),
    }
    if query.items.is_empty() {
        caveats.push("the text has no searchable words, identifiers or operators".to_owned());
    }
    // Bounded: at most `limit * 3` hits per evidence group (notes, records,
    // issues), in rank order; `hit_counts` gives the totals.
    let group = |hit: &Hit| match hit.value["kind"].as_str().unwrap_or_default() {
        "note" => "notes",
        "issue" | "pull_request" => "issues",
        _ => "records",
    };
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut shown = Vec::new();
    for hit in hits {
        let count = counts.entry(group(&hit)).or_default();
        *count += 1;
        if *count <= limit * 3 {
            shown.push(hit.value);
        }
    }
    Ok(json!({
        "boundary": NOVELTY_BOUNDARY,
        "query": query,
        "excluded": exclude,
        "identity": inputs.identity(),
        "index": index_state,
        "classification": classification,
        "classifications": CLASSIFICATIONS,
        "reading": reading,
        "best_coverage": [if exact { total } else { best }, total],
        "searched": searched,
        "caveats": caveats,
        "issues": inputs.issues,
        "hit_counts": counts,
        "hits": shown,
    }))
}

fn hit_lines(lines: &mut Vec<String>, hit: &Value, aliases: &crate::identity::Aliases) {
    let clip = |value: &Value, max: usize| retrieval::excerpt(&crate::pyfmt::text(value), max);
    let kind = hit["kind"].as_str().unwrap_or_default();
    let coverage = if hit["coverage"].is_array() {
        format!(" [{}/{}]", hit["coverage"][0], hit["coverage"][1])
    } else {
        String::new()
    };
    let place = match kind {
        "note" => format!(
            "{} line {}",
            hit["section"].as_str().unwrap_or_default(),
            hit["line"]
        ),
        "issue" | "pull_request" => format!(
            "#{} [{}] {} ({})",
            hit["number"],
            hit["state"].as_str().unwrap_or("unknown"),
            clip(&hit["title"], 70),
            hit["where"].as_str().unwrap_or_default()
        ),
        _ => {
            let reference = if hit["ref"].is_object() {
                &hit["ref"]
            } else {
                hit
            };
            let id = reference["id"].as_str().unwrap_or_default();
            match reference["label"].as_str() {
                Some(label) if id.len() >= 8 => {
                    format!("{} [{}]", retrieval::excerpt(label, 80), &id[..8])
                }
                _ => aliases.show(id),
            }
        }
    };
    let mut line = format!(
        "  {kind}{coverage} {place}{}",
        retrieval::successor_text(hit)
    );
    if let Some(via) = hit["via"].as_str() {
        line.push_str(&format!(" — {via}"));
    }
    if let Some(state) = hit["formal_state"].as_str() {
        line.push_str(&format!("; frontier: {state}"));
    }
    let notation: Vec<String> = hit["notation"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|n| clip(n, 60))
        .collect();
    if !notation.is_empty() {
        line.push_str(&format!("; note notation {}", notation.join(", ")));
    }
    let named = hit["names_structural_statements"]
        .as_array()
        .map_or(0, Vec::len);
    if named > 0 {
        line.push_str(&format!(
            "; names {named} structurally matched statement(s)"
        ));
    }
    lines.push(line);
    if let Some(excerpt) = hit["excerpt"].as_str() {
        lines.push(format!("      \"{}\"", retrieval::excerpt(excerpt, 220)));
    }
}

/// The text view: classification, reading, then each hit with its evidence
/// kind and location.
pub fn format_novelty(report: &Value, aliases: &crate::identity::Aliases, limit: usize) -> String {
    let mut lines = vec![
        format!(
            "Novelty check (advisory): {}",
            report["query"]["text"].as_str().unwrap_or_default()
        ),
        format!(
            "Classification: {} (best coverage {}/{})",
            report["classification"].as_str().unwrap_or_default(),
            report["best_coverage"][0],
            report["best_coverage"][1]
        ),
        format!(
            "Reading: {}",
            report["reading"].as_str().unwrap_or_default()
        ),
        format!(
            "Items: {}",
            report["query"]["items"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|item| format!(
                    "{} ({})",
                    item["text"].as_str().unwrap_or_default(),
                    item["kind"].as_str().unwrap_or_default()
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        format!(
            "Revision: {}; index {}",
            report["identity"]["revision"]["commit"]
                .as_str()
                .unwrap_or("unknown"),
            if report["index"]["rebuilt"] == true {
                "rebuilt for this query"
            } else {
                "reused (current)"
            }
        ),
    ];
    let hits = report["hits"].as_array().cloned().unwrap_or_default();
    type Member = fn(&str) -> bool;
    let groups: [(&str, Member); 3] = [
        ("Notes", |kind| kind == "note"),
        ("Corpus records (exact, structural, prose)", |kind| {
            !matches!(kind, "note" | "issue" | "pull_request")
        }),
        ("Issues and PRs", |kind| {
            matches!(kind, "issue" | "pull_request")
        }),
    ];
    for (title, member) in groups {
        let group: Vec<&Value> = hits
            .iter()
            .filter(|hit| member(hit["kind"].as_str().unwrap_or_default()))
            .collect();
        lines.push(format!("{title} ({}):", group.len()));
        for hit in group.iter().take(limit) {
            hit_lines(&mut lines, hit, aliases);
        }
        if group.len() > limit {
            lines.push(format!(
                "  … {} more (--json lists them)",
                group.len() - limit
            ));
        }
    }
    lines.push(format!(
        "Searched: {}",
        report["searched"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join("; ")
    ));
    for caveat in report["caveats"].as_array().into_iter().flatten() {
        lines.push(format!("Caveat: {}", caveat.as_str().unwrap_or_default()));
    }
    lines.push(format!("Boundary: {NOVELTY_BOUNDARY}."));
    lines.join("\n")
}
