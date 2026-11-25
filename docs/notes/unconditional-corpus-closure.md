# Audit of unconditional corpus consequences

Continues #497, #1007, #1565, #1926, #1987 and #1989. Initial baseline:
`8a8dcdbed7c2c1501b74c9ae8aa408ec5fa25c26`. Draft research checkpoint; no floor marking, relation, proof,
definition, or closure rule is changed here. No new status registry.

## Question and evidence boundary

Which exact existing propositions follow without disputed substantive
premises, and which additional routes can consume them? The primary inventory
is a computed projection of the canonical records, not a list of accepted
claims. In particular, distinguish:

- a theorem of logic or a definition-relative theorem (including universal
  conditional theorems, not the satisfaction of their antecedents);
- a strictly self-refuting denial in a matched performance, content and domain;
- direct actual or first-person warrant (not a universally quantified theorem);
- a necessary precondition of inquiry, with the actual inquiry identified;
- existing met legacy floor bases, with the basis retained;
- deductive consequences of each explicit basis;
- common ground relative to specified rival commitments;
- epistemic self-undermining without falsity;
- conditional certificates, consistency models and hidden application bridges.

Use the canonical [systematic loop](../systematic-corpus-loop.md), the
[frontier](../../truth/README.md#frontier-and-frontier-diff), the registered
support graph and the existing [orphan audit](orphan-graft-map.md#6-retorsion-graft-audit-1926-1963-1007-1008).
The Rust frontier exposes both `established_statements` and
`closed_statements`: the latter can include consequences of open leaves and
transcriptions; it is not the requested unconditional set. The existing
frontier handles bottom cycles; a separate diagnostic of SCCs may explain
their dependencies but must never seed their members as facts. A positive
implication hyperedge fires only when every required premise has a witness.

## First discriminating results (recorded evidence, not a new review)

- #1987's seven non-counting attacks do not turn warrant failure into falsity.
  In particular, epistemic nihilism's result `ec80b13d` does not establish F6
  `f56b2ee7`. The same-relation incompatibility `146b502b` assumes F6.
- Knowledge retorsion `72288c48` excludes knowing universal ignorance under
  factivity, not the truth of universal ignorance. Do not supply knowledge by
  stipulating it.
- The Cogito route `cc1a4204` needs actual assertion `b45ca9db` and cognitive
  realization `1edfc1d1`. Represented occurrence `46c875b1` needs the
  representation bridge; #1979/#1980 retain actual-world presence and
  concreteness. This is a high-value God-existence connection, not a
  premise-free proof of concrete population.
- The V2 verificationism package `92ad4e06` has the recorded premise-free
  refutation argument `c93862da` (result `2d032de7`); restricted auxiliaries and other verificationist
  theses are different claims. The V1 package instead relies on weak negation
  closure floor `3f979107`. See the [verificationism showcase](../showcase-verificationism.md).
- A theorem certifying a model's satisfiability proves that formal fact, not the
  actual truth of the model's commitments. A universal conditional can itself
  be logically established while its consequent at an actual witness is open.

## Reproduction and completion boundary

In a prepared checkout, run the existing worker preflight and build, then
`target/release/truth --json frontier` (no `--reaching-root` or `--routes`),
`target/release/truth --json orphans` for the default root and for
`--frontier-root STMT-GOD-EXISTS`. Use the complete statement inventory rather
than limiting the audit to either backward slice. Preserve input identity,
result and argument IDs, precise Lean types and every required premise.
Use the existing support-graph export for focused backward slices and
`truth context`, `truth dossier`, `truth semantics` for application checks.
Compare `established_statements` with met floor bases and a zero-input
least-fixed-point computation, explicitly separating consistency witnesses,
transcriptions and actual application conditions.

The current connector environment can read and write individual GitHub files
but cannot check out the corpus (network DNS fails) or run its Rust/Lean
verification. This initial note is not the exhaustive computation, and no
numerical corpus result or new verified argument is asserted. Complete the
full reproducible projection and semantic review before relying on this
audit for new premise establishment. Independent semantic challenge pending.

## Pinned record audit (checkpoint 2)

At the initial base, the Git tree lists 5,074 entries under
`corpus/statements`, 2,572 under `corpus/arguments`, and 2,570 under
`corpus/results` (non-truncated tree responses). These are file counts,
not a proof or establishment count. Reading thousands of individual blobs
through the connector is not a substitute for a complete checked-out graph.
The eight floor-marked records below were found by indexed search for
`self_evident` in the statements directory and all eight blobs were read at
the pinned base. The authoritative `floor[].met` and `criterion_reasons`
must still be exported from the current CLI; a marking alone is not evidence
that every criterion is met. No current floor is changed.

| Exact statement ID | Recorded basis | Warrant / justification | Scope, live objection and use |
| --- | --- | --- | --- |
| `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` | Excluded middle (legacy) | Recorded justifications `2164c64b`, `32c1a3f1`, `d80a3dd8`, `3be6adf4`, `d36bd424`, `e2d8d9a4`; constructive double negation of each instance is not the universal assertion of EM. | Intuitionistic withholding is not a denial; explicit classical basis remains. Modal/classical route rules use this distinction. |
| `c425f0c5-6c3f-5115-ba04-3e61bd049e3b` | F1, case-predicate noncontradiction (retorsion; legacy approval) | `a7ecf1fe-a234-5de6-bb72-bf76309c5ea3`: zero-axiom result about the encoded predicate and its Lean negation. | Denial `e5097538` is refuted in that interpretation. A dialetheist's alternative negation is not thereby represented; relevant to prima via and rival refutations. |
| `bef22027-4f6d-5722-9597-e4dec273ebdd` | F3, something changes (observation; legacy approval) | `c5e6b7dd`, `7b28a77b`; actual change in some characteristic or relation, not just motion. | Static episode control; McTaggart's later account is compatible with F3. Observing motion and interpreting it as general change are distinct. |
| `fbc516c1-a6cb-5495-9d31-6e2bb45e8e67` | F4, something is moved (observation; legacy approval) | `c5e6b7dd`; actual reduction from potency to act in a respect, stronger than mere occurrence. | Eleatic and McTaggart-style rivals recorded unrefuted. Actual-world and motion-in-a-respect calibration must be defended; prima via input. |
| `f56b2ee7-c69e-5e3b-85b0-e671d907ba58` | F6, an epistemic reason to believe (common ground; legacy approval) | `ec80b13d-0c87-5f71-bc70-16b42dc4c0e6`; nihilism is self-undermining; actual thin reason witness is the separate F6 claim. | Reasonless truth model survives; not preference-independent authority or full moral normativity. See #1980 for a warranted-acceptance or belief-specific route. |
| `3f979107-8ac1-557c-8e10-b3cfa3a7ba78` | Weak meaningfulness closure under negation (common ground; legacy approval) | `7ac3d198`; only from meaningful negation to meaningful double negation. Strong closure implies it. | The exact contrary remains recorded. Consumed by V1 law exclusion; not all propositions are meaningful. |
| `afa7a288-a1d5-5958-a1d0-3f68d4d186ad` | Strong meaningfulness closure under negation (common ground; legacy approval) | `53f64561`; for any meaningful sentence its negation is meaningful. | Stronger than V1 needs; 1946 strengthened exclusion uses it. No unrestricted linguistic validity. |
| `e27489c3-7419-5123-8476-386633e62532` | Causal power and outgoing productive activity require concreteness (common ground; legacy approval) | `d9a2d64b`; recorded operari-based derivation has open premises. Concrete means esse in re at the selected world. | Four full-strength rivals and an exact negative; abstract relevance is not productive cause. Do not widen to formal/final/exemplary cause or infer necessary actuality. God-route concreteness remains sense-specific. |

### Executed selected implication closure

Read the following fourteen argument and result records directly at the
baseline, confirming argument/result correspondence and each result's
`solution-present` status. The table records the **conclusion statement**,
argument and result UUIDs separately. These are recorded results, not new
kernel/Comparator/NanoDa checks; the full canonical transcription heuristic,
actual proof axiom audit, sense/dossier checks and semantic review remain
pending. For this selected calculation, include each implication as
registered, not as a promotion to philosophical truth. The least fixed
point with no input gives eight conclusion IDs; with the eight recorded
floor markings hypothetically supplied as seeds, it gives ten new IDs
(the weak closure is already a seed), not eighteen unconditional truths.
This sample does not count any `refutes` or `alternative_to` relation as a
positive implication. No whole-corpus total is inferred. The fourteen selected edges contain no
nontrivial SCC or self-loop; that observation says nothing about cycles in
the omitted graph.

| Conclusion statement ID | Argument ID | Result ID | Recorded premises (complete) | Interpretation / limitation |
| --- | --- | --- | --- | --- |
| `f96aff82-50fd-525b-8f74-99036a71e2d3` | `8a79f1f4-26fd-56c1-aed5-af197738fed2` | `a7ecf1fe-a234-5de6-bb72-bf76309c5ea3` | none | No case contradiction in Lean; refutation relation to F1 rival remains scope-relative, not a denial of every dialetheism. |
| `53515f2a-068a-5f75-8f79-1c97dbd3f87b` | `c9cb4b0b-e6a5-527d-bafc-67e8fab3ce37` | `72288c48-d10f-5042-9961-84a1deb2ac18` | none | Factive knowledge cannot know universal ignorance; universal ignorance itself can be true. |
| `8efdfe70-cb76-575f-a13c-16a35cfb7c9e` | `83208e1e-e6bf-53e7-a0a6-eeb481d6f22f` | `b41427d3-a0c7-55aa-b1cb-f4f90a14277c` | none | Not every Lean Prop fails; actual object-language truth requires calibration. |
| `484ff137-4e6e-5572-88d4-39f080ace82a` | `301f8e5f-ef2f-59c2-9749-b76402b44242` | `a360c98c-dbb4-5412-b645-83b971e1a7f3` | none | Not every Lean Prop holds; actual truth-predicate/negation representation remains distinct. |
| `61f64a70-27c6-521b-babb-0d54b43e412a` | `4124c437-b63a-5aa8-bdb5-a8373e4c6893` | `fa3e85b3-531d-5504-b680-f3909dd50faf` | none | Truth nontriviality certificate; expressive/capture/disquotation hypotheses are inside its theorem type; no automatic absolute truth. |
| `4963e32f-b9e6-55ce-8c6c-811ff9db6513` | `f8e82f70-7645-5676-aebc-aef21b5cca89` | `ec80b13d-0c87-5f71-bc70-16b42dc4c0e6` | none | If nihilism holds, no one has reason to believe it. Its model survives; attacks, not falsity. |
| `b8e30c15-56d5-5d6e-94eb-611d58a7a415` | `c93862da-e2c1-5ddc-aeda-9050b14a84b2` | `2d032de7-5ab9-5c0d-af09-d60c4a73088d` | none | V2 exclusion package fails with its unrestricted auxiliaries; narrow refutation, not all verificationism. |
| `28319bae-efee-41ab-93d9-aaba9c63648e` | `17a2c392-3bc1-4b53-b9ba-9f5635f23490` | `e03147fa-7a1f-48d9-bac0-7aec0ee2b645` | none | Singleton identity sequent for supplied content; application to actual reasoning requires content and identity in scope. |
| `7a6a60f5-1cdd-52bc-9ea3-f213214c277a` | `32b3030e-fb60-56d2-a30a-af1b3f9c432e` | `8aa484b7-c76f-50a2-975f-0e4340e439f6` | `3f979107-8ac1-557c-8e10-b3cfa3a7ba78` | V1 law exclusion fails given weak negation closure; not zero-input. |
| `3f979107-8ac1-557c-8e10-b3cfa3a7ba78` | `2597b819-0089-5e8b-96fb-052944c27b14` | `6c7eaa48-8c27-5b01-80a1-669ad9567110` | `afa7a288-a1d5-5958-a1d0-3f68d4d186ad` | Strong to weak meaningfulness closure; directional implication only. |
| `8697bb2d-f29d-5945-88ea-bb62d6a3e4e2` | `857ce9c1-6b90-57c1-a2f4-73d2528b9080` | `d7295336-2058-5b9a-8b67-f8bac00b7dde` | `1722a80f-47a4-5605-8b66-b3534e457bcb` | Performed doubt cannot accurately deny thought if realization premise holds. Actual performance is not asserted. |
| `d9181e4c-e26a-4cd2-ae0b-add96f520fad` | `8e216377-1bf3-4262-b3ff-ef64f0e46136` | `146b502b-e5fd-40cf-8a39-9ed2d45e59bb` | `f56b2ee7-c69e-5e3b-85b0-e671d907ba58` | F6 excludes nihilism for the same reason relation; cannot independently establish F6. |
| `e81971f1-601c-57f5-be2d-c4b0624d0cad` | `f93f2dfd-5ec8-4378-a90a-0e8c4a79b30e` | `cc1a4204-1315-46a8-bf0a-ac436b06b790` | `b45ca9db-0bf2-40d3-819c-44dc4e2cef5c`, `1edfc1d1-34d4-4f3e-99e6-e07a6ba58ffc` | Thought occurrence from actual assertion and realization; no bearer or concreteness. |
| `43253cd8-62be-4528-85e4-54806bd3fac0` | `afc88915-f9c8-4371-8225-c52f5e6af2a6` | `46c875b1-286f-4bfb-a1c9-cd66acbfc7f6` | `e81971f1-601c-57f5-be2d-c4b0624d0cad`, `13b5b929-dfc0-4ce0-8b3b-f00430024030` | Some represented existent; same representation and selected-world existence required for actual population. #1979/#1980 add concreteness/presence conditions. |

In this slice all eight zero-input certificates arrive in round one. Adding
only the assertion and realization seeds supplies thought occurrence
`e81971f1`; supplying the representation bridge too gives represented
existence `43253cd8` in round two. Neither route supplies the intended
world's concrete individual. The three added seeds are hypothetical for
this computation, not new floor judgments. See the existing #1979/#1980
research before extending this route.

### Whole-corpus reproduction (read-only, pending full run)

Use the existing Rust CLI and the maintained forward-chaining oracle
`scripts/support_formula.py` rather than creating a new closure authority.
Run on a clean checkout of the selected revision, with the normal worker
environment. The first command is deliberately **not** `frontier --routes`:
the latter emits only the routes object. Store disposable exports under
`target/`, not a checked-in truth-status register.

```sh
python3 scripts/worker_env.py --check
python3 scripts/worker_env.py -- cargo build --locked --release -p truth
target/release/truth check
mkdir -p target/unconditional-audit
target/release/truth --json frontier > target/unconditional-audit/frontier.json
target/release/truth --json orphans > target/unconditional-audit/orphans.json
target/release/truth --json orphans --frontier-root STMT-GOD-EXISTS > target/unconditional-audit/god-orphans.json
```

The existing support-graph exporter accepts any number of statement IDs.
Export all statement IDs at once on Linux (not merely its default two
targets). The script below is a proposed reproducible projection, to be
executed locally; it neither writes corpus records nor changes frontier
rules. It uses the existing pinned analysis dependencies and computes
the **direct implication** closure separately from canonical
`established_statements` (which includes floor, recorded refutations and
strength). Status-qualified, non-transcription, non-model rules are a
conservative candidate set. A theorem with hidden semantic assumptions
remains a candidate for interpretation review even when it has no
graph premises. Non-transcription is not a philosophical warrant.

```sh
uv run --with dd==0.6.0 --with networkx==3.4.2 python - <<'PY'
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
from support_formula import forward_closure, validate_graph
import networkx as nx

out = Path("target/unconditional-audit")
frontier = json.loads((out / "frontier.json").read_text())
ids = sorted(frontier["statement_depths"])
assert set(ids) == set(frontier["statement_statuses"])
raw = subprocess.check_output(
    ["target/release/truth", "--json", "support-graph", *ids], text=True
)
graph = json.loads(raw)
validate_graph(graph)
assert graph["input_identity"] == frontier["input_identity"]
assert set(graph["target_statement_ids"]) == set(ids)
assert {s["id"] for s in graph["statements"]} == set(ids)
(out / "graph.json").write_text(raw)

arguments = {}
for p in sorted(Path("corpus/arguments").glob("*.json")):
    a = json.loads(p.read_text())
    assert a["id"] not in arguments
    arguments[a["id"]] = a
transcribed = set(frontier["transcription_results"])
rules = []
for r in graph["rules"]:
    a = arguments[r["argument_id"]]
    if a.get("commitment_statement_ids"):
        continue
    witnesses = [
        w for w in r["results"]
        if w["status"] in {"solution-present", "verified"}
        and w["result_id"] not in transcribed
    ]
    if witnesses:
        rules.append({**r, "results": witnesses,
                      "result_ids": [w["result_id"] for w in witnesses]})

floor = {f["statement_id"] for f in frontier["floor"] if f["met"]}
empty = forward_closure([], rules)
legacy = forward_closure(sorted(floor), rules)
established = set(frontier["established_statements"])
deps = nx.DiGraph()
deps.add_nodes_from(ids)
for r in rules:
    for p in r["premise_statement_ids"]:
        deps.add_edge(p, r["conclusion_statement_id"])
components = []
for group in nx.strongly_connected_components(deps):
    if len(group) == 1 and not any(deps.has_edge(x, x) for x in group):
        continue
    components.append({
        "members": sorted(group),
        "zero_input_reached": sorted(group & empty),
        "floor_relative_reached": sorted(group & legacy),
        "canonical_established": sorted(group & established),
        "entry_rules": sorted(
            r["argument_id"] for r in rules
            if r["conclusion_statement_id"] in group
            and not set(r["premise_statement_ids"]) & group
        ),
        "mixed_rules": [
            {"argument_id": r["argument_id"],
             "external_premises": sorted(set(r["premise_statement_ids"]) - group)}
            for r in rules if r["conclusion_statement_id"] in group
            and set(r["premise_statement_ids"]) & group
            and set(r["premise_statement_ids"]) - group
        ],
    })
# No SCC member is ever made a seed by this diagnostic.
by_conclusion = {}
all_incoming = {}
all_consumers = {}
for r in rules:
    by_conclusion.setdefault(r["conclusion_statement_id"], []).append(r)
for r in graph["rules"]:
    all_incoming.setdefault(r["conclusion_statement_id"], []).append(r["argument_id"])
    for p in r["premise_statement_ids"]:
        all_consumers.setdefault(p, []).append(r["argument_id"])

def eligible_supports(supports, reached):
    return [r["argument_id"] for r in supports
            if set(r["premise_statement_ids"]) <= reached]

inventory = []
for statement in graph["statements"]:
    sid = statement["id"]
    supports = by_conclusion.get(sid, [])
    inventory.append({
        **statement,
        "canonical_established": sid in established,
        "zero_input_direct_implication": sid in empty,
        "floor_relative_direct_implication": sid in legacy,
        "floor": [f for f in frontier["floor"] if f["statement_id"] == sid],
        "canonical_status": frontier["statement_statuses"][sid],
        "eligible_incoming_rules": supports,
        "all_registered_incoming_argument_ids": sorted(all_incoming.get(sid, [])),
        "all_registered_consumer_argument_ids": sorted(set(all_consumers.get(sid, []))),
        "zero_input_supports": eligible_supports(supports, empty),
        "floor_relative_supports": eligible_supports(supports, legacy),
        "eligible_consumer_statements": sorted(deps.successors(sid)),
        "semantic_review": "not assessed by computation",
    })
report = {
    "source_head": graph["source_head"],
    "worktree_dirty": graph["worktree_dirty"],
    "input_identity": graph["input_identity"],
    "graph_sha256": graph["graph_sha256"],
    "zero_input": sorted(empty),
    "floor_relative": sorted(legacy),
    "canonical_established": sorted(established),
    "canonical_only": sorted(established - legacy),
    "direct_only": sorted(legacy - established),
    "cyclic_components": sorted(components, key=lambda c: c["members"]),
    "inventory": inventory,
}
(out / "inventory.json").write_text(
    json.dumps(report, indent=2, sort_keys=True) + "\n"
)
PY
```

Review every entry in the zero-input set before interpreting it as a
substantive proposition. Preserve theorem-internal antecedents, axiom
footprints, consistency witnesses and the exact scope of intended
interpretations. Run `truth context ARGUMENT-ID`, `truth dossier STMT-ID`,
`truth brief STMT-ID`, `truth semantics STMT-ID` and the semantic preflight
for any proposed graft. The generated inventory links all registered supporting and consuming rules
and separately records rules eligible for the direct-implication diagnostic.
An eligible support in the completed fixed point is not necessarily an
acyclic derivation witness on its own: replay from the selected seeds to
identify a firing order. Semantic review is intentionally pending.
Prioritize zero-input results that are disconnected under both root views,
then actual observation / first-person and necessary inquiry applications
with selected witnesses; separately compare common ground for each named
rival bundle. A proof that depends on a conclusion it purports to defend
must not count as establishing that conclusion. Do not promote an
`alternative_to` set to an exhaustive partition unless certified.

Run the repository's normal verification and review gates for any later
formal changes, and report the computed
`target/release/truth frontier-diff --base <merge-base>` for both root
targets. The current note is not a new theorem, floor approval or completed
corpus-wide semantic audit.
