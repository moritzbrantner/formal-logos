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


## Checkpoint 3: logical witnesses, semantic transfer and SCC inspection

This expands the selected implication audit by 27 registered argument/result
pairs at the same pinned base. All pairs were read from their actual records
and the result status was `solution-present`; this is not a fresh verification.
The exact premises are graph premises, not the full Lean proof-import or
theorem-internal dependencies. For the central truth-pilot, retorsion and
truth-nontriviality results, the frozen Challenges, definitions and relevant
Solutions were also inspected. No new claim about the adequacy of a historical
reading is made.

The related actual-inquiry draft #1995 and conventionalism / psychologism drafts
#1991/#1990 own their wider epistemological arguments. The present lane audits
logical and semantic consequences rather than reopening those research topics.
For the existing absolute-truth, F6 and scientism grafts, reuse
[orphan-graft-map.md](orphan-graft-map.md); its one-witness examples have
already been checked in Lean there. This is not a second claim to that work.

| Registered result file | Conclusion statement ID | Argument ID | Result ID | Recorded premises | Scope, warrant or control |
| --- | --- | --- | --- | --- | --- |
| [LOGIC-NON-CONTRADICTION](../../corpus/results/LOGIC-NON-CONTRADICTION.json) | `e02e6c70-fbc0-59e2-8cef-edd44715b893` | `fcee262a-dfba-56d4-95b6-e35bbff475dc` | `436b5818-6d34-5f15-b828-a9a7b56fbc31` | none | Constructive Prop noncontradiction, not unrestricted adequacy of a rival’s negation. |
| [LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE](../../corpus/results/LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE.json) | `be102c88-1680-5837-9bf3-8491dd3280f2` | `79cc7b1f-1df3-5383-9f3f-92d1efa71742` | `3be6adf4-216f-53a0-b69b-084ac5fc7e48` | none | Every instance has double negation, not positive EM. |
| [LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE](../../corpus/results/LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE.json) | `293a58b8-5aa4-5a1d-bd2a-686cb047591f` | `0236e896-2141-5a43-a84b-274a143204ae` | `d36bd424-9fe4-5a67-a109-7d0c5c419e06` | none | No consistent denial of a particular instance; withholding survives. |
| [LOGIC-EXCLUDED-MIDDLE-IFF-DNE](../../corpus/results/LOGIC-EXCLUDED-MIDDLE-IFF-DNE.json) | `cd460425-9160-545e-92db-e8902c09e384` | `869f1010-b1d1-5937-bdff-a73583f36fd2` | `e2d8d9a4-ecab-5d32-8c57-4109df41dbb6` | none | Constructive equivalence of EM and DNE; neither asserted. |
| [EXCLUDED-MIDDLE-ASSERTION-BOUNDARY-CONTROLS](../../corpus/results/EXCLUDED-MIDDLE-ASSERTION-BOUNDARY-CONTROLS.json) | `f2b40ced-dfee-5795-a457-318f9c524d0a` | `335968ac-c307-56d5-bec1-8535ab8482ad` | `e369dd43-f8ce-5330-8701-0d355ac2865c` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` | Object-level EM can coexist with withholding the assertion; marker controls only. |
| [INTUITIONISM-ENTAILS-EXCLUDED-MIDDLE-WITHHELD](../../corpus/results/INTUITIONISM-ENTAILS-EXCLUDED-MIDDLE-WITHHELD.json) | `dd9921a6-cea1-5cb5-ac08-512a4a5b1813` | `46b46d58-747d-53a3-81d9-59945c34d014` | `66c58475-265b-5466-975d-24ea5731d7e7` | `702d4c9b-3828-5d83-8687-91d6ccdb8fa6`, `1bd98cda-fec3-5ecc-ad0c-b8b11c2b6462`, `0db3a62e-90ec-59a3-8599-f3843f636af1`, `be102c88-1680-5837-9bf3-8491dd3280f2` | Positive proof/assertion-policy rival; irrefutability is available but the other theory commitments remain inputs. |
| [ARIST-MET-1012A-THOUGHT-BIVALENCE-IFF-EXCLUDED-MIDDLE](../../corpus/results/ARIST-MET-1012A-THOUGHT-BIVALENCE-IFF-EXCLUDED-MIDDLE.json) | `90445a81-be2c-549a-b190-ceb1d1362b30` | `4c33e093-4aba-5a4d-88c3-08b1cb931925` | `13c88303-6931-5e84-bfab-6457b6cd9db3` | `62fbdad9-babe-5e3d-877e-c618858b2b19`, `b7f66357-c688-5bad-bf34-14ef9f3a87aa`, `ee440511-1103-5020-8a39-d2a6b96e5397` | Bivalence of thought under these calibrations is EM-equivalent, not independent evidence against withholding. |
| [BRIDGE-IV7-CONTRADICTORY-PAIR-FROM-EXCLUDED-MIDDLE](../../corpus/results/BRIDGE-IV7-CONTRADICTORY-PAIR-FROM-EXCLUDED-MIDDLE.json) | `78842acb-e26c-5d26-9995-cdb26e5ce9eb` | `6351bf87-7563-5c19-9720-9f160a740b3c` | `29fe4476-ee77-5eda-97eb-6a1d4d852daa` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` | Declared instantiation. Declared instantiation of EM in a state predicate. |
| [BRIDGE-IV7-EXCLUDED-MIDDLE-AFFIRMING-OR-DENYING-TRUE-OR-FALSE](../../corpus/results/BRIDGE-IV7-EXCLUDED-MIDDLE-AFFIRMING-OR-DENYING-TRUE-OR-FALSE.json) | `44dd6cf2-2f7b-5c90-9258-c9b39e3ba87e` | `237a0195-b15a-5556-9bbd-7a34ef3ad11d` | `35d98410-6cd9-5d34-912d-968ac7385870` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410`, `b7f66357-c688-5bad-bf34-14ef9f3a87aa` | Thought bivalence still needs truth-by-composition. |
| [BRIDGE-TERTIA-NECESSITY-CAUSE-OR-NOT-FROM-EXCLUDED-MIDDLE](../../corpus/results/BRIDGE-TERTIA-NECESSITY-CAUSE-OR-NOT-FROM-EXCLUDED-MIDDLE.json) | `1e3e2501-3bec-5509-b865-705209477c57` | `12f07b36-55ac-555e-aefb-db911e5816c7` | `083d31cc-f4ad-561a-818f-d91ecda3379a` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` | Declared instantiation. Case split of necessary being’s cause of necessity; no inhabitant of the necessary class asserted. |
| [LOGIC-SOME-PROPOSITION-HOLDS](../../corpus/results/LOGIC-SOME-PROPOSITION-HOLDS.json) | `15c9ec9b-ec22-52bf-9fdc-89e83c1b0a2a` | `9ea473d3-5375-50b0-8d0b-20c4209ee77f` | `7bcb4ebe-20c5-5221-85ca-2d47bd7236a7` | none | Direct True constructor; independent entry to reciprocal graph support. |
| [LOGIC-SOME-PROPOSITION-FAILS](../../corpus/results/LOGIC-SOME-PROPOSITION-FAILS.json) | `1c2b66ce-c7f0-5845-a84b-bf399126025e` | `2b1ff68f-8dfc-53ee-b1b2-43608e09b547` | `657c9b85-fbae-5828-a854-576617f76205` | none | False witness and its negation. |
| [LOGIC-NOT-ALL-FAIL-ENTAILS-SOME-HOLDS](../../corpus/results/LOGIC-NOT-ALL-FAIL-ENTAILS-SOME-HOLDS.json) | `15c9ec9b-ec22-52bf-9fdc-89e83c1b0a2a` | `c5c9ff49-a3ec-557c-a25a-ae360a25d478` | `e630f67c-488b-56f1-8d05-d2b9e19b88a0` | `8efdfe70-cb76-575f-a13c-16a35cfb7c9e` | Witness the proved proposition not-all-fail itself; not existential elimination for arbitrary predicates. |
| [LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL](../../corpus/results/LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL.json) | `8efdfe70-cb76-575f-a13c-16a35cfb7c9e` | `ec000eff-7de6-5ffc-b126-0b9bc328b741` | `71ac7c71-9ea4-5cf0-a92a-25e01d79a9d2` | `15c9ec9b-ec22-52bf-9fdc-89e83c1b0a2a` | Eliminate the witness against the universal denial. |
| [LOGIC-NO-GLOBAL-PROPOSITIONAL-COLLAPSE](../../corpus/results/LOGIC-NO-GLOBAL-PROPOSITIONAL-COLLAPSE.json) | `a919f81e-d9ff-5b7a-be38-c9473c042e8e` | `6a7f2ea8-64a3-5c84-905e-97f2a4ac0dd1` | `f79ddcf6-2f42-5f55-a249-1e509705955f` | none | Not all Props are logically equivalent; uses the two witnessed poles inside Lean. |
| [TRUTH-COLLAPSE-CONTROLS](../../corpus/results/TRUTH-COLLAPSE-CONTROLS.json) | `e6f8513b-4ed5-58a8-831a-2cf3b2293d1f` | `657ed546-c5c0-5ce1-abc5-7c6ae02c0d8e` | `e67a42c3-c904-58bd-8d4b-e9f2b8e51edc` | none | Model certificate: one-point uninterpreted structure, local/global profile controls, glut and relative/nihilist controls; no actual-world model selection. |
| [TRUTH-ACCOUNT-COMPATIBILITY](../../corpus/results/TRUTH-ACCOUNT-COMPATIBILITY.json) | `f64df602-bf01-563b-826f-9752feb75293` | `5ef7bff1-57b7-5905-87a8-cbe63286e341` | `74f123ce-4e4f-5d02-b505-95a0d8a5e4ce` | none | Encoded intuitionist and signed thought-composition accounts are jointly witnessed, not actual truth. |
| [LOGIC-EMPTY-EPISODE-CONTROL](../../corpus/results/LOGIC-EMPTY-EPISODE-CONTROL.json) | `81a85cbd-3661-5b1b-bff3-f2f3b43edc56` | `f6846c20-a34a-5ece-b7d0-8fce84bcf510` | `f7df7705-20a4-5236-9378-69d9ea187194` | none | Model with no actual performance; retorsion alone cannot supply occurrence. |
| [LOGIC-STATIC-EPISODE-CONTROL](../../corpus/results/LOGIC-STATIC-EPISODE-CONTROL.json) | `d0f04b5b-5c5f-5397-86ca-432de73877c7` | `d9f68331-16fa-59bd-b546-e374f40526fb` | `3fab8a6b-ed9a-5851-b6a0-656bd076278a` | none | One occurrence with constant state; no succession inferred. |
| [LOGIC-PERFORMED-DENIAL-RETORSION](../../corpus/results/LOGIC-PERFORMED-DENIAL-RETORSION.json) | `17f2fdc1-4dcf-564b-afc3-9bdad891966e` | `768cabc8-a429-532b-b11c-457e203f12ca` | `bfda68fd-6fd2-5a26-afe5-1ac99eb01ba3` | none | No accurate performed universal denial in its own episode class; no actual token supplied. |
| [OBJECTIVE-TRUTH-ACTUAL-STABLE-TO-TRUTH-COMPONENT](../../corpus/results/OBJECTIVE-TRUTH-ACTUAL-STABLE-TO-TRUTH-COMPONENT.json) | `40840c3d-90da-5237-b2a3-8ea9519b5c9c` | `ef2848bf-d993-51a1-bb0b-19a473296054` | `489f716a-6306-5e51-be37-f46df5448b3f` | `326adc2f-b56d-58af-802e-9bf3a6f46c61` | Actual-and-stable calibration implies truth component, not either calibration's applicability. |
| [OBJECTIVE-TRUTH-DEFINITION-CONTROLS](../../corpus/results/OBJECTIVE-TRUTH-DEFINITION-CONTROLS.json) | `ccea0d68-5dbd-5120-acd6-83222ab4a0b4` | `480e3afc-c9b8-5806-8dec-f532d05464f3` | `b0ae9897-6c8e-57de-8b92-d852600f9cf8` | none | Finite definition controls; actual-truth, invariance and classification differ. |
| [OBJECTIVE-TRUTH-DEFINITION-FORK](../../corpus/results/OBJECTIVE-TRUTH-DEFINITION-FORK.json) | `dac67701-e7fc-538e-a33a-45e1349fb088` | `3adb1eff-7827-554f-b33e-7837a0eea329` | `7cd27d15-79aa-5a39-bcd2-48115f91f44a` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` | Declared instantiation. EM case split includes remainder; does not establish named exhaustiveness. |
| [OBJECTIVE-TRUTH-EXTERNAL-BRIDGE-NEEDED](../../corpus/results/OBJECTIVE-TRUTH-EXTERNAL-BRIDGE-NEEDED.json) | `eac971d2-9af3-5709-b053-71cfa55cf89b` | `a0939704-3326-5c06-b962-f081792e5002` | `3475369c-9c70-576e-96fa-8b1e62e15f55` | none | Stably false content separates profile invariance from actual truth; limits external-evil argument. |
| [OBJECTIVE-TRUTH-FROM-NAMED-ELIMINATION](../../corpus/results/OBJECTIVE-TRUTH-FROM-NAMED-ELIMINATION.json) | `326adc2f-b56d-58af-802e-9bf3a6f46c61` | `a3281a44-78c4-5b61-aa37-852a619d4fbb` | `3081f575-fefa-55d0-97f3-cef393309611` | `6cdc4062-245e-5f84-9b1c-117673045506`, `d792059e-0b01-56a9-9bde-6abcd158024b`, `266890f6-6b38-5d42-8fa9-57e6d731c4b8` | Declared instantiation. Named coverage and both exclusions are open; elimination transcription. |
| [RELATIVISM-NO-ABSOLUTE-TRUTH-MODELS](../../corpus/results/RELATIVISM-NO-ABSOLUTE-TRUTH-MODELS.json) | `3ecdf33e-621c-5f6f-99a3-1ad2f079fe9e` | `fcf2e749-76a3-5da6-9ebf-74d0bef5d2a0` | `6fee2b02-5bb9-534f-830d-81694aacfc33` | none | Relative assertion and exempt absolute assertion have models; no general proof of relativism. |
| [RELATIVISM-NO-ABSOLUTE-TRUTH-SELF-FALSIFYING](../../corpus/results/RELATIVISM-NO-ABSOLUTE-TRUTH-SELF-FALSIFYING.json) | `13490096-3453-5792-a4a8-d8e2f7a0fe4c` | `114d2581-ae65-50b8-9001-1154c0f31de6` | `dbc2fb38-580c-5f0c-813d-767076523c8b` | `5c18a8c4-c908-5397-b429-44c20b48c87e`, `de454f1e-652d-5ab3-8888-3259bc829b60` | Requires own scope and disquotation; rejects absolute assertion, not the relative-only model. |

### Executed expanded sample and regression controls

The union of the original fourteen rules and these 27 rules has **41 distinct
argument IDs**. Using least-fixed-point chaining with complete conjunctions,
the selected registered rules give:

| Basis | Newly reached conclusion IDs |
| --- | ---: |
| Empty input | 23 |
| Eight floor markings supplied hypothetically | 29 |
| Same hypothetical floor, omit four explicitly declared instantiation edges | 26 |

These are counts of this induced sample, not whole-corpus counts, philosophical
establishment, fresh verification or the canonical frontier's computed
closure. Full heuristic transcription filtering remains pending. The
empty-input conclusions include the existence of finite control models
and universal conditional laws; those must retain their types. A
`commitment_statement_ids` bundle is not automatically a new truth seed.

The directed premise-to-conclusion projection of these 41 rules contains one
nontrivial strongly connected component, with two members:

- `15c9ec9b-ec22-52bf-9fdc-89e83c1b0a2a`, SomePropositionHolds.
- `8efdfe70-cb76-575f-a13c-16a35cfb7c9e`, NotEveryPropositionFails.

The internal edges are arguments `c5c9ff49-a3ec-557c-a25a-ae360a25d478`
and `ec000eff-7de6-5ffc-b126-0b9bc328b741`. Two registered zero-premise
arguments enter this SCC, `9ea473d3-5375-50b0-8d0b-20c4209ee77f` and
`83208e1e-e6bf-53e7-a0a6-eeb481d6f22f`. Reading the Solutions is important:
the second actually imports and consumes the first, so these are not two
independent grounds. The independent entry is the direct `True` constructor
in [SomePropositionHolds/Solution.lean](../../TruthCore/Results/Logic/TruthPilot/SomePropositionHolds/Solution.lean).

Two deletion controls were executed on the selected **graph edges**, not on
the Lean library. Removing the second zero-input rule alone retains the
independent first and derives NotEveryPropositionFails in round two.
Removing both zero-input rules makes neither SCC member reachable from
the empty input, despite both reciprocal implications. The underlying
Lean theorems are not invalidated by these graph counterfactuals.

Reproduce the selected sample in a checkout: parse the UUID columns in the
two tables, select these exact argument IDs from the exported support graph,
and use `support_formula.forward_closure` and the existing NetworkX SCC
projection from the whole-corpus recipe above. Verify the four recorded
instantiation flags against their result records; the sample omits only
declared transcriptions for the third row, not heuristic flags. For each
deletion control keep the remaining graph and the empty seed set fixed.
No SCC is supplied as an input.

### Semantic findings and live decisions

**1. Nontrivial logic has a genuine constructive floor, not an unrestricted
metaphysics.** The proof of SomePropositionHolds constructs `True`; the
proof of SomePropositionFails exhibits `False` with its negation. The
noncollapse result combines the two and therefore establishes a difference
in truth/equivalence inside the encoded `Prop` domain. The exact
`UndifferentiatedStructureModel` conjunct of
[TruthCollapseControls](../../TruthCore/Logic/TruthNontriviality.lean)
has that noncollapse together with a nonempty one-point carrier, an identity
step function and an empty relation. It is a control on the **lack of a
formal connection** from propositional noncollapse to numerical multiplicity
of beings, change or causal relations. It does not establish that the actual
world has those features. The performed-denial static control gives a
different, already recorded reason that occurrence alone does not yet
supply the prima via's change premise. Hence do not infer actual
metaphysical composition or productive dependency just from logical
noncollapse. This bears on both impersonal and theistic worldviews equally.

**2. The logical case split used by the tertia via is floor-relative, not a
proof of the existence of its subject.** The exact instantiation result
`083d31cc` concludes `1e3e2501` from excluded middle, not from the
constructively proved irrefutability `be102c88`. Excluding a denied
instance or establishing EM-equivalent bivalence does not derive EM.
The universe of necessary beings can be empty for a universal
cause-of-necessity dichotomy. The existing route therefore needs a
population/necessary-being witness and the causal/necessity bridges
separately. No new modal or causal assumption follows by the case split.

**3. Absolute truth is an application test, not a new lemma search.**
The authoritative target `f625ad83-909e-52e2-b74a-92b0725c1629` uses
`Relativism.SomeAbsoluteTruth T := ∃ p, T.trueAbs p`, not Lean's
`SomePropositionHolds`. Its rival `bff72296-915a-543f-8903-182edf096dfc`
denies this in the same content domain. The existing `TruthNontrivialityCore`
has the disquotation-plus-capture exclusion of the global denial and the
expressivity condition; the stronger relative-only control explicitly
satisfies global no-absolute-truth while preserving expressive relative
predicates. The proof of `NotEveryPropositionFails` is real, but its
capture in a specified actual-language absolute truth predicate is not
provided by that proof. The existing orphan note already derives the
one-content capture and F6 applications and identifies the difference
between an empirical establishment predicate and exclusive empirical
origin. Do not register a second derivation whose only new premise restates
its conclusion. The next positive test is semantic: take the particular
proved proposition, determine whether the rival can express its very
truth without changing its content or restricting the truth predicate's
scope, and distinguish (a) local content truth, (b) context-independent
truth of that content, (c) a mind-independent truthmaker, and (d) a
world-independent modal necessity. These are not interchangeable.
The indexed search on current main returned no argument record mentioning
the full target ID `f625ad83` (nor a consumer of `61f64a70` beyond its
producer); this is an indexed discovery result, not exhaustive proof
of absence, and the checked applications and contextual attacks already
exist. Use the canonical dossier and novelty/semantics commands before
any registration.

**4. Objective truth and absolute truth are distinct targets.** The
existing `ObjectiveTruthDefinitionFork` records a stable-false control:
profile invariance by itself cannot yield actual truth. Neither
`HasTruthComponent` nor `ActualStableDefinition` asserts that any
objective content is instantiated. The objective-truth named elimination
requires named coverage (not the EM split containing a remainder) and
the other two exclusions. These distinctions also constrain the
external moral-evil argument; do not transfer the truth-pilot's logical
noncollapse into actual moral realism or the pure-perfection argument.
The formal controls are strong scope separators, not evidence that
ordinary speakers use “objectively true” for stably false propositions.

**Provisional reassessment.** Favor the directly witnessed constructive
logical core and distinguish it from every extra semantic or existential
application. For rejecting a global skeptical denial, actual meaningful
use of a matched content may give first-person or cumulative warrant
without an independently demonstrated universal semantic calibration.
Keep that warrant inquiry open; no skeptical position is eliminated
merely by adding an abstract control, and no arbitrary skeptical rival
is introduced. The strongest standing cases in this slice are already
recorded: proof-relative withholding, scoped/relative truth, modelled
no-episode/constant-state controls. Their existence is formal compatibility,
not a claim of equal philosophical warrant. Reopening condition: a
justified same-content actual witness, or a proof in the already fixed
truth/episode semantics that transfers that witness without packing the
target into a premise. Independent semantic challenge remains pending.

The working environment still cannot resolve github.com for a local
checkout, and the public deployed graph manifest was inaccessible to
the retrieval tool. The complete canonical closure, verified current
floor, all-corpus SCCs and application review still require the local
replay. No corpus records or floor markings are changed in this checkpoint.


## Checkpoint 4: actuality, modal certificates and concrete contingency

Pinned to the same baseline as checkpoints 2–3. The current main had moved
to `bff18fce135d73ffe2e00933a56decdb2a1c89af` when this checkpoint began;
the sample remains pinned to the initial revision for reproducibility.
The related actual-inquiry research #1995 owns its broader epistemological
applications. This lane compares actual-population and modal application
bases, reusing [modal results triage](modal-results-triage.md) and the
[modal spine](modal-spine.md).

### Executed closure and conditional impact

A further 42 directly inspected argument/result pairs extend the selected
sample to 83 distinct registered arguments. All new result records have
status `solution-present`. In the resulting graph the least-fixed-point
chaining gave:

| Basis | Newly reached conclusion IDs |
| --- | ---: |
| Empty input | 41 |
| Eight recorded floor markings hypothetically supplied | 47 |
| Same floor, excluding explicitly declared transcriptions (instantiation and assembly) | 42 |

These are sample diagnostics, not philosophical truth judgments, fresh
verification or whole-corpus counts. The only nontrivial SCC in this
sample remains the two-statement truth-pilot cycle in checkpoint 3.
The complete added rule inventory is appended below. The full canonical
frontier has its own handling of heuristic transcriptions, strength
registrations, counted refutations and met floor criteria.

Compare additional reached IDs beyond the empty-input baseline and the
scenario's own seeds. No floor seeds are added to this comparison.

| Scenario | Additional conclusion IDs in the selected graph |
| --- | --- |
| Actual concrete population `56f68b40` | none |
| Actual concrete contingency `c94b5446` | `185ce448`, `56f68b40`, `602246df`, `9aeab54e` |
| Contingency + T schema `cb456382` | the same four and `5089057e` |
| Contingency + B schema `98bede5a` | the same four and `a03ed3eb` |
| Contingency + T and 5 schemas `cb456382`, `6f474aba` | the same four and both `5089057e`, `a03ed3eb` |

**Concrete population and actual contingency must remain separate.**
`56f68b40` is recorded as a working truth, not a floor marking, and has
substantial direct warrant from actual exercise without settling whether
a bearer is an immaterial substance. `c94b5446` additionally requires a
genuine accessible alternative where the very same concrete individual
is absent, not merely an alternative description, an earlier time, or
a different state of it. Its actual contingency is still open. Its
existing checked consequences exclude concrete necessitarianism,
actual full modal collapse and a necessarily performed act token that
strictly yields every actual concretum. The T/B/5 schema inputs give
further collapse exclusions. These consequences constrain both theistic
and impersonal necessitating-source theories, without additional causal,
choice, personality or PSR premises; a necessary source whose productive
exercise is not both necessary and strictly efficacious survives.
The conditional refutations cannot defend their own source premise.
The modal triage note already records these connections; the reconciled
theorems import verified modal laws rather than retain their certificates
as open graph premises.

### Candidate graft: actual population supplies possible population

The existing [empty-history necessary-being result](../../TruthCore/Results/Explanation/EmptyHistoryCausalAvailability/Challenge.lean)
(result `e9b7ecc7-c668-54c2-a82d-62e804c75af5`, argument
`c34db0b0-141a-5b87-86cb-59528aa0af99`) consumes the open possible
population premise `5a12e877-ef76-5763-b149-1fe063f8384e` and already
requires actual reflexivity `2b20b5af-d653-56ba-8001-35903fb3d1ea`.
If the directly warranted actual concrete population
`56f68b40-9737-59a0-8cac-5610980a1547` uses the same Ontic,
Concrete and actual standpoint w, choose w itself as the possibility
witness. No new possible history, S5, causal production, or actual
contingency principle is required.

Uncompiled local candidate, using only existing definitions:

```lean
import TruthCore.Explanation.EmptyHistoryCausalAvailability

open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

example {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (w : W)
    (hActual : InhabitedConcreteAt A.ontic Concrete w)
    (hReflexive : ActualReflexive A.ontic w) :
    PossiblyInhabitedConcreteAt A Concrete w :=
  ⟨w, hReflexive, hActual⟩
```

The exact definition is an existential over accessible worlds with the
same `InhabitedConcreteAt` predicate. Current-main indexed search found
the target ID only in the empty-history consumer and the Lean declaration
in that module, its result and its count control; this is not exhaustive
novelty evidence. Run the normal `truth related`, `truth dossier`,
`truth novelty`, and `truth semantics` checks on the three full IDs
before registering a graft. This is a witness instantiation and may be
classified as a transcription, not a substantive new theorem or
independent metaphysical warrant.

It replaces a separate possible-population input with an already
available actual-population input on this route, if the interpretation
matches. The original consumer's other inputs are retained: EM,
Euclidean access, the fixed negative-fact meaning, and the three-part
accessible empty coverage. It does not prove a necessary being from
population and reflexivity alone. In particular, a consumer whose
`ExistsAt` represents whole-history EVER-existence cannot silently
consume an actual witness calibrated only to a now-slice. The existing
history correspondence remains open, as do admission and causal
availability of the negative fact. A fact is not an individual and
CauseFact is not Ontic.Causes.

**Executed finite boundary test (Python, not Lean).** The following
enumeration ran across 128 assignments of concreteness for one candidate,
existence at two labels, and four accessibility edges. All forward
implications held; all four omission/separation controls were found.

```python
from itertools import product
controls = set()
for c, e0, e1, a00, a01, a10, a11 in product((False, True), repeat=7):
    e = [e0, e1]
    a = [[a00, a01], [a10, a11]]
    actual = c and e0
    reflexive = a00
    possible = any(a[0][v] and c and e[v] for v in range(2))
    contingent = actual and any(a[0][v] and not e[v] for v in range(2))
    necessary = all(not a[0][v] or e[v] for v in range(2))
    assert not (actual and reflexive) or possible
    assert not contingent or actual
    assert not (contingent and necessary)
    if actual and not reflexive and not possible:
        controls.add("omit reflexivity")
    if reflexive and not actual and not possible:
        controls.add("omit actual population")
    if possible and reflexive and not actual:
        controls.add("reverse fails")
    if actual and reflexive and necessary and not contingent:
        controls.add("contingency does not follow")
assert len(controls) == 4
```

These are finite controls of the stipulated predicate shapes, not
substantive philosophical objections or metaphysical possibility
certificates.

### Actuality: the weakest local commitment versus the universal thesis

The [Ontic](../../TruthCore/German/Kant/CosmologicalInference.lean)
actual existence predicate is independent of candidate-domain membership
and of the cause relation. The [esse contract](../../TruthCore/Causality/ExistenceActuality.lean)
`0436de86` is a one-way interface into a supplied act-in-esse respect.
Its intended profile can have direct conceptual warrant, but in an
arbitrary assignment the existence and act predicates are independent.
The two perfection premises `ca84f62d`, `196e6606` support both the
direct `7067553d` and negative `65c301a8` routes. Reconstructing the
positive thesis classically from the latter is not independent support.
The existing golden-mountain omission controls distinguish predication
of a candidate from its being in act in the chosen esse respect.
A Meinongian account of true predication of a nonexistent object does
not itself establish a realized operation of that object.

The merely-possible route needs `a62975a9` and `c85117b0`. In the
[actuality map](../../TruthCore/Causality/Round2ExistenceAct.lean),
MerelyPossible is a supplied predicate, not a defined complement.
An intended reading of *merely* possible as possible but not actual
supports the second (disjointness) conceptually; it does not support the
first universal claim that every candidate lacking esse is merely
possible, especially for a Platonist admitting nonproductive abstracta.
A direct actual witness and a universal act/esse thesis are different
commitments. Prefer testing the local act-to-existence and
existence-to-act use sites, preserving wider principles as independent
questions.

The configured necessary-to-act theorem `17ae2081` also isolates
a logical strength boundary. Under actual reflexivity, absence of
possible absence constructively yields double-negated actual presence:
assuming absence here supplies a counterexample at w. The registered
proof uses EM on that particular existence proposition to obtain
positive presence, then consumes `ExistingInActAt`. If a same-bearer
positive `NecessaryAt` (box-existence) premise is already warranted on
the intended Ontic, reflexivity immediately yields presence without this
EM step. The existing `necessaryAt_iff_boxExistsAt` is definitionally
proved. No constructive equivalence of positive box and the negative
reading is asserted. Actualist K/possibilist K root equivalence is
conditioned by the existing packed actual-root facts; arbitrary K-box
existence need not imply actual existence. Neither the universal
necessary-to-act bridge nor tertia-via convergence establishes the
existence of a necessary candidate or of a maximum.

### Exact modal escalation, without an extra metaphysical axiom

The registered zero-external-premise certificate `0b44216e` proves
equivalence of forward escalation for all predicates and masked successor
connectivity. The [existing solution](../../TruthCore/Results/Modal/NecessaryIfConnectivity/Solution.lean)
already proves both rival escalations from connectivity and the boxed
conditional in `matrix`; EM is used for coverage. Its reflexive symmetric
three-world line is not Euclidean. Thus Euclidean access is sufficient
but not the minimal mathematical condition. Existing statement
`0523281a-0c8b-5cc3-a05e-dfb111d706cc` names connectivity;
`c41962ba-9ff9-511a-a837-d5339dc2c690` names all-predicate validity.
The positive and negative registered results use Euclidean access.
A same-standpoint alternate derivation can consume the existing
`matrix` (or propagation helpers) without new mathematics; it needs
the normal binding and semantic checks and an actual consumer before
registration. For one fixed God predicate, the all-predicate
correspondence need not be necessary. No frame applicability, boxed
conditional for GOD_4, or possibility horn is established. Empty K5 and
disconnected S5 controls prevent inferring an actual or global necessity
from coverage alone.

**Next decisive test:** establish whether actual concrete occurrence
supplies justified accessible absence of the same concretion, not just
a change of states or our description. If this cannot be warranted
directly, retain actual population as the weaker direct starting point.
Test the local existence-to-esse interpretation without presupposing
the universal act-to-being principle. Coordinate these tests with the
existing actuality and contingency research, not an overlapping
formalization. No new floor status or corpus record has been added.

The environment was rechecked: `git ls-remote` failed with
"Could not resolve host: github.com", and neither cargo nor lake was
available on PATH. Full local closure, heuristic transcription/axiom
audit, local compilation of the example, and independent semantic
challenge remain pending.

### Exact added rule inventory and reproduction

All 42 pairs below were read at the pinned baseline, with matching argument/result
IDs and recorded solution-present status. The rows preserve graph premises;
their universal hypotheses and proof imports remain in the theorem types.
The declared transcription annotation is not a substitute for the canonical
heuristic. The zero-input closure includes formal controls and certificates,
not the truth of what their models represent.

| Result file | Conclusion ID | Argument ID | Result ID | Full graph premise IDs | Interpretation / boundary |
| --- | --- | --- | --- | --- | --- |
| [actualist-possibility-boundary](../../corpus/results/actualist-possibility-boundary.json) | `0465695f-0070-574b-b07c-dadfcea317ef` | `479efd00-820d-5d4b-9576-142d30b5f720` | `3b01b485-0f9c-567a-8f65-43a24ff297c1` | `8aa0a46a-473f-544c-9686-9e028d0285e3`, `938650b0-ff50-5c60-8b70-5b7dc600eaaf` | Gödel 1970 actualist antecedent excluded with positivity and symmetry, not theism or Scott. |
| [EXISTING-IN-ACT-AT-FROM-SOME-ACTUALITY](../../corpus/results/EXISTING-IN-ACT-AT-FROM-SOME-ACTUALITY.json) | `0436de86-6579-53f2-9ff5-2111ba44ebae` | `425afcd6-3304-5142-9ab5-830076908a40` | `b9846898-43d2-5856-8a23-51a2289c2495` | `adf07168-21a9-5ea3-83b1-7d404f3f6421`, `7067553d-cad9-5d79-b6b2-912e35051530` | Existence to esse contract through some act and act-to-being; no converse. |
| [ACTUALITY-WITHOUT-BEING-NOT-ELIMINATED](../../corpus/results/ACTUALITY-WITHOUT-BEING-NOT-ELIMINATED.json) | `e5d79009-a63d-5e24-960e-4cd34b74e786` | `1aa44995-a4b9-5796-8fb1-72efea0d8893` | `3db73abe-e200-5099-92f8-84d8ab6c8c80` | none | Tested elimination reduces to double-negated disputed premise; rival not excluded. |
| [ACTUALITY-ONLY-INSOFAR-AS-BEING-FROM-MEINONGIAN-REFUTATION](../../corpus/results/ACTUALITY-ONLY-INSOFAR-AS-BEING-FROM-MEINONGIAN-REFUTATION.json) | `7067553d-cad9-5d79-b6b2-912e35051530` | `547f928a-d0cd-5b25-b702-dbbaa052f450` | `e0677f8f-730a-5f01-91c7-3601a8f3a84b` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410`, `65c301a8-afb4-5d75-a321-9a1c0c67af65` | EM and negative result yield positive universal; same perfection dependencies. |
| [ACTUALITY-ONLY-INSOFAR-AS-BEING-FROM-PERFECTION](../../corpus/results/ACTUALITY-ONLY-INSOFAR-AS-BEING-FROM-PERFECTION.json) | `7067553d-cad9-5d79-b6b2-912e35051530` | `8ba56e15-0d7d-567d-a45a-92b84b03972b` | `4c1c8b86-53b1-58cc-bdc1-34efacc6966f` | `ca84f62d-67cb-58a6-bc3e-a631ab46e3d1`, `196e6606-d61b-59c4-a12b-7ce056936b92` | Perfection in act and perfection only insofar as being, both open. |
| [NO-ACTUALITY-WITHOUT-BEING-FROM-PERFECTION](../../corpus/results/NO-ACTUALITY-WITHOUT-BEING-FROM-PERFECTION.json) | `65c301a8-afb4-5d75-a321-9a1c0c67af65` | `c2a87347-2c5d-5e76-a2a9-0659136ef542` | `0256bc45-17d7-500c-80ac-8f61ba0781ff` | `ca84f62d-67cb-58a6-bc3e-a631ab46e3d1`, `196e6606-d61b-59c4-a12b-7ce056936b92` | Same two premises exclude encoded rival; not independent evidence. |
| [MEINONGIAN-ACTUALITY-CONTROLS](../../corpus/results/MEINONGIAN-ACTUALITY-CONTROLS.json) | `3eca738f-2066-58d1-a1f9-52350f4af791` | `351c3920-d935-5f7c-9459-60b84c226c2e` | `f91a71d7-0337-56e9-bf58-74a703866520` | none | Golden-mountain omission controls, not actual rival truth. |
| [MODAL-NECESSARY-BEING-ACTUALITY](../../corpus/results/MODAL-NECESSARY-BEING-ACTUALITY.json) | `d76abd3e-6b06-52d0-994f-c819bed63897` | `e8dc6592-a90c-50f7-8324-357c2a948e31` | `17ae2081-1352-57c5-b5fd-e1ae3219411c` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410`, `2b20b5af-d653-56ba-8001-35903fb3d1ea`, `0436de86-6579-53f2-9ff5-2111ba44ebae` | No possible absence to presence via EM and reflexivity; no existence witness. |
| [NECESSARY-ROOT-BOX-T-STRENGTHENS-ACTUALIST-K](../../corpus/results/NECESSARY-ROOT-BOX-T-STRENGTHENS-ACTUALIST-K.json) | `7f24ce4d-9d93-56dc-9bd6-2dd947c224e5` | `3fe7c31a-f477-568f-a408-a3e29eada228` | `90157e4c-1344-52b1-b01d-7b90f0a4cedf` | `49a47eb5-c4bd-5880-b981-8cc4003b3b1b` | Root premise already contains actual bearer. |
| [NECESSARY-ROOT-ACTUALIST-K-STRENGTHENS-BOX-K](../../corpus/results/NECESSARY-ROOT-ACTUALIST-K-STRENGTHENS-BOX-K.json) | `cdf897a8-5490-561a-b9d2-507486a3f192` | `25bfe291-d969-57e1-8320-59c5996135b3` | `5c9e78c3-1e39-5d3e-9b84-4253ff87b4fd` | `7f24ce4d-9d93-56dc-9bd6-2dd947c224e5` | Declared transcription. Assembly: drop actual-existence clause, existing equivalence not fresh evidence. |
| [MODAL-K-LAWS](../../corpus/results/MODAL-K-LAWS.json) | `0d0b6e3c-6207-5284-bf0b-7dce386ba347` | `47a688e5-f17e-5bd2-8278-a66b408c3b05` | `c3e2bc08-bbc6-5b40-8b7b-9acb876f0631` | none | Mathematical full-predicate collapse / successor identity. |
| [MODAL-T-LAWS](../../corpus/results/MODAL-T-LAWS.json) | `e2de4fb7-a47d-5670-90bf-d48c0e52f75f` | `f9e11467-318c-5f4c-bbdc-0fd62c7141e6` | `bd043b01-df8e-547b-ab47-4ea2b951afd1` | none | T conditional frame laws, not actual reflexivity. |
| [MODAL-B-LAWS](../../corpus/results/MODAL-B-LAWS.json) | `e1329ed7-6581-5862-a9b1-ab90a5e7fc8e` | `5cc9b388-18b4-5291-9e43-548c993f7fe1` | `a9ec8cc6-f83d-5ce7-bc0e-cac6a183a49b` | none | Symmetry collapse propagation; reflexivity for converses. |
| [MODAL-D-LAWS](../../corpus/results/MODAL-D-LAWS.json) | `888871a5-4d97-51e2-8def-bce4b69372c5` | `3be79b2e-0fa6-5abc-a9a4-eaaebb6b0cfb` | `7511bf26-aa10-57ce-a7db-d49a048465ab` | none | Serial-frame conditional law, no metaphysical frame truth. |
| [MODAL-S4-LAWS](../../corpus/results/MODAL-S4-LAWS.json) | `58fa71d7-159f-5e6c-9d03-0a2ed2e7ddf6` | `2ce5e758-84ca-553d-be41-6ca0e5241ccf` | `811f302c-b36b-575f-a9c6-f6b4c191e7d3` | none | S4 collapse and cluster conditions; given frame properties. |
| [MODAL-S5-LAWS](../../corpus/results/MODAL-S5-LAWS.json) | `1f21c751-c8eb-570e-8359-b139fe4fbcff` | `a8fa4489-95c5-5a29-b2c6-d40deadd030e` | `b52d36f7-2e62-5d3e-b2dd-1550199b3812` | none | Full collapse excludes contingency under S5; no actual frame asserted. |
| [MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE](../../corpus/results/MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE.json) | `8239eddf-aadf-5ad7-9243-e7698c7e8d27` | `5638e542-b04a-5394-bafc-06b0f7b70bbd` | `5792f1a1-8474-5b0b-9b03-ab6e0e83fdec` | none | Declared transcription. Assembly: universal T/reflexive and D/serial correspondence; empty carrier allowed. |
| [MODAL-T-FRAME-BOUNDARY](../../corpus/results/MODAL-T-FRAME-BOUNDARY.json) | `5eff5171-dfb3-55a8-afb0-fd2db3961b8b` | `bb262988-68c4-55a0-802a-363b77c78f71` | `676c1e40-122f-56b6-9b89-db04333f80d9` | none | Reflexive chain lacks symmetry/transitivity; inventory matters. |
| [MODAL-S5-DOMAIN-BOUNDARY](../../corpus/results/MODAL-S5-DOMAIN-BOUNDARY.json) | `d1737c2e-c7fe-5e55-8ac9-e235786b8cd1` | `d5648baf-a877-5136-8543-ec12b933f277` | `64f3293f-e58a-5b4d-b126-eb6feaee490f` | none | Restricted proposition inventory changes collapse test. |
| [MODAL-S5-SYMMETRY-BOUNDARY](../../corpus/results/MODAL-S5-SYMMETRY-BOUNDARY.json) | `92df4ab0-edfe-518c-80b6-827aa283aa8c` | `d03ead21-8fd8-5061-b831-db6cb5120c74` | `e2a36f6f-0504-52e3-b348-90e8c11aadf4` | none | Reflexive transitive nonsymmetric control separates propagation. |
| [NECESSARY-IF-EXISTENT-CONTROLS](../../corpus/results/NECESSARY-IF-EXISTENT-CONTROLS.json) | `eef92037-9447-5920-b588-9d056a13ed98` | `9676146a-e4f2-5e1a-96bd-d8ac97ca4b6a` | `ceeb12bd-8442-511a-995f-a105e953887e` | none | S4, actual-only, nonserial K5 and disconnected S5 controls. |
| [NECESSARY-IF-EXISTENT-COVERAGE](../../corpus/results/NECESSARY-IF-EXISTENT-COVERAGE.json) | `306493cd-404d-5aca-afd5-860ce74f3bd6` | `f2251a3d-0e5d-5446-9790-02f5c8ce4146` | `ce06db1e-4cc3-570d-8a39-84d32b508707` | `62b4a40a-919e-5da4-998c-131c386b7361`, `bd1281e6-75b3-5503-8c0a-f97213388c88`, `ee4ab504-c8fe-59bc-bc96-7cbeefed6410` | Coverage of necessary alternatives, neither selected nor exclusive without nonvacuity. |
| [NECESSARY-IF-EXISTENT-EXACT-FRAME](../../corpus/results/NECESSARY-IF-EXISTENT-EXACT-FRAME.json) | `0b44216e-ad42-5a27-8fc9-00852620516c` | `077a885d-b7a8-5f24-bfba-e6365ab7ed75` | `a61757ac-27a5-5f9e-9509-2fcb59153cab` | none | All-predicate masked successor reachability; Euclidean sufficient not necessary. |
| [NECESSARY-IF-EXISTENT-NEGATIVE](../../corpus/results/NECESSARY-IF-EXISTENT-NEGATIVE.json) | `49b675bf-5ce1-5168-8e1c-5725970869b4` | `d9cbeaad-9a24-5147-a6f2-6c875c3a6fd0` | `a179ee3e-87cb-5ee3-b697-988800344744` | `62b4a40a-919e-5da4-998c-131c386b7361`, `bd1281e6-75b3-5503-8c0a-f97213388c88`, `d8018f24-e70f-5cce-b3ad-3b7b472e83a7` | Possible absence escalates to impossible existence given boxed conditional and frame. |
| [NECESSARY-IF-EXISTENT-POSITIVE](../../corpus/results/NECESSARY-IF-EXISTENT-POSITIVE.json) | `9a847482-82a0-5a76-987b-a9b46d38b7da` | `c9936c30-bf57-5713-8683-40752a182efd` | `d9db5ed8-4a7d-5e11-8c4a-16ee0669a1ac` | `62b4a40a-919e-5da4-998c-131c386b7361`, `bd1281e6-75b3-5503-8c0a-f97213388c88`, `dda96283-22ca-5580-bdc5-56a21ade6cc3` | Possible existence escalates to necessity; possibility not supplied. |
| [EXISTING-IN-ACT-AT-FROM-MERE-POSSIBILITY](../../corpus/results/EXISTING-IN-ACT-AT-FROM-MERE-POSSIBILITY.json) | `0436de86-6579-53f2-9ff5-2111ba44ebae` | `f1ea8b89-cbcf-5327-9256-c77e708ae5f9` | `b4e28e3d-3604-5e6f-afa2-5036e9fabb96` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410`, `a62975a9-bcd4-5bc7-83e7-6d4f5d2b2c13`, `c85117b0-6113-5460-95d8-5593d1acd49d` | Primitive MerelyPossible and lack-esse bridge separate. |
| [EXISTING-IN-ACT-AT-FROM-ELEATIC-POWER](../../corpus/results/EXISTING-IN-ACT-AT-FROM-ELEATIC-POWER.json) | `0436de86-6579-53f2-9ff5-2111ba44ebae` | `985d9280-9b10-500f-828f-b47ce50679df` | `f3e50c70-425e-58ad-981b-bdbbb4ca2bac` | `ae68972c-175a-5e68-86fb-f69fa30e2054`, `0a7896e7-fc8a-55b2-a368-978bda235b31`, `7067553d-cad9-5d79-b6b2-912e35051530` | Eleatic power route; not existence by definition. |
| [CONTINGENT-NODE-INHABITS](../../corpus/results/CONTINGENT-NODE-INHABITS.json) | `56f68b40-9737-59a0-8cac-5610980a1547` | `32c7d630-cc81-5cb0-9261-9181a213a9ae` | `207805c8-fc0b-53e9-bcc5-611e0b9bbe5f` | `c94b5446-e7e7-5b36-9bed-288959725526` | Declared transcription. Assembly strength registration: contingency supplies population, not converse. |
| [CONTINGENT-NODE-CONTROLS](../../corpus/results/CONTINGENT-NODE-CONTROLS.json) | `6c5e503c-7727-5765-ae55-e0029d81699b` | `dfc7b8e2-c7fd-5511-bba1-f8ec297414f1` | `3e1d8dfa-b732-5e4b-84ee-374fafe05f66` | none | Nonvacuity and omission controls; grounding principle vacuous under concrete necessitarianism. |
| [MODAL-POSSIBILITY-TRANSFER](../../corpus/results/MODAL-POSSIBILITY-TRANSFER.json) | `83f5fb38-7357-51dd-82ee-f167aac59758` | `ae3ef3a7-6bbe-5933-aedf-566b8532df0b` | `5aff626e-02c5-503d-b654-04d282304927` | none | All-predicate diamond transfer exactly access inclusion; no metaphysical conceivability transfer. |
| [NO-COLLAPSE-K](../../corpus/results/NO-COLLAPSE-K.json) | `185ce448-0297-51f9-95f6-e272dba93156` | `65880bb6-09f6-5fc2-8852-9bffc9c1a435` | `567be3f9-2c5e-5636-8b7b-72f23518ea9f` | `c94b5446-e7e7-5b36-9bed-288959725526` | Contingency excludes actual full collapse. |
| [NO-NEC-COLLAPSE-T](../../corpus/results/NO-NEC-COLLAPSE-T.json) | `5089057e-c590-5e04-b3e5-150c472a1266` | `eb868f3a-66d2-53ee-bd4b-47f7e7a33ac4` | `278b1ba0-6ed5-5a8a-b533-a1d15f7fd916` | `cb456382-efd6-554b-8ee4-c8fc193f876a`, `c94b5446-e7e7-5b36-9bed-288959725526` | T and contingency exclude necessary collapse; step-frame omission. |
| [NO-POSS-COLLAPSE-KTB](../../corpus/results/NO-POSS-COLLAPSE-KTB.json) | `a03ed3eb-ada4-5a66-a488-c5a1b7b37950` | `f054d090-5a08-5a16-ac01-e630085bef1a` | `e17f2e2c-7e0c-5fe7-b1fc-d608cdd5ba26` | `98bede5a-c5ff-5c26-9af0-10d526d422e2`, `c94b5446-e7e7-5b36-9bed-288959725526` | B and contingency exclude possible collapse. |
| [NO-POSS-COLLAPSE-S5](../../corpus/results/NO-POSS-COLLAPSE-S5.json) | `a03ed3eb-ada4-5a66-a488-c5a1b7b37950` | `3afa8ec7-acb3-5414-af52-bdbad5caa26a` | `f9d317dc-d660-5cbd-a4c3-2efb20a70428` | `cb456382-efd6-554b-8ee4-c8fc193f876a`, `6f474aba-fda0-57fa-8330-6246de589f63`, `c94b5446-e7e7-5b36-9bed-288959725526` | T+5 route to same conclusion; not proof of contingency. |
| [NO-NECESSARY-ACT-YIELDS-ALL](../../corpus/results/NO-NECESSARY-ACT-YIELDS-ALL.json) | `602246df-ec76-55f5-b9af-b285d02ab96f` | `bbbbdfc6-e8a7-593c-b4a7-5b151b219668` | `4fa5cf30-d40c-5550-9a48-de01e75770ed` | `c94b5446-e7e7-5b36-9bed-288959725526` | Contingent effect excludes necessary strict act yielding all concreta; not every necessary source. |
| [NOT-ALL-NECESSARY-FROM-CONTINGENT](../../corpus/results/NOT-ALL-NECESSARY-FROM-CONTINGENT.json) | `9aeab54e-372d-5cb0-9993-3f61dfd92584` | `e1d0d14b-1d3f-5e06-8968-e33b9a1dba8c` | `672ba45d-8e16-5b58-986b-f0522e640915` | `c94b5446-e7e7-5b36-9bed-288959725526` | Same concrete witness excludes concrete necessitarianism. |
| [SIMPLICITY-COLLAPSE-CORE](../../corpus/results/SIMPLICITY-COLLAPSE-CORE.json) | `069506dc-ddac-5ff3-a7e8-3a44be023e43` | `8bd1f7cb-33af-561a-b21f-28f216556e1f` | `6ef579ca-3680-5450-bca2-ffa243b36cb1` | none | Necessary strict act token excludes contingent output; necessary bearer alone insufficient. |
| [MODAL-FORK-T](../../corpus/results/MODAL-FORK-T.json) | `bed94ec2-ebd9-59e0-8c68-2d5eee6009e3` | `03a8322c-8315-5859-9bbe-3a8c85ae3fab` | `0be37d73-c1f3-5936-8f11-96d34b75c0df` | `8239eddf-aadf-5ad7-9243-e7698c7e8d27`, `cdf897a8-5490-561a-b9d2-507486a3f192`, `cb456382-efd6-554b-8ee4-c8fc193f876a`, `0aa36cd6-29b1-5d3e-bf2e-e92a737cc58c` | Uses universal correspondence but needs root, actual T validity and reading. |
| [MODAL-HIJK-CONVERGENCE-CERTIFICATE](../../corpus/results/MODAL-HIJK-CONVERGENCE-CERTIFICATE.json) | `c3afabb3-3442-5b29-83bf-7114354b345a` | `866251cb-15ea-55ec-824c-0cb2e3116d7c` | `87a2fc46-e23b-5c41-8002-5d3d64a8cac3` | none | Declared transcription. Assembly of frame correspondences, approved Mathlib axioms including choice. |
| [MODAL-TERTIA-VIA-CONVERGENCE](../../corpus/results/MODAL-TERTIA-VIA-CONVERGENCE.json) | `26ea1f1e-bd79-5d83-8638-2d14048eea4a` | `9f7e31d8-5e0e-518d-b080-187cfdc67576` | `1a11625a-d538-5bf1-b88f-685285a668ad` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410`, `2b20b5af-d653-56ba-8001-35903fb3d1ea`, `0436de86-6579-53f2-9ff5-2111ba44ebae`, `d9fad785-40ab-555a-a1c1-5e39c9d50497`, `3c468121-b8fe-5342-a1ab-d35009e5fdd4` | Conditional identity with any maximum; no existence of either. |
| [a4c8b0ce-c6cd-4e0a-858c-fad90e6e0d72](../../corpus/results/a4c8b0ce-c6cd-4e0a-858c-fad90e6e0d72.json) | `43f09b83-776d-57b8-a5b3-b84715e48fc2` | `351b9698-90ce-4a81-864f-647dddae767b` | `a4c8b0ce-c6cd-4e0a-858c-fad90e6e0d72` | `43253cd8-62be-4528-85e4-54806bd3fac0` | Declared transcription. Instantiation to selected existence extension; not concrete or necessary population. |
| [empty-history-causal-availability](../../corpus/results/empty-history-causal-availability.json) | `c778a6ca-e756-56ac-aa68-c81e9883ca7c` | `c34db0b0-141a-5b87-86cb-59528aa0af99` | `e9b7ecc7-c668-54c2-a82d-62e804c75af5` | `ee4ab504-c8fe-59bc-bc96-7cbeefed6410`, `62b4a40a-919e-5da4-998c-131c386b7361`, `2b20b5af-d653-56ba-8001-35903fb3d1ea`, `655599be-0184-5e92-b935-93443cad28a6`, `8e8c261c-37cf-57ef-9386-530e76370430`, `5a12e877-ef76-5763-b149-1fe063f8384e` | Necessary witness via coverage world or caused negative fact; all six inputs, no causal role for first branch. |

Reproduce the 83-rule sample by selecting the argument IDs in the three
inventory tables from the full exported support graph, retaining exactly
the listed graph premises, and running the existing forward-closure oracle.
For the third closure scenario remove result-backed rules explicitly marked
as declared transcriptions in these tables (including assembly in checkpoint
4); use the same eight input IDs. The recorded count comparison and seed
scenarios do not assert formal closure outside the selected graph. The
actual-to-possible population candidate is **not** included as a new edge.
