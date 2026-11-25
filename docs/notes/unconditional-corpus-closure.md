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
