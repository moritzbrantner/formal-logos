"""The binding policy of `scripts/Discover.lean` (`truth discover`) on fixtures.

A sense tag on a whole binder identifies two binders of different modules; a
tag with fixed arguments (`CausesIn _ _ esse`, key `sense|_ _ esse`) describes
only that partial application and must never identify the full relations
(Codex P1 on #1796, AGENTS.md invariant 9). The fixture modules in
`scripts/testdata/discover-binding/` import only Init; the scratch file is
assembled as `truth discover` assembles it (`scratch_text` in
`truth/src/discover.rs`), with the transcription probe stubbed because no
target here reaches it as a finding.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "Discover.lean"
FIXTURES = ROOT / "scripts" / "testdata" / "discover-binding"
DUPER = ROOT / ".lake" / "packages" / "Duper" / ".lake" / "build" / "lib" / "lean" / "Duper.olean"
MODULES = ["DiscoverFixtureTarget", "DiscoverFixturePremise"]
TARGET = "TruthCore.DiscoverFixtureTarget.Target"
PREMISE = "TruthCore.DiscoverFixturePremise.Premise"


def skip_reason() -> str | None:
    if os.environ.get("TRUTH_CORE_LEAN_TESTS") == "false":
        return "Lean integration tests are outside this metadata-only CI job"
    if not shutil.which("lake"):
        return "needs the Lean toolchain (lake)"
    if not DUPER.is_file() and not os.environ.get("CI"):
        return "needs Duper built (`lake build Duper`)"
    return None


def lean_string(text: str) -> str:
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def tags(relation_key: str) -> list[list[str]]:
    rows = []
    for decl, relation in ((TARGET, "CausesIn"), (PREMISE, "Causes")):
        rows += [[decl, "B", "carrier"], [decl, "a", "element"], [decl, relation, relation_key]]
    return rows


def scratch(commands: list[str]) -> str:
    body = "\n".join(line for line in TOOL.read_text().splitlines() if not line.startswith("import "))
    imports = ["Duper", "Lean"] + [f"TruthCore.{m}" for m in MODULES]
    return (
        "".join(f"import {m}\n" for m in imports)
        + '\nmacro "prove_sweep_probe" : tactic => `(tactic| fail "stub")\n\n'
        + body
        + "\nset_option maxHeartbeats 0\n\n"
        + "\n".join(commands)
        + "\n"
    )


def run(commands: list[str]) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        module_dir = Path(tmp) / "TruthCore"
        module_dir.mkdir()
        compile_steps = []
        for module in MODULES:
            shutil.copy(FIXTURES / f"{module}.lean", module_dir / f"{module}.lean")
            compile_steps.append(
                f'lean --root="$1" -o "$1/TruthCore/{module}.olean" "$1/TruthCore/{module}.lean"'
            )
        path = Path(tmp) / "Scratch.lean"
        path.write_text(scratch(commands))
        script = " && ".join(compile_steps) + ' && LEAN_PATH="$1:$LEAN_PATH" lean "$2"'
        completed = subprocess.run(
            ["lake", "env", "sh", "-c", script, "sh", tmp, str(path)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
    if completed.returncode != 0:
        raise AssertionError(completed.stderr or completed.stdout)
    outcomes: dict = {}
    for line in completed.stdout.splitlines():
        if "DISCOVER-JSON " in line:
            value = json.loads(line.split("DISCOVER-JSON ", 1)[1])
            outcomes[value["label"]] = value
    return outcomes


@unittest.skipIf(skip_reason() is not None, skip_reason() or "")
class DiscoverBindingTest(unittest.TestCase):
    def test_partial_application_tags_never_identify_whole_binders(self):
        commands = [
            f'#discover "{label}" 20000 "" {lean_string(json.dumps({"tags": tags(key)}))} '
            f"{TARGET} from {PREMISE}"
            for label, key in (("whole", "cause"), ("partial", "cause|_ _ 0"))
        ]
        outcomes = run(commands)

        def froms(label: str) -> list[str]:
            return sorted(b["from"] for b in outcomes[label]["binders"])

        # A whole-binder tag identifies the two relations: one shared binder, so
        # the premise proves the target.
        self.assertEqual(froms("whole"), [f"{TARGET}.B", f"{TARGET}.CausesIn", f"{TARGET}.a"])
        self.assertIsNotNone(outcomes["whole"]["closed"])
        # The same tag only at `_ _ 0` leaves both full relations separate
        # binders: nothing equates them at respect `1`, which the goal needs,
        # so it is not found.
        self.assertEqual(
            froms("partial"),
            [f"{PREMISE}.Causes", f"{TARGET}.B", f"{TARGET}.CausesIn", f"{TARGET}.a"],
        )
        self.assertIsNone(outcomes["partial"]["closed"])
        self.assertEqual(outcomes["partial"]["domain_identified_by_name"], [])

    def test_premise_free_check_ignores_premise_only_binders(self):
        target = "TruthCore.DiscoverFixtureTarget.Inhabited'"
        premise = "TruthCore.DiscoverFixturePremise.HasElement"
        config = lean_string(json.dumps({"tags": [[premise, "B", "carrier"], [target, "B", "carrier"]]}))
        outcome = run([f'#discover "nonempty" 20000 "" {config} {target} from {premise}'])["nonempty"]
        # `x : B` comes only from the premise: the target is no theorem of its
        # vocabulary, though the goal with the premise (which binds `x`) closes.
        self.assertIsNone(outcome["alone"])
        self.assertIsNotNone(outcome["closed"])

    def test_contradiction_uses_the_premises_own_binders(self):
        target = "TruthCore.DiscoverFixtureTarget.HoldsAt"
        premise = "TruthCore.DiscoverFixturePremise.EverywhereBoth"
        rows = [[d, b, b] for d in (target, premise) for b in ("B", "R")]
        config = lean_string(json.dumps({"tags": rows}))
        outcome = run([f'#discover "incompatible" 20000 "" {config} {target} from {premise}'])["incompatible"]
        # The premise is refuted only with the target's `x : B`; over an empty
        # `B` it holds, so it is no incompatibility (the derivation still closes).
        self.assertIsNotNone(outcome["closed"])
        self.assertIsNone(outcome["vacuous"])

    def test_bridges_never_borrow_an_unused_candidates_element(self):
        allp = "TruthCore.DiscoverFixturePremise.AllP"
        marker = "TruthCore.DiscoverFixturePremise.Marker"
        some_q = "TruthCore.DiscoverFixtureTarget.SomeQ"
        some_q_at = "TruthCore.DiscoverFixtureTarget.SomeQAt"
        rows = [[d, "B", "carrier"] for d in (allp, marker, some_q, some_q_at)]
        config = lean_string(json.dumps({"tags": rows, "bridges": True}))
        outcomes = run([
            f'#discover "borrowed" 20000 "" {config} {some_q} from {allp} {marker}',
            f'#discover "own" 20000 "" {config} {some_q_at} from {allp}',
        ])
        # `∀ y, P y → Q y` with `∀ y, P y` proves `∃ y, Q y` only given an
        # element; the one `Marker` introduces is not the report's (Marker is
        # unused), so over an empty `B` the reported bridge would fail.
        self.assertIsNone(outcomes["borrowed"]["closed"])
        self.assertEqual(outcomes["borrowed"]["bridges"], [])
        # Control: with the target's own `x : B` the same bridge is reported.
        own = outcomes["own"]["bridges"]
        self.assertTrue(own, outcomes["own"])
        self.assertEqual((own[0]["from"], own[0]["to"]), (f"{allp}.P", f"{some_q_at}.Q"))
        self.assertEqual(own[0]["used"], [0])
        self.assertEqual(own[0]["assumed_binders"], [])

    def test_models_rest_only_on_allowed_axioms(self):
        target = "TruthCore.DiscoverFixtureTarget.NeedsHard"
        premise = "TruthCore.DiscoverFixtureTarget.GivesHard"
        outcome = run([f'#discover "axiom" 20000 "" "{{}}" {target} from {premise}'])["axiom"]
        # The derivation closes without the axiom (the premise gives `Hard`), but
        # every one-point model needs `Hard`, which only `simp` with the
        # disallowed axiom `hard_holds` closes: no model is reported.
        self.assertIsNotNone(outcome["closed"])
        self.assertLessEqual(set(outcome["proof"]["axioms"]), {"propext", "Classical.choice", "Quot.sound"})
        self.assertIsNone(outcome["witness"])

    def test_name_identification_survives_dropping_its_origin(self):
        marker = "TruthCore.DiscoverFixturePremise.DomMarker"
        rule = "TruthCore.DiscoverFixturePremise.DomRule"
        goal = "TruthCore.DiscoverFixtureTarget.DomGoal"
        witness = "TruthCore.DiscoverFixtureTarget.DomWitness"
        rows = [[goal, "Q", "q"], [rule, "Q", "q"], [rule, "P", "p"], [witness, "P", "p"]]
        config = lean_string(json.dumps({"tags": rows}))
        outcome = run([f'#discover "alias" 20000 "" {config} {goal} from {marker} {rule} {witness}'])["alias"]
        # `DomMarker` introduces `C`; `DomRule` (same module) shares it by the
        # module convention, `DomWitness` (other module) by name only. Dropping
        # the unused `DomMarker` leaves the two retained premises sharing `C`
        # across modules by name alone: the flag must stay.
        self.assertIsNotNone(outcome["closed"])
        self.assertEqual(outcome["minimal"], [1, 2])
        self.assertEqual(outcome["domain_identified_by_name"], [f"{witness}.C = {rule}.C"])

    def test_bridge_domains_include_the_declarations_of_bridge_only_binders(self):
        target = "TruthCore.DiscoverFixtureTarget.BTarget"
        every = "TruthCore.DiscoverFixtureTarget.BAll"
        mark = "TruthCore.DiscoverFixturePremise.BMark"
        config = lean_string(json.dumps({"tags": [[every, "P", "p"], [mark, "P", "p"]], "bridges": True}))
        outcome = run([f'#discover "fixed" 20000 "" {config} {target} from {every} {mark}'])["fixed"]
        # The fixed bridge `∀ d, P x d → Q x d` uses `BMark`'s element `x`, which
        # neither the used premise nor the target mentions: it is an assumed
        # binder, and `BMark`'s carrier `B` joined the target's by name only, so
        # the bridge carries that identification although `BMark` is unused.
        fixed = [b for b in outcome["bridges"] if b["fixed"] == ["x"]]
        self.assertTrue(fixed, outcome)
        self.assertEqual(fixed[0]["assumed_binders"], ["x"])
        self.assertIn(f"{mark}.B = {target}.B", fixed[0]["domain_identified_by_name"])

    def test_literal_negation_cores_are_marked_and_genuine_ones_are_not(self):
        target = "TruthCore.DiscoverFixtureTarget.Unrelated"
        lit_p = "TruthCore.DiscoverFixturePremise.LitP"
        lit_not_p = "TruthCore.DiscoverFixturePremise.LitNotP"
        gen_some = "TruthCore.DiscoverFixturePremise.GenSome"
        outcomes = run([
            f'#discover "literal" 20000 "" "{{}}" {target} from {lit_p} {lit_not_p}',
            f'#discover "genuine" 20000 "" "{{}}" {target} from {lit_p} {gen_some}',
        ])
        # `LitNotP C S := ¬ LitP C S`: the core is P and its literal negation
        # (#1819); `truth discover` filters it as `literal_negation`.
        literal = outcomes["literal"]
        self.assertIsNotNone(literal["vacuous"])
        self.assertEqual(sorted(literal["vacuous_core"]), [0, 1])
        self.assertEqual(literal["literal_negation"], [0, 1])
        # Negative control: `∃ y, ¬ S y` contradicts `∀ y, S y` but is not its
        # definitional negation, so the incompatibility stays reported.
        genuine = outcomes["genuine"]
        self.assertIsNotNone(genuine["vacuous"])
        self.assertEqual(sorted(genuine["vacuous_core"]), [0, 1])
        self.assertIsNone(genuine["literal_negation"])

    def test_conjunctive_antecedents_get_one_conjunctive_bridge(self):
        conj = "TruthCore.DiscoverFixtureTarget.ConjGoal"
        single = "TruthCore.DiscoverFixtureTarget.SingleGoal"
        rule = "TruthCore.DiscoverFixturePremise.ConjRule"
        rows = [[d, b, b] for d in (conj, single, rule) for b in ("B", "Q")]
        config = lean_string(json.dumps({"tags": rows, "bridges": True}))
        outcomes = run([
            f'#discover "conj" 20000 "" {config} {conj} from {rule}',
            f'#discover "single" 20000 "" {config} {single} from {rule}',
        ])
        bridges = outcomes["conj"]["bridges"]
        # No bridge makes one conjunct (`A1` or `A2`) sufficient for `R`.
        singles = [b for b in bridges if b["from"] in (f"{conj}.A1", f"{conj}.A2") and b["to"] == f"{rule}.R"]
        self.assertEqual(singles, [], bridges)
        # The conjunctive version is reported once instead.
        conjunctive = [b for b in bridges if b.get("conjunctive")]
        self.assertEqual(len(conjunctive), 1, bridges)
        self.assertEqual(conjunctive[0]["from"], f"{conj}.A1 ∧ {conj}.A2")
        self.assertEqual(conjunctive[0]["to"], f"{rule}.R")
        self.assertEqual(conjunctive[0]["replaces_single_conjuncts"], [f"{conj}.A1", f"{conj}.A2"])
        # Control: a single antecedent keeps its ordinary bridge `A1 → R`.
        plain = outcomes["single"]["bridges"]
        self.assertTrue(any(b["from"] == f"{single}.A1" and b["to"] == f"{rule}.R" for b in plain), plain)
        self.assertFalse(any(b.get("conjunctive") for b in plain), plain)

    def test_projection_binding_is_an_explicit_reported_choice(self):
        target = "TruthCore.DiscoverFixtureTarget.ProjTarget"
        premise = "TruthCore.DiscoverFixtureTarget.ProjPremise"
        wrong = "TruthCore.DiscoverFixtureTarget.ProjWrong"
        outcomes = run([
            f'#discover "projection" 20000 "" "{{}}" {target} from {premise}',
            f'#discover "useless" 20000 "" "{{}}" {target} from {wrong}',
        ])
        # Over separate `x : B` and `b : Box B` the goal is false; binding `x`
        # to `b.val` closes it, and the choice is reported, not silent.
        found = outcomes["projection"]
        self.assertIsNotNone(found["closed"])
        self.assertEqual(found["projection"]["binder"], f"{target}.x")
        self.assertEqual(found["projection"]["bound_to"], f"{premise}.b.val")
        bound = [b for b in found["binders"] if b.get("bound_to")]
        self.assertEqual([(b["from"], b["bound_to"]) for b in bound], [(f"{target}.x", f"{premise}.b.val")])
        self.assertIn("val", found["signature"])
        self.assertNotIn("(x :", found["signature"])
        # A choice that does not close the goal is listed as tried; the goal
        # stays unresolved.
        useless = outcomes["useless"]
        self.assertIsNone(useless["closed"])
        self.assertEqual([c["bound_to"] for c in useless["projections_tried"]], [f"{wrong}.b.val"])


if __name__ == "__main__":
    unittest.main()
