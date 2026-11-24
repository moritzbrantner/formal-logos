"""The actual countermodel extractor on small declarations in its Lean environment.

No corpus modules or alternative extractor are needed: append the declarations
and probes to Countermodel.lean, then inspect Countermodel.run's JSON output.
The existing CI Python suite discovers this file; metadata-only jobs skip Lean.
"""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from lean_test_support import requires_built

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "Countermodel.lean"
PREFIX = "COUNTERMODEL-JSON "
NS = "CountermodelFixture."
FIXTURE = r"""
namespace CountermodelFixture

theorem explicitNested {A B : Type} (f : A → B) (g : B → A) (P : A → Prop)
    (h : ∃ x : A, P (g (f x))) : ∃ x : A, P (g (f x)) := h

theorem implicitInput {A B : Type} (f : {a : A} → B) (P : B → Prop)
    (h : ∃ x : A, P (@f x)) : ∃ x : A, P (@f x) := h

theorem binaryInput {A : Type} (f : A → A → A) (P : A → Prop)
    (h : ∃ x : A, P (f x x)) : ∃ x : A, P (f x x) := h

theorem functionEquality {A : Type} (f g : A → A) (h : f = g) : f = g := h

structure Frame where
  Carrier : Type
  relation : Carrier → Carrier → Prop

theorem sharedFrame (frame : Frame) (h : ∃ x, frame.relation x x) :
    ∃ x, frame.relation x x := h

/-- A parameterized frame: a relation, an element, a unary function and a
field outside the fragment. -/
structure Fr (W : Type) where
  acc : W → W → Prop
  pt : W
  step : W → W
  extra : List W

/-- A profile nesting the frame, as `CausalityFrame` nests `History`. -/
structure Prof (W : Type) where
  fr : Fr W
  mark : W → Prop

theorem nestedFrame {W : Type} (m : Prof W) (h : ∀ x, m.fr.acc x (m.fr.step x))
    (hMark : m.mark m.fr.pt) : m.mark m.fr.pt ∧ ∃ y, m.fr.acc m.fr.pt y :=
  ⟨hMark, _, h m.fr.pt⟩

theorem mentionsOpaque {W : Type} (F : Fr W) (h : F.extra = []) : F.extra = [] := h

structure Refl (W : Type) where
  acc : W → W → Prop
  refl : ∀ x, acc x x

theorem proofField {W : Type} (F : Refl W) (w : W) (h : F.acc w w) : F.acc w w := h

/-- A structure built by a definition (a frame adapter): its projections
reduce to the definition's arguments. -/
def adapt {W : Type} (acc : W → W → Prop) (pt : W) : Fr W := ⟨acc, pt, id, []⟩

theorem throughAdapter {W : Type} (acc : W → W → Prop) (pt : W)
    (h : (adapt acc pt).acc pt pt) : acc pt (adapt acc pt).pt := h

end CountermodelFixture

run_meta do
  for name in #[``CountermodelFixture.explicitNested,
      ``CountermodelFixture.implicitInput, ``CountermodelFixture.binaryInput,
      ``CountermodelFixture.functionEquality, ``CountermodelFixture.sharedFrame,
      ``CountermodelFixture.nestedFrame, ``CountermodelFixture.mentionsOpaque,
      ``CountermodelFixture.proofField, ``CountermodelFixture.throughAdapter] do
    let result ← try Countermodel.run name
      catch e => pure (Json.mkObj [("theorem", Json.str name.toString),
        ("error", Json.str (← e.toMessageData.toString))])
    logInfo m!"COUNTERMODEL-JSON {result.compress}"
"""


@requires_built()
@unittest.skipUnless(shutil.which("lake") or (Path.home() / ".elan/bin/lake").exists(),
                     "Lean integration requires lake")
class CountermodelExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "CountermodelFixture.lean"
            path.write_text(TOOL.read_text() + "\n" + FIXTURE)
            completed = subprocess.run(
                [sys.executable, "scripts/worker_env.py", "--", "lake", "env", "lean", str(path)],
                cwd=ROOT, capture_output=True, text=True, timeout=120,
            )
        if completed.returncode != 0:
            raise AssertionError(completed.stdout + completed.stderr)
        cls.reports = {}
        for line in completed.stdout.splitlines():
            if PREFIX in line:
                report = json.loads(line.split(PREFIX, 1)[1])
                cls.reports[report["theorem"].removeprefix(NS)] = report

    def test_explicit_nested_functions_preserve_carrier_and_function_identity(self):
        report = self.reports["explicitNested"]
        self.assertNotIn("error", report)
        self.assertEqual(report["carriers"], ["A", "B"])
        self.assertEqual(report["functions"], [
            {"name": "f", "domain": "A", "codomain": "B"},
            {"name": "g", "domain": "B", "codomain": "A"},
        ])
        self.assertEqual(report["predicates"], [{"name": "P", "args": ["A"]}])
        self.assertEqual([p["name"] for p in report["premises"]], ["h"])
        for formula in (report["premises"][0]["formula"], report["conclusion"]["formula"]):
            self.assertEqual((formula["t"], formula["sort"]), ("exists", "A"))
            self.assertEqual(formula["body"], {
                "t": "atom", "p": "P",
                "args": [{"app": "g", "arg": {"app": "f", "arg": {"v": formula["v"]}}}],
            })

    def test_implicit_function_input_is_explicitly_unsupported(self):
        self.assertIn("unsupported parameter f", self.reports["implicitInput"]["error"])

    def test_binary_function_input_stays_unsupported(self):
        self.assertIn("unsupported parameter f", self.reports["binaryInput"]["error"])

    def test_function_equality_stays_unsupported(self):
        self.assertIn("unsupported formula", self.reports["functionEquality"]["error"])

    def test_a_structure_bundled_carrier_is_a_precise_field_refusal(self):
        # A carrier inside the structure (a dependent field) stays outside the
        # fragment; the refusal names the field, not the whole structure.
        self.assertIn("unsupported field frame.Carrier : Type", self.reports["sharedFrame"]["error"])

    def test_structure_fields_become_typed_tables_and_a_constructor(self):
        report = self.reports["nestedFrame"]
        self.assertNotIn("error", report)
        self.assertEqual(report["carriers"], ["W"])
        self.assertEqual(
            [(p["name"], p["args"], p["field"]) for p in report["predicates"]],
            [("m_fr_acc", ["W", "W"], "m.fr.acc"), ("m_mark", ["W"], "m.mark")])
        self.assertEqual(report["constants"], [{"name": "m_fr_pt", "sort": "W", "field": "m.fr.pt"}])
        self.assertEqual(report["functions"],
                         [{"name": "m_fr_step", "domain": "W", "codomain": "W", "field": "m.fr.step"}])
        # Inner structures first; the opaque field is built as `default`.
        self.assertEqual([s["name"] for s in report["structures"]], ["m_fr", "m"])
        self.assertEqual(report["structures"][0]["fields"], ["m_fr_acc", "m_fr_pt", "m_fr_step", None])
        self.assertEqual(report["structures"][1]["fields"], ["m_fr", "m_mark"])
        self.assertEqual(report["opaque_fields"], [{"field": "m.fr.extra", "type": "List W"}])
        h = report["premises"][0]["formula"]
        self.assertEqual(h["body"], {"t": "atom", "p": "m_fr_acc", "args": [
            {"v": h["v"]}, {"app": "m_fr_step", "arg": {"v": h["v"]}}]})

    def test_a_mentioned_field_outside_the_fragment_is_named(self):
        self.assertIn("unsupported field F.extra : List W", self.reports["mentionsOpaque"]["error"])

    def test_a_proof_field_is_a_precise_refusal(self):
        self.assertIn("unsupported field F.refl", self.reports["proofField"]["error"])
        self.assertIn("proof field", self.reports["proofField"]["error"])

    def test_projections_of_an_adapter_reduce_to_its_arguments(self):
        report = self.reports["throughAdapter"]
        self.assertNotIn("error", report)
        self.assertEqual(report["structures"], [])
        self.assertIn("CountermodelFixture.adapt", report["unfolded"])
        self.assertEqual(report["conclusion"]["formula"],
                         {"t": "atom", "p": "acc", "args": [{"v": "pt"}, {"v": "pt"}]})


if __name__ == "__main__":
    unittest.main()
