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

structure Inner (A : Type) where
  relation : A → Prop
  flag : A → Bool

structure Outer (A : Type) where
  left : Inner A
  right : Inner A

theorem nestedFields {A : Type} (p : Outer A) (x : A)
    (h : p.left.relation x ∧ p.right.flag x) :
    p.right.flag x ≠ false ∧ p.left.relation x := ⟨by simpa [h.2], h.1⟩

structure UnsupportedField (A : Type) where
  relation : A → Prop
  step : A → A

theorem unsupportedField {A : Type} (p : UnsupportedField A) (x : A)
    (h : p.relation x) : p.relation x := h

class Vocabulary (A : Type) where
  relation : A → Prop

theorem classParameter {A : Type} [p : Vocabulary A] (x : A)
    (h : p.relation x) : p.relation x := h

end CountermodelFixture

run_meta do
  for name in #[``CountermodelFixture.explicitNested,
      ``CountermodelFixture.implicitInput, ``CountermodelFixture.binaryInput,
      ``CountermodelFixture.functionEquality, ``CountermodelFixture.sharedFrame,
      ``CountermodelFixture.nestedFields, ``CountermodelFixture.unsupportedField,
      ``CountermodelFixture.classParameter] do
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

    def test_structure_cannot_introduce_a_carrier(self):
        self.assertIn("unsupported structure field frame.Carrier",
                      self.reports["sharedFrame"]["error"])

    def test_nested_relations_have_distinct_field_tables(self):
        report = self.reports["nestedFields"]
        self.assertNotIn("error", report)
        names = [f"«countermodel field {i}»" for i in range(4)]
        self.assertEqual(report["predicates"], [{"name": name, "args": ["A"]} for name in names])
        body = report["premises"][0]["formula"]
        self.assertEqual(body["a"]["p"], names[0])
        self.assertEqual(body["b"]["a"]["p"], names[3])
        self.assertEqual(report["conclusion"]["formula"]["a"]["a"]["a"]["p"], names[3])
        structure, = report["structures"]
        self.assertEqual(structure["lean_type"], "CountermodelFixture.Outer A")
        self.assertIn("@CountermodelFixture.Inner.mk A", structure["lean_value"])
        self.assertIn(f"decide ({names[3]} x0)", structure["lean_value"])

    def test_unsupported_field_reports_its_path(self):
        self.assertIn("unsupported structure field p.step",
                      self.reports["unsupportedField"]["error"])

    def test_typeclass_parameter_stays_unsupported(self):
        self.assertIn("unsupported parameter p", self.reports["classParameter"]["error"])


if __name__ == "__main__":
    unittest.main()
