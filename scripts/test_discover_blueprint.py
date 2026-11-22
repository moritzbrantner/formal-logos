"""Offline tests for `scripts/discover_blueprint.py` (#1832) on a synthetic corpus."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "discover_blueprint.py"


def write(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data))


class DiagnoseTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        c = self.root / "corpus"
        for sid, decl in (("t", "M.T"), ("p", "N.P"), ("q", "M.Q"), ("u", "M.U")):
            write(c / "statements" / f"{sid}.json", {"id": sid, "lean_declaration": decl})
        # Target t: known from p (another module, carrier B instead of Being).
        write(c / "arguments" / "a1.json", {"id": "a1", "label": "t from p",
                                            "premise_statement_ids": ["p"],
                                            "conclusion_statement_id": "t"})
        # Target u: known from q (same module, same binder names).
        write(c / "arguments" / "a2.json", {"id": "a2", "label": "u from q",
                                            "premise_statement_ids": ["q"],
                                            "conclusion_statement_id": "u"})
        # An argument with no verified result does not count.
        write(c / "arguments" / "a3.json", {"id": "a3", "label": "t from u",
                                            "premise_statement_ids": ["u"],
                                            "conclusion_statement_id": "t"})
        for rid, aid in (("r1", "a1"), ("r2", "a2")):
            write(c / "results" / f"{rid}.json", {"id": rid, "argument_id": aid})
        (c / "disambiguations").mkdir(parents=True)
        self.binders = self.root / "binders.jsonl"
        rows = [
            {"declaration": "M.T", "module": "M", "binders": [["Being", True, False], ["InAct", False, False]]},
            {"declaration": "N.P", "module": "N", "binders": [["B", True, False], ["InAct", False, False]]},
            {"declaration": "M.Q", "module": "M", "binders": [["Being", True, False], ["InAct", False, False]]},
            {"declaration": "M.U", "module": "M", "binders": [["Being", True, False], ["InAct", False, False]]},
        ]
        self.binders.write_text("".join(json.dumps(r) + "\n" for r in rows))

    def diagnose(self, findings: list[dict]) -> list[dict]:
        report = self.root / "report.json"
        write(report, {"findings": findings})
        out = subprocess.run(
            [sys.executable, str(TOOL), "--root", str(self.root), "diagnose", str(report),
             "--binders", str(self.binders), "--json"],
            check=True, capture_output=True, text=True).stdout
        return {row["target"]: row for row in json.loads(out)}

    def finding(self, target, candidates, kind="unresolved"):
        return {"target": {"statement_id": target}, "candidates": candidates, "kind": kind, "lean": None}

    def test_unidentified_cross_module_binders_are_an_identification_gap(self):
        rows = self.diagnose([self.finding("t", ["p"])])
        self.assertEqual(rows["t"]["verdict"], "identification")
        known = rows["t"]["known"]
        self.assertEqual([k["argument"] for k in known], ["a1"])  # a3 has no result
        self.assertEqual(sorted(known[0]["unidentified"]), ["N.P.B", "N.P.InAct"])

    def test_unretrieved_known_premise_is_a_retrieval_gap(self):
        rows = self.diagnose([self.finding("t", [])])
        self.assertEqual(rows["t"]["verdict"], "identification+retrieval")

    def test_unretrieved_identifiable_premise_is_only_a_retrieval_gap(self):
        rows = self.diagnose([self.finding("u", [])])
        self.assertEqual(rows["u"]["verdict"], "retrieval")

    def test_same_module_names_are_identified(self):
        rows = self.diagnose([self.finding("u", ["q"])])
        self.assertEqual(rows["u"]["verdict"], "search")
        self.assertEqual(rows["u"]["known"][0]["unidentified"], [])

    def test_sense_tags_identify_across_modules(self):
        write(self.root / "corpus" / "disambiguations" / "d.json", {"id": "d", "senses": [
            {"id": "s-being", "lean_parameters": [{"declaration": "M.T", "parameter": "Being"},
                                                  {"declaration": "N.P", "parameter": "B"}]},
            {"id": "s-act", "lean_parameters": [{"declaration": "M.T", "parameter": "InAct"},
                                                {"declaration": "N.P", "parameter": "InAct"}]}]})
        rows = self.diagnose([self.finding("t", ["p"])])
        self.assertEqual(rows["t"]["known"][0]["unidentified"], [])
        self.assertEqual(rows["t"]["verdict"], "search")

    def test_partial_application_tags_do_not_identify(self):
        write(self.root / "corpus" / "disambiguations" / "d.json", {"id": "d", "senses": [
            {"id": "s-act", "lean_parameters": [
                {"declaration": "M.T", "parameter": "InAct", "arguments": ["_", "esse"]},
                {"declaration": "N.P", "parameter": "InAct", "arguments": ["_", "esse"]}]}]})
        rows = self.diagnose([self.finding("t", ["p"])])
        self.assertIn("N.P.InAct", rows["t"]["known"][0]["unidentified"])

    def test_no_verified_argument_is_no_known(self):
        rows = self.diagnose([self.finding("q", ["p"])])
        self.assertEqual(rows["q"]["verdict"], "no-known")

    def test_closed_goal_is_found(self):
        rows = self.diagnose([self.finding("t", ["p"], kind="discovery")])
        self.assertEqual(rows["t"]["verdict"], "found")


class OracleTests(unittest.TestCase):
    def test_overlay_is_restored_after_the_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            # A stub runner that records what it saw.
            (root / "scripts" / "run-discovery.sh").write_text(
                "#!/usr/bin/env bash\ncat corpus/disambiguations/*.json > seen.txt\n"
                "mkdir -p \"$TRUTH_DISCOVER_REPORT_DIR/run1\"\n")
            original = {"id": "d", "senses": [{"id": "s1", "label": "IN_ACT_4",
                                                "lean_parameters": [{"declaration": "A", "parameter": "x"}]}]}
            write(root / "corpus" / "disambiguations" / "d.json", original)
            before = (root / "corpus" / "disambiguations" / "d.json").read_bytes()
            overlay = root / "overlay.json"
            write(overlay, [{"sense": "IN_ACT_4", "declaration": "B", "parameter": "y"},
                            {"sense": "TEMP_RESPECT", "declaration": "B", "parameter": "R"}])
            env = {"TRUTH_DISCOVER_REPORT_DIR": str(root / "reports"), "PATH": "/usr/bin:/bin"}
            subprocess.run([sys.executable, str(TOOL), "--root", str(root), "oracle", str(overlay), "--"],
                           check=True, env=env)
            seen = (root / "seen.txt").read_text()
            self.assertIn('"parameter": "y"', seen)
            self.assertIn("TEMP_RESPECT", seen)
            self.assertEqual((root / "corpus" / "disambiguations" / "d.json").read_bytes(), before)
            self.assertEqual(sorted(p.name for p in (root / "corpus" / "disambiguations").iterdir()), ["d.json"])
            self.assertTrue((root / "reports" / "run1" / "overlay.json").is_file())


if __name__ == "__main__":
    unittest.main()
