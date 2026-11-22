"""Offline tests for `scripts/discover_blueprint.py` (#1832) on a synthetic corpus."""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import tempfile
import time
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


STUB = """#!/usr/bin/env bash
# Stub runner: records what the oracle's worktree holds, then acts per MODE.
cat corpus/disambiguations/*.json > "$SEEN"
cat notes.txt >> "$SEEN" 2>/dev/null || true
pwd >> "$SEEN"
case "$MODE" in
  fail) exit 3 ;;
  sleep) touch "$SEEN.started"; sleep 60 ;;
esac
mkdir -p "$TRUTH_DISCOVER_REPORT_DIR/run1"
"""


class OracleTests(unittest.TestCase):
    """The oracle never touches the repository's corpus and always removes its
    temporary worktree."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.root = base / "repo"
        self.scratch = base / "scratch"
        self.scratch.mkdir()
        (self.root / "scripts").mkdir(parents=True)
        (self.root / "scripts" / "run-discovery.sh").write_text(STUB)
        write(self.root / "corpus" / "disambiguations" / "d.json",
              {"id": "d", "senses": [{"id": "s1", "label": "IN_ACT_4",
                                      "lean_parameters": [{"declaration": "A", "parameter": "x"}]}]})
        for argv in (["init", "-q"], ["add", "-A"],
                     ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "fixture"]):
            subprocess.run(["git", "-C", str(self.root), *argv], check=True)
        # An uncommitted change the worktree must carry.
        (self.root / "notes.txt").write_text("uncommitted-marker\n")
        self.before = self.snapshot()
        self.seen = base / "seen.txt"
        self.overlay = base / "overlay.json"
        write(self.overlay, [{"sense": "IN_ACT_4", "declaration": "B", "parameter": "y"},
                             {"sense": "TEMP_RESPECT", "declaration": "B", "parameter": "R"}])
        self.env = {"PATH": os.environ["PATH"], "SEEN": str(self.seen),
                    "TRUTH_DISCOVER_REPORT_DIR": str(base / "reports")}

    def snapshot(self) -> dict[str, bytes]:
        return {str(p.relative_to(self.root)): p.read_bytes()
                for p in sorted(self.root.rglob("*")) if p.is_file() and ".git" not in p.parts}

    def command(self, overlay: Path | None = None) -> list[str]:
        return [sys.executable, str(TOOL), "--root", str(self.root), "oracle",
                str(overlay or self.overlay), "--scratch", str(self.scratch), "--"]

    def assert_clean(self):
        self.assertEqual(self.snapshot(), self.before)
        self.assertEqual(list(self.scratch.iterdir()), [])
        listing = subprocess.run(["git", "-C", str(self.root), "worktree", "list", "--porcelain"],
                                 check=True, capture_output=True, text=True).stdout
        self.assertEqual(listing.count("worktree "), 1)

    def test_overlay_is_applied_only_in_the_worktree(self):
        subprocess.run(self.command(), check=True, env={**self.env, "MODE": "ok"})
        seen = self.seen.read_text()
        self.assertIn('"parameter": "y"', seen)
        self.assertIn("TEMP_RESPECT", seen)
        self.assertIn("uncommitted-marker", seen)
        self.assertNotIn(str(self.root) + "\n", seen)  # ran elsewhere
        self.assertTrue((Path(self.env["TRUTH_DISCOVER_REPORT_DIR"]) / "run1" / "overlay.json").is_file())
        self.assert_clean()

    def test_failing_runner(self):
        done = subprocess.run(self.command(), env={**self.env, "MODE": "fail"})
        self.assertEqual(done.returncode, 3)
        self.assert_clean()

    def test_unknown_sense(self):
        bad = self.overlay.with_name("bad.json")
        write(bad, [{"sense": "NO_SUCH_SENSE", "declaration": "B", "parameter": "y"}])
        done = subprocess.run(self.command(bad), env={**self.env, "MODE": "ok"},
                              capture_output=True, text=True)
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("unknown sense", done.stderr)
        self.assertFalse(self.seen.exists())
        self.assert_clean()

    def test_sigterm_while_runner_sleeps(self):
        proc = subprocess.Popen(self.command(), env={**self.env, "MODE": "sleep"})
        started = Path(str(self.seen) + ".started")
        for _ in range(200):
            if started.exists():
                break
            time.sleep(0.05)
        self.assertTrue(started.exists())
        proc.send_signal(signal.SIGTERM)
        self.assertNotEqual(proc.wait(timeout=30), 0)
        self.assert_clean()


if __name__ == "__main__":
    unittest.main()
