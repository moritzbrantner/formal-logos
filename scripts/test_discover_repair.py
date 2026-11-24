"""Tests for the adaptive repair of `scripts/discover_blueprint.py` (#1833).

The planner, guards and trace are tested offline on a synthetic corpus with a
stub solver. `LeanRepairTests` runs the real solver path (`#discover` and the
countermodel probe of `scripts/DiscoverRepair.lean`, appended to
`scripts/Discover.lean` as `truth discover` assembles its scratch file) on the
Init-only fixture modules in `scripts/testdata/discover-repair/`; it is skipped
without the Lean toolchain and a built Duper.
"""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("discover_blueprint", ROOT / "scripts" / "discover_blueprint.py")
bp = importlib.util.module_from_spec(SPEC)
sys.modules["discover_blueprint"] = bp
SPEC.loader.exec_module(bp)

FIXTURES = ROOT / "scripts" / "testdata" / "discover-repair"
DUPER = ROOT / ".lake" / "packages" / "Duper" / ".lake" / "build" / "lib" / "lean" / "Duper.olean"
A = "TruthCore.RepairFixtureA"
B = "TruthCore.RepairFixtureB"
STATEMENTS = {
    "t": f"{A}.Target", "ptor": f"{A}.PtoR", "rtoq": f"{A}.RtoQ",
    "qher": f"{A}.QHereditary", "qev": f"{A}.QEverywhere", "qpairs": f"{A}.QAtPairs",
    "allp": f"{A}.AllP", "notallp": f"{A}.NotAllP", "chain": f"{A}.Chain",
    "chainends": f"{A}.ChainEnds", "noel": f"{B}.NoElement", "em": "TruthCore.Logic.ExcludedMiddle",
    "onticgood": f"{A}.OnticAllGood", "profilegood": f"{A}.ProfileAllGood",
}
MODULES = {decl: decl.rsplit(".", 1)[0] for decl in STATEMENTS.values()}


def write(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data))


def make_corpus(root: Path, arguments: list[tuple[str, list[str], str]]) -> bp.Corpus:
    c = root / "corpus"
    for sid, decl in STATEMENTS.items():
        write(c / "statements" / f"{sid}.json", {"id": sid, "lean_declaration": decl, "label": sid})
    for aid, premises, conclusion in arguments:
        write(c / "arguments" / f"{aid}.json", {"id": aid, "label": aid,
                                                "premise_statement_ids": premises,
                                                "conclusion_statement_id": conclusion})
        write(c / "results" / f"r-{aid}.json", {"id": f"r-{aid}", "argument_id": aid})
    (c / "disambiguations").mkdir(parents=True, exist_ok=True)
    (c / "results").mkdir(parents=True, exist_ok=True)
    return bp.Corpus(root)


def finding(target, candidates, kind="unresolved", lean=None, filters=(), premises=()):
    return {"target": {"statement_id": target, "lean_declaration": STATEMENTS[target]},
            "label": "t1", "kind": kind, "candidates": list(candidates),
            "premises": [{"statement_id": p} for p in premises],
            "filters": [{"filter": f} for f in filters],
            "lean": lean if lean is not None else {"closed": None, "bridges": []}}


OPTIONS = {"heartbeats": 100000, "candidates": 8}


class Harness:
    """Plans and executes with a given solver against one finding."""

    def __init__(self, corpus, f, trace_path, runner):
        self.corpus, self.f, self.trace = corpus, f, bp.Trace(trace_path)
        self.runner = runner

    def items(self):
        report = {"options": OPTIONS, "findings": [self.f]}
        return bp.plan_all(self.corpus, report, {}, [self.f], self.trace, "rev", "report.json")

    def item(self):
        return self.items()[0]

    def run(self, action_name):
        item = self.item()
        action = next(a for a in item["actions"] if a["action"] == action_name)
        entries = bp.execute(action, item, self.corpus, self.trace, "rev", self.runner, senses=False)
        self.trace.save()
        return entries

    def auto(self, limit=50, include_reports=True):
        """`retry --auto`: run the first admissible action until none is left."""
        runs = 0
        while runs < limit:
            item = self.item()
            chosen = next((a for a in item["actions"] if not a["refused"]
                           and (a["goals"] or include_reports)), None)
            if not chosen:
                return runs
            bp.execute(chosen, item, self.corpus, self.trace, "rev", self.runner, senses=False)
            self.trace.save()
            runs += 1
        raise AssertionError("repair loop did not terminate")


def stub(outcome):
    def runner(corpus, labelled):
        return {label: dict(outcome(goal), label=label) for label, goal in labelled}
    return runner


class PlannerTests(unittest.TestCase):
    def test_exact_bundle_is_not_a_truncated_retrieval(self):
        f = finding("t", ["ptor", "rtoq"])
        self.assertTrue(bp.signals(f, {"candidates": 2})["truncated"])
        self.assertFalse(bp.signals(f, {"premise_selection": "exact", "candidates": None})["truncated"])

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.corpus = make_corpus(self.root, [("lemma", ["qher"], "qev")])
        self.trace_path = self.root / "trace.json"

    def diag(self, item):
        return {d["code"]: d["status"] for d in item["diagnoses"]}

    def test_reusable_lemma_is_proposed_and_failure_is_not_a_refutation(self):
        h = Harness(self.corpus, finding("qev", ["qher"]), self.trace_path, None)
        # The target itself is the lemma's conclusion: a known derivation, not reuse.
        self.assertEqual([a["action"] for a in h.item()["actions"] if a["action"] == "reuse-lemma"], [])
        write(self.root / "corpus" / "statements" / "qpairs.json",
              {"id": "qpairs", "lean_declaration": STATEMENTS["qpairs"], "definition_ids": ["d"]})
        write(self.root / "corpus" / "statements" / "qev.json",
              {"id": "qev", "lean_declaration": STATEMENTS["qev"], "definition_ids": ["d"]})
        h = Harness(bp.Corpus(self.root), finding("qpairs", ["qher"]), self.trace_path, None)
        item = h.item()
        reuse = [a for a in item["actions"] if a["action"] == "reuse-lemma"]
        self.assertEqual(len(reuse), 1)
        self.assertEqual(reuse[0]["goals"][0]["premises"], ["qher", "qev"])
        self.assertEqual(self.diag(item)["a"], "possible")
        self.assertNotIn("refut", json.dumps(item["diagnoses"]).replace("not a refutation", ""))

    def test_support_cycle_is_refused(self):
        corpus = make_corpus(self.root, [("via-target", ["t"], "rtoq")])
        write(self.root / "corpus" / "statements" / "t.json",
              {"id": "t", "lean_declaration": STATEMENTS["t"], "definition_ids": ["d"]})
        write(self.root / "corpus" / "statements" / "rtoq.json",
              {"id": "rtoq", "lean_declaration": STATEMENTS["rtoq"], "definition_ids": ["d"]})
        corpus = bp.Corpus(self.root)
        self.assertTrue(corpus.only_through("rtoq", "t"))
        rows = [{"argument": "x", "premises": ["ptor", "rtoq"], "not_retrieved": ["rtoq"],
                 "unidentified": [], "binding": []}]
        actions = bp.plan(finding("t", ["ptor"]), corpus, OPTIONS, rows, bp.Trace(None), "rev")
        split = next(a for a in actions if a["action"] == "split")
        self.assertTrue(any("support cycle" in r for r in split["refused"]))

    def test_unsupported_bridge_stays_open(self):
        bridge = {"text": "∀ x, R x → Q x", "from": f"{A}.PtoR.R", "to": "Other.T.Q", "used": [0]}
        f = finding("t", ["ptor"], lean={"closed": None, "bridges": [bridge]})
        h = Harness(self.corpus, f, self.trace_path, stub(lambda g: {"countermodel": None}))
        item = h.item()
        self.assertEqual(self.diag(item)["e"], "possible")
        opened = [a for a in item["actions"] if a["action"] == "open-bridge"]
        self.assertEqual(len(opened), 1)
        self.assertEqual(opened[0]["report"]["status"], "OPEN")
        self.assertEqual(opened[0]["goals"], [])
        for a in item["actions"]:
            for g in a["goals"]:
                self.assertTrue(set(g["premises"]) <= set(self.corpus.statements))
        h.auto()
        reported = [e for e in h.trace.entries if e["action"] == "open-bridge"]
        self.assertEqual(len(reported), 1)
        self.assertEqual(reported[0]["outcome"]["status"], "OPEN")

    def test_expired_budget_stays_unresolved(self):
        f = finding("t", ["ptor"], lean={"error": "Lean timed out after 300s"})
        h = Harness(self.corpus, f, self.trace_path, None)
        self.assertEqual(self.diag(h.item())["a"], "supported")
        self.assertEqual(bp.assess({"error": "Lean timed out after 9s"},
                                   {"command": "discover", "premises": [], "target": "t"},
                                   self.corpus)["status"], "unresolved")
        out = bp.assess({"closed": None}, {"command": "discover", "premises": ["ptor"], "target": "t"},
                        self.corpus)
        self.assertEqual(out["status"], "unresolved")
        self.assertIn("not refuted", out["notes"][0])

    def test_kept_premise_without_model_is_not_called_necessary(self):
        raw = {"closed": {"prover": "duper", "used": [0, 1], "axioms": []}, "minimal": [0, 1],
               "deletions": [{"premise": 0, "outcome": "kept"}, {"premise": 1, "outcome": "kept"}],
               "omissions": [{"premise": 0, "model": None}, {"premise": 1, "model": "all False"}],
               "witness": "all True", "probe": False, "vacuous": None, "domain_identified_by_name": []}
        out = bp.assess(raw, {"command": "discover", "premises": ["ptor", "rtoq"], "target": "t"},
                        self.corpus, senses=False)
        status = {n["premise"]: n["status"] for n in out["necessity"]}
        self.assertEqual(status["ptor"], "kept within budget; necessity unresolved")
        self.assertEqual(status["rtoq"], "needed (one-point omission model)")
        self.assertEqual(out["status"], "closed-candidate")

    def test_literal_negation_is_not_support(self):
        lean = {"closed": {"prover": "duper", "used": [0, 1]}, "vacuous": {"used": [0, 1]},
                "vacuous_core": [0, 1], "literal_negation": [0, 1]}
        f = finding("t", ["allp", "notallp"], kind="filtered", lean=lean, filters=["literal_negation"])
        item = Harness(self.corpus, f, self.trace_path, None).item()
        self.assertEqual(self.diag(item)["d"], "supported")
        self.assertEqual([a["action"] for a in item["actions"]], ["reject"])
        self.assertEqual(bp.assess(lean, {"command": "discover", "premises": ["allp", "notallp"],
                                          "target": "t"}, self.corpus)["status"],
                         "rejected-literal-negation")

    def test_domain_by_name_is_not_merged(self):
        lean = {"closed": {"prover": "duper", "used": [0]}, "minimal": [0],
                "domain_identified_by_name": [f"{B}.NoElement.B = {A}.Target.B"]}
        f = finding("t", ["noel"], kind="filtered", lean=lean, filters=["domain_by_name"],
                    premises=["noel"])
        before = sorted(p.read_text() for p in (self.root / "corpus").rglob("*.json"))
        h = Harness(self.corpus, f, self.trace_path, stub(lambda g: {"closed": None}))
        item = h.item()
        self.assertEqual(self.diag(item)["c"], "supported")
        strict = [a for a in item["actions"] if a["action"] == "strict-domains"]
        self.assertTrue(strict and strict[0]["goals"][0]["strict_domains"])
        h.auto()
        self.assertEqual(self.diag(h.item())["c"], "supported")
        self.assertEqual(before, sorted(p.read_text() for p in (self.root / "corpus").rglob("*.json")))

    def test_no_repair_loop_and_no_duplicate_inputs(self):
        h = Harness(self.corpus, finding("t", ["ptor"]), self.trace_path,
                    stub(lambda g: {"closed": None, "countermodel": None, "premises_model": "all True"}))
        runs = h.auto()
        keys = [e["key"] for e in h.trace.entries if e.get("key")]
        self.assertEqual(len(keys), len(set(keys)))
        self.assertLessEqual(runs, bp.MAX_ATTEMPTS_PER_GOAL + 2)
        actions = [e["action"] for e in h.trace.entries]
        self.assertEqual(actions, ["engine", "countermodel", "budget"])
        # A rerun from the saved trace proposes nothing new.
        again = Harness(self.corpus, finding("t", ["ptor"]), self.trace_path, h.runner)
        self.assertEqual(again.auto(), 0)
        self.assertEqual(len(again.trace.entries), len(h.trace.entries))

    def test_attempt_cap(self):
        trace = bp.Trace(None)
        f = finding("t", ["ptor"])
        for i in range(bp.MAX_ATTEMPTS_PER_GOAL):
            trace.add({"key": f"k{i}", "goal_label": bp.goal_label(f), "action": "budget",
                       "revision": "rev"})
        actions = bp.plan(f, self.corpus, OPTIONS, [], trace, "rev")
        cm = next(a for a in actions if a["action"] == "countermodel")
        self.assertTrue(any("attempt cap" in r for r in cm["refused"]))

    def test_attempt_cap_counts_every_goal_of_an_action(self):
        # Seven runs: a one-goal action fits, a two-goal split would make nine.
        trace = bp.Trace(None)
        f = finding("t", ["ptor"])
        for i in range(bp.MAX_ATTEMPTS_PER_GOAL - 1):
            trace.add({"key": f"k{i}", "goal_label": bp.goal_label(f), "action": "budget",
                       "revision": "rev"})
        rows = [{"argument": "x", "premises": ["ptor", "rtoq"], "not_retrieved": ["rtoq"],
                 "unidentified": [], "binding": []}]
        actions = {a["action"]: a for a in bp.plan(f, self.corpus, OPTIONS, rows, trace, "rev")}
        self.assertEqual(len(actions["split"]["goals"]), 2)
        self.assertTrue(any("attempt cap" in r for r in actions["split"]["refused"]))
        self.assertFalse(any("attempt cap" in r for r in actions["countermodel"]["refused"]))

    def test_settled_diagnosis_is_not_retried_with_another_bundle(self):
        f = finding("t", ["ptor"])
        rows = [{"argument": a, "premises": ["ptor", p], "not_retrieved": [p], "unidentified": [],
                 "binding": []} for a, p in (("x", "rtoq"), ("y", "allp"))]
        trace = bp.Trace(None)
        first = [a for a in bp.plan(f, self.corpus, OPTIONS, rows, trace, "rev")
                 if a["action"] == "known-bundle"]
        self.assertEqual([a["refused"] for a in first], [[], []])
        trace.add({"key": first[0]["goals"][0]["key"], "goal_label": bp.goal_label(f),
                   "action": "known-bundle", "outcome": {"status": "closed-known"}})
        second = [a for a in bp.plan(f, self.corpus, OPTIONS, rows, trace, "rev")
                  if a["action"] == "known-bundle"]
        self.assertTrue(all(any("already settled" in r for r in a["refused"]) for a in second))

    def test_action_ids_do_not_shift(self):
        f = finding("t", ["ptor"])
        rows = [{"argument": "x", "premises": ["ptor", "rtoq"], "not_retrieved": ["rtoq"],
                 "unidentified": [], "binding": []}]
        trace = bp.Trace(None)
        before = {a["action"]: a["id"] for a in bp.plan(f, self.corpus, OPTIONS, rows, trace, "rev")}
        cm = next(a for a in bp.plan(f, self.corpus, OPTIONS, rows, trace, "rev")
                  if a["action"] == "countermodel")
        trace.add({"key": cm["goals"][0]["key"], "goal_label": bp.goal_label(f),
                   "action": "countermodel", "outcome": {"status": "no-countermodel"}})
        after = bp.plan(f, self.corpus, OPTIONS, rows, trace, "rev")
        names = [a["action"] for a in after]
        self.assertLess(names.index("split"), names.index("budget"))
        self.assertEqual({a["action"]: a["id"] for a in after if a["action"] != "budget"}, before)

    def test_countermodel_claims_stay_within_the_plain_binding(self):
        f = finding("t", ["ptor"])
        base = {"goal_label": bp.goal_label(f), "action": "countermodel",
                "goal": {"command": "countermodel"}}
        plain = dict(base, key="k1", outcome={"status": "countermodel", "projections_untested": [],
                                              "premises_model": "all True"})
        diag = {d["code"]: d for d in bp.classify(f, self.corpus, OPTIONS, [], [plain])}
        self.assertEqual(diag["a"]["status"], "excluded")
        self.assertIn("plain binding", diag["a"]["evidence"][-1])
        # (e) is never supported by a countermodel alone.
        self.assertEqual(diag["e"]["status"], "possible")
        # A premise model rules out an inconsistent core, not a vacuous target.
        self.assertNotEqual(diag["d"]["status"], "excluded")
        self.assertIn("vacuity of the target is not tested", diag["d"]["evidence"][-1])
        projected = dict(plain, outcome=dict(plain["outcome"], projections_untested=["T.o := P.m.ontic"]))
        diag = {d["code"]: d for d in bp.classify(f, self.corpus, OPTIONS, [], [projected])}
        self.assertEqual(diag["a"]["status"], "possible")
        self.assertIn("projection binding(s) not tested", diag["a"]["evidence"][-1])

    def test_budget_needs_a_completed_countermodel_search(self):
        f = finding("t", ["ptor"])
        trace = bp.Trace(None)
        trace.add({"key": None, "failed_key": "k", "goal_label": bp.goal_label(f),
                   "action": "countermodel", "outcome": {"status": "failed", "infrastructure": True}})
        self.assertNotIn("budget", [a["action"] for a in bp.plan(f, self.corpus, OPTIONS, [], trace, "rev")])

    def test_infrastructure_failures_are_rerun_at_most_twice(self):
        h = Harness(self.corpus, finding("t", ["ptor"]), self.trace_path,
                    stub(lambda g: {"error": "no output", "infrastructure": True}))
        h.auto()
        failed = [e for e in h.trace.entries if e.get("failed_key")]
        self.assertEqual(len(failed), bp.MAX_FAILURES_PER_INPUT)
        self.assertTrue(all(e["key"] is None and e["outcome"]["status"] == "failed" for e in failed))
        cm = next(a for a in h.item()["actions"] if a["action"] == "countermodel")
        self.assertTrue(any("infrastructure" in r for r in cm["refused"]))

    def test_many_goals_do_not_overflow_the_trace(self):
        trace = bp.Trace(None)
        for i in range(100):
            f = dict(finding("t", ["ptor"]), label=f"t{i}")
            bp.seed_trace(trace, f, dict(OPTIONS, heartbeats=1000 + i), "rev", self.corpus, "r")
        self.assertEqual(len(trace.entries), 100)

    def test_unchecked_binders_do_not_support_a_search_gap(self):
        rows = [{"argument": "x", "premises": ["ptor"], "not_retrieved": [], "unidentified": [],
                 "binding": []}]
        f = finding("t", ["ptor"])
        checked = {d["code"]: d["status"] for d in bp.classify(f, self.corpus, OPTIONS, rows, [])}
        unchecked = {d["code"]: d["status"] for d in
                     bp.classify(f, self.corpus, OPTIONS, rows, [], binders_checked=False)}
        self.assertEqual(checked["a"], "supported")
        self.assertEqual(unchecked["a"], "possible")

    def test_projection_filters_and_known_senses(self):
        goal = {"command": "discover", "premises": ["ptor"], "target": "t"}
        closed = {"closed": {"prover": "duper", "used": [0]}, "minimal": [0], "witness": "all True"}
        self.assertEqual(bp.assess(dict(closed, projection_unused=True), goal, self.corpus,
                                   senses=False)["status"], "rejected-projection-unused")
        self.assertEqual(bp.assess(dict(closed, projection={"ambiguous": True}), goal, self.corpus,
                                   senses=False)["status"], "rejected-projection-ambiguous")
        unique = bp.assess(dict(closed, projection={"ambiguous": False, "binder": "T.o",
                                                    "bound_to": "P.m.ontic"}), goal, self.corpus,
                           senses=False)
        self.assertEqual(unique["status"], "closed-candidate")
        self.assertIn("specialization", unique["notes"][-2])
        corpus = make_corpus(self.root, [("k", ["ptor"], "t")])
        known = bp.assess(closed, goal, corpus)
        self.assertEqual(known["status"], "closed-known")
        self.assertIn("senses", known)

    def test_plan_only_repair_writes_no_trace(self):
        report = self.root / "report.json"
        write(report, {"options": OPTIONS, "findings": [finding("t", ["ptor"])]})
        subprocess.run([sys.executable, str(ROOT / "scripts" / "discover_blueprint.py"), "--root",
                        str(self.root), "repair", str(report), "--revision", "rev"],
                       check=True, capture_output=True, text=True)
        self.assertFalse((self.root / "repair-trace.json").exists())

    def test_separate_binders_support_misidentification(self):
        trace = bp.Trace(None)
        f = finding("t", ["ptor"])
        trace.add({"key": "k1", "goal_label": bp.goal_label(f), "action": "known-bundle",
                   "goal": {"command": "discover"}, "outcome": {"status": "unresolved"},
                   "binders": [{"name": "R", "from": f"{A}.PtoR.R", "sense": None},
                               {"name": "CausesIn_2", "from": "M.P.CausesIn", "sense": "s|_ _ esse"}]})
        diag = {d["code"]: d for d in bp.classify(f, self.corpus, OPTIONS, [], trace.entries)}
        self.assertEqual(diag["c"]["status"], "supported")
        self.assertIn("M.P.CausesIn (partial-application tag)", diag["c"]["evidence"][-1])

    def test_tags_follow_the_engine_order(self):
        d = self.root / "corpus" / "disambiguations"
        write(d / "a.json", {"id": "zz", "senses": [
            {"id": "partial", "lean_parameters": [{"declaration": STATEMENTS["ptor"], "parameter": "R",
                                                   "arguments": ["_", "x"]}]}]})
        write(d / "b.json", {"id": "aa", "senses": [
            {"id": "whole", "lean_parameters": [{"declaration": STATEMENTS["ptor"], "parameter": "R"}]}]})
        corpus = bp.Corpus(self.root)
        self.assertEqual([k for *_, k in corpus.lean_tags([STATEMENTS["ptor"]])],
                         ["whole", "partial|_ x"])
        self.assertEqual(corpus.order_sensitive([STATEMENTS["ptor"]]), [f"{STATEMENTS['ptor']}.R"])
        diag = {d["code"]: d for d in bp.classify(finding("t", ["ptor"]), corpus, OPTIONS, [], [])}
        self.assertIn("depends on tag order", diag["c"]["evidence"][0])

    def test_assess_reads_the_minimized_proof_axioms(self):
        corpus = make_corpus(self.root, [("k", ["ptor", "em"], "t")])
        goal = {"command": "discover", "premises": ["ptor", "rtoq"], "target": "t"}
        # The full proof is classical, the minimized one is not: no grant.
        raw = {"closed": {"prover": "duper", "used": [0, 1],
                          "axioms": ["propext", "Classical.choice", "Quot.sound"]},
               "proof": {"prover": "duper", "used": [0], "axioms": ["propext"]},
               "minimal": [0], "witness": "all True"}
        out = bp.assess(raw, goal, corpus, senses=False)
        self.assertEqual(out["status"], "closed-candidate")
        self.assertEqual(out["axioms"], ["propext"])
        raw["proof"]["axioms"] = ["propext", "Classical.choice"]
        self.assertEqual(bp.assess(raw, goal, corpus, senses=False)["status"], "closed-known")
        # A forbidden axiom on the minimized proof rejects it (the engine's filter).
        raw["proof"]["axioms"] = ["propext", "sorryAx"]
        out = bp.assess(raw, goal, corpus, senses=False)
        self.assertEqual(out["status"], "rejected-axioms")
        self.assertIn("sorryAx", out["notes"][-1])

    def test_run_cap_is_per_input_revision(self):
        trace = bp.Trace(None)
        f = finding("t", ["ptor"])
        for i in range(bp.MAX_ATTEMPTS_PER_GOAL):
            trace.add({"key": f"k{i}", "goal_label": bp.goal_label(f), "action": "budget",
                       "revision": "inputs old at abc"})
        old = bp.plan(f, self.corpus, OPTIONS, [], trace, "inputs old at def")
        new = bp.plan(f, self.corpus, OPTIONS, [], trace, "inputs new at def")
        cap = lambda acts: any("attempt cap" in r for a in acts if a["action"] == "countermodel"
                               for r in a["refused"])
        self.assertTrue(cap(old))
        self.assertFalse(cap(new))

    def test_known_modulo_logic(self):
        corpus = make_corpus(self.root, [("k", ["ptor", "em"], "t"), ("free", [], "rtoq")])
        # Excluded middle is granted only to a classical proof (#1850's rule).
        self.assertIsNone(corpus.known(["ptor"], "t"))
        self.assertEqual(corpus.known(["ptor"], "t", classical=True),
                         {"arguments": ["k"], "modulo_logic": True})
        goal = {"command": "discover", "premises": ["ptor"], "target": "t"}
        closed = {"closed": {"prover": "duper", "used": [0], "axioms": []}, "minimal": [0],
                  "witness": "all True"}
        self.assertEqual(bp.assess(closed, goal, corpus, senses=False)["status"], "closed-candidate")
        closed["closed"]["axioms"] = ["propext", "Classical.choice", "Quot.sound"]
        self.assertEqual(bp.assess(closed, goal, corpus, senses=False)["status"], "closed-known")
        self.assertEqual(corpus.known(["ptor", "em"], "t")["modulo_logic"], False)
        self.assertIsNone(corpus.known(["rtoq"], "t"))


def skip_reason() -> str | None:
    if os.environ.get("TRUTH_CORE_LEAN_TESTS") == "false":
        return "Lean integration tests are outside this metadata-only CI job"
    if not shutil.which("lake"):
        return "needs the Lean toolchain (lake)"
    if not DUPER.is_file() and not os.environ.get("CI"):
        return "needs Duper built (`lake build Duper`)"
    return None


@unittest.skipIf(skip_reason(), skip_reason() or "")
class LeanRepairTests(unittest.TestCase):
    """The fixtures of #1833 on the real solver path."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.lean_root = Path(cls.tmp.name) / "lean"
        (cls.lean_root / "TruthCore").mkdir(parents=True)
        steps = []
        for module in ("RepairFixtureA", "RepairFixtureB"):
            shutil.copy(FIXTURES / f"{module}.lean", cls.lean_root / "TruthCore" / f"{module}.lean")
            steps.append(f'lean --root="$1" -o "$1/TruthCore/{module}.olean" "$1/TruthCore/{module}.lean"')
        subprocess.run(["lake", "env", "sh", "-c", " && ".join(steps), "sh", str(cls.lean_root)],
                       cwd=ROOT, check=True, capture_output=True, text=True)
        cls.root = Path(cls.tmp.name) / "corpus-root"
        cls.root.mkdir()
        statements = dict(STATEMENTS)
        statements.pop("em")
        cls.corpus = make_corpus(cls.root, [("lemma", ["qher"], "qev")])
        cls.corpus.statements.pop("em")
        for sid in ("qpairs", "qev"):
            cls.corpus.statements[sid]["definition_ids"] = ["d"]

        def runner(corpus, labelled):
            return bp.run_lean(corpus, labelled, lock=None, launcher=["lake"], modules=MODULES,
                               extra_lean_path=str(cls.lean_root))
        cls.runner = staticmethod(runner)
        # One Lean process for the goals that several tests read.
        goals = {
            "pairs-alone": ("qpairs", ["qher"], "discover", 100000, False),
            "by-name": ("t", ["noel"], "discover", 100000, False),
            "literal": ("t", ["allp", "notallp"], "discover", 100000, False),
            "chain-low": ("chainends", ["chain"], "discover", 1, False),
            "chain-cm": ("chainends", ["chain"], "countermodel", 20000, False),
            "projected": ("onticgood", ["profilegood"], "discover", 100000, False),
        }
        labelled = [(k, {"command": c, "target": t, "premises": p, "heartbeats": hb,
                         "strict_domains": s}) for k, (t, p, c, hb, s) in goals.items()]
        cls.goals = dict(labelled)
        cls.raw = runner(cls.corpus, labelled)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def harness(self, f):
        return Harness(self.corpus, f, Path(self.tmp.name) / f"trace-{self._testMethodName}.json",
                       self.runner)

    def test_reusable_lemma_unblocks_the_goal(self):
        self.assertEqual(bp.assess(self.raw["pairs-alone"], self.goals["pairs-alone"],
                                   self.corpus)["status"], "unresolved")
        h = self.harness(finding("qpairs", ["qher"]))
        [entry] = h.run("reuse-lemma")
        self.assertEqual(entry["modified"]["added"], ["qev"])
        out = entry["outcome"]
        self.assertEqual(out["status"], "closed-candidate", out)
        self.assertEqual(out["minimal"], ["qev"])
        self.assertNotIn("known", out)
        self.assertEqual([n["status"] for n in out["necessity"]],
                         ["needed (one-point omission model)"])

    def test_by_name_carrier_identification_is_not_a_repair(self):
        raw = self.raw["by-name"]
        self.assertEqual(bp.assess(raw, self.goals["by-name"], self.corpus)["status"],
                         "rejected-domain-by-name")
        f = finding("t", ["noel"], kind="filtered", lean=raw, filters=["domain_by_name"],
                    premises=["noel"])
        h = self.harness(f)
        [entry] = h.run("strict-domains")
        self.assertTrue(entry["goal"]["strict_domains"])
        self.assertEqual(entry["outcome"]["status"], "unresolved")
        self.assertEqual({d["code"]: d["status"] for d in h.item()["diagnoses"]}["c"], "supported")

    def test_literal_conflict_is_not_support(self):
        out = bp.assess(self.raw["literal"], self.goals["literal"], self.corpus)
        self.assertEqual(out["status"], "rejected-literal-negation")

    def test_countermodel_binders_and_bounds(self):
        h = self.harness(finding("t", ["ptor"]))
        [entry] = h.run("countermodel")
        out = entry["outcome"]
        self.assertEqual(out["status"], "countermodel")
        names = {b["name"]: b["from"] for b in out["model"]["binders"]}
        self.assertEqual(names, {"B": f"{A}.Target.B", "P": f"{A}.Target.P", "Q": f"{A}.Target.Q",
                                 "R": f"{A}.PtoR.R"})
        # Q is false and P, R true: P → R holds, P → Q fails.
        self.assertEqual(out["model"]["interpretation"], "slot 1 False, rest True")
        self.assertEqual(out["model"]["slots"], [{"binder": "P", "slots": [0]},
                                                 {"binder": "Q", "slots": [1]},
                                                 {"binder": "R", "slots": [2]}])
        self.assertEqual(out["model"]["projections_untested"], [])
        # The bounds prose is the repair tool's, not Lean's.
        self.assertIn("does not refute any premise", out["model"]["bounds"])
        self.assertTrue(out["premises_model"])
        self.assertEqual({d["code"]: d["status"] for d in h.item()["diagnoses"]}["a"], "excluded")

    def test_countermodel_does_not_cover_projection_bindings(self):
        h = self.harness(finding("onticgood", ["profilegood"]))
        [entry] = h.run("countermodel")
        out = entry["outcome"]
        self.assertEqual(out["status"], "countermodel", out)
        self.assertEqual(out["projections_untested"],
                         [f"{A}.OnticAllGood.o := {A}.ProfileAllGood.m.ontic"])
        self.assertEqual({d["code"]: d["status"] for d in h.item()["diagnoses"]}["a"], "possible")
        # #discover itself closes the goal under that projection binding (by one
        # premise application, so the transcription probe rejects it).
        raw = self.raw["projected"]
        closed = bp.assess(raw, self.goals["projected"], self.corpus)
        self.assertEqual(closed["status"], "rejected-transcription", closed)
        self.assertEqual(closed["projection"]["bound_to"], f"{A}.ProfileAllGood.m.ontic")

    def test_expired_budget_is_unresolved_not_refuted(self):
        self.assertEqual(bp.assess(self.raw["chain-low"], self.goals["chain-low"],
                                   self.corpus)["status"], "unresolved")
        self.assertEqual(bp.assess(self.raw["chain-cm"], self.goals["chain-cm"],
                                   self.corpus)["status"], "no-countermodel")


if __name__ == "__main__":
    unittest.main()
