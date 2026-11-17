"""Independent exhaustive oracle for symbolic premise-combination counts."""
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import itertools
import json
from pathlib import Path
import tempfile
import unittest

try:
    from dd import cudd
    import networkx  # Optional dependencies are installed by the focused uv check.
except ImportError as error:
    raise unittest.SkipTest("Run uv run scripts/support_formula.py --self-test for the optional symbolic-analysis tier") from error

import support_formula as support


def fixture(statements, rules, targets=("G",)):
    edges = [{"argument_id": f"rule-{i}", "premise_statement_ids": sorted(set(premises)),
              "conclusion_statement_id": conclusion, "result_ids": [f"result-{i}"]}
             for i, (premises, conclusion) in enumerate(rules)]
    conclusions = {r["conclusion_statement_id"] for r in edges}
    return {"schema_version": 1, "kind": "registered-support-graph", "complete": True,
            "source_head": "fixture", "target_statement_ids": list(targets),
            "statements": [{"id": s, "label": s} for s in sorted(statements)], "rules": edges,
            "terminal_statement_ids": sorted(set(statements) - conclusions)}


def brute_closure(seeds, rules):
    """Scan to saturation, independently of the production work-queue code."""
    reached = set(seeds)
    while True:
        following = reached | {r["conclusion_statement_id"] for r in rules
                               if set(r["premise_statement_ids"]) <= reached}
        if following == reached:
            return reached
        reached = following


def all_subsets(items):
    for bits in itertools.product((False, True), repeat=len(items)):
        yield {item for item, included in zip(items, bits) if included}


def brute_minimal(graph, target, basis):
    allowed = graph["terminal_statement_ids"] if basis == "terminal" else [s["id"] for s in graph["statements"]]
    allowed = sorted(set(allowed) - {target})
    successful = {frozenset(s) for s in all_subsets(allowed) if target in brute_closure(s, graph["rules"])}
    return {s for s in successful if not any(other < s for other in successful)}


class FormulaTests(unittest.TestCase):
    def check_exhaustive(self, graph, basis):
        bdd, formulas, variables, _ = support.solve_graph(graph, basis, memory_mib=64)
        for target, formula in formulas.items():
            minimal = support.minimal_models(bdd, formula, list(variables.values()))
            expected = brute_minimal(graph, target, basis)
            actual = set()
            for selection in all_subsets(sorted(variables)):
                assignment = {var: sid in selection for sid, var in variables.items()}
                if bdd.let(assignment, minimal) == bdd.true:
                    actual.add(frozenset(selection))
            self.assertEqual(actual, expected)
            self.assertEqual(support.exact_count(bdd, minimal), len(expected))
            self.assertEqual(support.minimal_by_shannon(bdd, formula), minimal)
            expected_histogram = {len(s): sum(len(other) == len(s) for other in expected) for s in expected}
            self.assertEqual(support.exact_histogram(bdd, minimal, 100000), expected_histogram)

    def test_cycles_zero_premise_absorption_and_irrelevant_inputs(self):
        graph = fixture("PQSTXZUABGI", [
            (["X"], "P"), (["P"], "Q"), (["Q"], "P"),
            (["Q", "S"], "G"), (["T"], "G"), (["T", "S"], "G"),
            ([], "Z"), (["Z", "U"], "G"),
            (["A"], "B"), (["B"], "A"), (["A"], "G")])
        self.assertEqual(brute_minimal(graph, "G", "terminal"), {
            frozenset({"X", "S"}), frozenset({"T"}), frozenset({"U"})})
        self.check_exhaustive(graph, "terminal")
        self.check_exhaustive(graph, "direct-or-derived")

    def test_direct_acceptance_and_derivation_both_survive(self):
        graph = fixture("GHXY", [(["X", "Y"], "H"), (["H"], "G")], targets=("G", "H"))
        self.assertEqual(brute_minimal(graph, "G", "direct-or-derived"), {
            frozenset({"H"}), frozenset({"X", "Y"})})
        self.check_exhaustive(graph, "terminal")
        self.check_exhaustive(graph, "direct-or-derived")

    def test_unproved_terminal_target_cannot_assume_itself(self):
        graph = fixture("G", [])
        graph["statements"][0]["status"] = "closed"
        self.check_exhaustive(graph, "terminal")
        self.check_exhaustive(graph, "direct-or-derived")
        self.assertEqual(brute_minimal(graph, "G", "terminal"), set())

    def test_zero_premise_target_has_one_empty_support(self):
        graph = fixture("GI", [([], "G")])
        self.check_exhaustive(graph, "terminal")
        self.check_exhaustive(graph, "direct-or-derived")
        self.assertEqual(brute_minimal(graph, "G", "terminal"), {frozenset()})

    def test_complemented_edges_skips_and_constant_roots(self):
        bdd = cudd.BDD()
        bdd.declare("before", "x", "middle", "y", "after")
        bdd.configure(reordering=False)
        formula = ~bdd.var("x") | bdd.var("y")
        self.assertEqual(support.exact_count(bdd, formula), 24)
        self.assertEqual(support.exact_histogram(bdd, formula, 100), {0: 1, 1: 4, 2: 7, 3: 7, 4: 4, 5: 1})
        self.assertEqual(support.exact_count(bdd, bdd.true), 32)
        self.assertEqual(support.exact_count(bdd, bdd.false), 0)
        self.assertEqual(support.minmax_size(bdd, bdd.false), (None, None))

    def test_minimal_count_above_javascript_integer_precision(self):
        bdd = cudd.BDD()
        variables = [f"{i}_{side}" for i in range(54) for side in ("a", "b")] + ["z"]
        bdd.declare(*variables)
        bdd.configure(reordering=False)
        formula = bdd.true
        for i in range(54):
            formula &= bdd.var(f"{i}_a") | bdd.var(f"{i}_b")
        formula |= bdd.var("z")
        minimal = support.minimal_models(bdd, formula, variables)
        # Unlike a power of two, this exact count cannot be represented by a double.
        self.assertEqual(support.exact_count(bdd, minimal), 2**54 + 1)
        self.assertEqual(support.minmax_size(bdd, minimal), (1, 54))
        self.assertEqual(support.exact_histogram(bdd, minimal, 100000), {1: 1, 54: 2**54})

    def test_histogram_limit_does_not_truncate_count(self):
        graph = fixture("GPQ", [(["P"], "G"), (["Q"], "G")])
        with redirect_stderr(StringIO()):
            report = support.calculate(graph, memory_mib=64, histogram_node_limit=0)
        target = report["targets"]["G"]
        self.assertEqual(target["minimal_support_count"], "2")
        self.assertEqual(target["status"], "exact")
        self.assertEqual(target["histogram_status"], "unavailable_node_limit")
        self.assertIsNone(target["size_histogram"])

    def test_invalid_graph_is_rejected(self):
        graph = fixture("GP", [(["P"], "G")])
        graph["rules"][0]["premise_statement_ids"] = ["missing"]
        with self.assertRaisesRegex(ValueError, "Unknown statement"):
            support.validate_graph(graph)

    def test_incomplete_or_wrong_kind_export_is_rejected(self):
        graph = fixture("G", [])
        graph["complete"] = False
        with self.assertRaisesRegex(ValueError, "complete registered-support-graph"):
            support.validate_graph(graph)
        graph["complete"] = True
        graph["kind"] = "bounded-frontier"
        with self.assertRaisesRegex(ValueError, "complete registered-support-graph"):
            support.validate_graph(graph)

    def test_graph_replay_and_export_recover_all_conjunctions(self):
        graph = fixture("GPQ", [(["P"], "G"), (["Q"], "G")])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, report, artifact = root / "graph.json", root / "report.json", root / "bdd.json"
            source.write_text(json.dumps(graph))
            with redirect_stderr(StringIO()), redirect_stdout(StringIO()):
                code = support.main(["--graph", str(source), "--output", str(report), "--bdd-output", str(artifact), "--memory-mib", "64"])
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(report.read_text())["status"], "complete")
            exported = json.loads(artifact.read_text())
            order = exported["variable_order"]

            def evaluate(edge, selected):
                if abs(edge) == 1:
                    return edge == 1
                level, low, high = exported["nodes"][abs(edge) - 2]
                child = high if order[level] in selected else low
                value = evaluate(child, selected)
                return not value if edge < 0 else value

            found = {frozenset(exported["statement_by_variable"][v] for v in selection)
                     for selection in all_subsets(order) if evaluate(exported["roots"]["G_minimal"], selection)}
            self.assertEqual(found, {frozenset({"P"}), frozenset({"Q"})})

    def test_baseline_requires_matching_basis(self):
        current = {"basis": "terminal", "targets": {"G": {"minimal_support_count": "18014398509481985",
                   "minimum_premise_count": 2, "maximum_minimal_premise_count": 5, "mandatory_statement_ids": ["P"]}}}
        old = {"basis": "terminal", "targets": {"G": {"minimal_support_count": "18014398509481984",
               "minimum_premise_count": 3, "maximum_minimal_premise_count": 5, "mandatory_statement_ids": ["Q"]}}}
        delta = support.compare_baseline(current, old)["targets"]["G"]
        self.assertEqual(delta["minimal_support_count_delta"], "1")
        self.assertEqual(delta["mandatory_inputs_removed"], ["Q"])
        old["basis"] = "direct-or-derived"
        self.assertEqual(support.compare_baseline(current, old)["status"], "incomparable")


if __name__ == "__main__":
    unittest.main()
