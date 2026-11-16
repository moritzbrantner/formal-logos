"""`truth frontier` and `frontier-diff` against `corpus.py frontier`."""
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import corpus
from truth_parity import golden
from truth_parity.common import U, migrate, humanize, migrated_revision, ParityCase
from truth_parity.thickness import thickness_fixture


def frontier_fixture(root):
    """The thickness fixture plus floor markings of every basis (met, unmet,
    owner-approved), a counted retorsion, an unrefuted sceptical rival, an
    objection, inferences and stages, a transcription closure, unavailable and
    bibliographic witnesses, a case split, settlement actions and a Lean
    definition behind the goal-consequent and opaque-atom heuristics."""
    thickness_fixture(root, convert=False)

    def write(kind, record):
        (root / "corpus" / kind / f"{record['id']}.json").write_text(json.dumps(record))

    (root / "corpus" / "inferences").mkdir(exist_ok=True)
    statements = {
        "F-LEG": {"self_evident": {"basis": None}},
        "F-RET": {"self_evident": {"basis": "retorsion", "denial_statement_id": "NF",
                                   "justification_ids": ["RES-RET"]}},
        "F-OBS": {"self_evident": {"basis": "observation", "justification_ids": ["CLAIM-OBS"],
                                   "sceptical_rival_ids": ["SK"]}},
        "F-CG": {"self_evident": {"basis": "common_ground", "question_statement_id": "Q",
                                  "positions": [{"statement_id": "Q", "claim_ids": ["CLAIM-CG"]}]}},
        "F-OWN": {"self_evident": {"basis": "common_ground", "question_statement_id": "Q",
                                   "owner_approval": {"decision": "https://example.invalid/1"},
                                   "disagreement": {"rival_statement_ids": ["Q2"]}}},
        "F-STALE": {"self_evident": {"basis": "legacy", "owner_approval": {"decision": "https://example.invalid/2"},
                                     "disagreement": {"rival_statement_ids": []}}},
        "NF": {}, "SK": {}, "Q": {}, "Q2": {}, "TC": {}, "BR": {"lean_declaration": "Fixture.Bridge"},
        "OPQ": {}, "STMT-GOD-EXISTS": {},
        "CY-A": {}, "CY-B": {}, "CY-D": {}, "CY-G": {}, "CY-H": {},
    }
    for statement_id, extra in statements.items():
        write("statements", {"id": statement_id, "paraphrase": f"{statement_id} paraphrase", **extra})
    e = json.loads((root / "corpus" / "statements" / "E.json").read_text())
    e["settlement_actions"] = [{"kind": "floor", "status": "needs-owner-decision", "description": "d"}]
    write("statements", e)
    for argument_id, premises, conclusion in [
        ("ARG-RET", [], "X"), ("ARG-USE", ["F-LEG", "F-RET", "F-OBS", "F-CG", "F-OWN"], "C"),
        ("ARG-TC", ["F-LEG"], "TC"), ("ARG-TC-USE", ["TC", "OPQ"], "E"), ("ARG-OPQ", ["BR", "D"], "OPQ"),
        ("ARG-GOD", ["U"], "STMT-GOD-EXISTS"),
        # #1476: an ungrounded cycle CY-A <-> CY-B with a dependent CY-D, and
        # a cycle CY-G <-> CY-H entered from the met floor premise F-LEG.
        ("ARG-CY-A", ["CY-B"], "CY-A"), ("ARG-CY-B", ["CY-A"], "CY-B"), ("ARG-CY-D", ["CY-A"], "CY-D"),
        ("ARG-CY-G", ["CY-H"], "CY-G"), ("ARG-CY-H", ["CY-G"], "CY-H"), ("ARG-CY-G-F", ["F-LEG"], "CY-G"),
    ]:
        write("arguments", {"id": argument_id, "premise_statement_ids": premises,
                            "conclusion_statement_id": conclusion, "inference_ids": ["INF"],
                            "meaning": argument_id})
    write("inferences", {"id": "INF", "output_statement_id": "U", "input_statement_ids": ["D"],
                         "assumption_statement_ids": ["Q2"], "discharged_statement_ids": [],
                         "rule": "r", "meaning": "m"})
    (root / "TruthCore").mkdir()
    (root / "TruthCore" / "Defs.lean").write_text("def Bridge (P Q : Prop) : Prop := P → Q\n")
    (root / "Fixture" / "Opaque.lean").write_text(
        "theorem opaque_step (A B : Prop) (h : Bridge A B) (a : A) : B := by\n"
        "  have x := h a\n  exact x\n  done\n"
    )
    for result_id, argument_id, extra in [
        ("RES-RET", "ARG-RET", {}), ("RES-USE", "ARG-USE", {}),
        ("RES-TC", "ARG-TC", {"transcription": "single_application"}),
        ("RES-OPQ", "ARG-OPQ", {"solution_module": "Fixture.Opaque", "theorem": "Fixture.opaque_step"}),
        ("RES-GOD", "ARG-GOD", {"joint_settlement_schema": True,
                                "case_split": {"target_statement_id": "ROOT", "note": "n", "cases": [
                                    {"label": "one", "lean_declaration": "TruthCore.One", "statement_id": "R"},
                                    {"label": "two", "lean_declaration": "TruthCore.Two"}]}}),
        *((f"RES-{name}", f"ARG-{name}", {}) for name in ("CY-A", "CY-B", "CY-D", "CY-G", "CY-H", "CY-G-F")),
    ]:
        write("results", {"id": result_id, "argument_id": argument_id, "challenge_module": "Fixture.Challenge",
                          "solution_module": "Fixture.Solution", "theorem": "Fixture.none",
                          "comparator_config": "c.json", "status": "verified", **extra})
    for relation_id, subject_kind, subject, predicate, obj in [
        ("REL-ALT-NF", "statement", "NF", "alternative_to", "F-RET"),
        ("REL-REFUTE-NF", "argument", "ARG-RET", "refutes", "NF"),
        ("REL-ALT-SK", "statement", "SK", "alternative_to", "F-OBS"),
        ("REL-ALT-Q", "statement", "Q2", "alternative_to", "Q"),
        ("REL-ALT-OWN", "statement", "Q2", "alternative_to", "F-OWN"),
        ("REL-ALT-STALE", "statement", "Q2", "alternative_to", "F-STALE"),
        ("REL-ATTACK", "statement", "Q2", "attacks", "D"),
        ("REL-REFUTE-OPEN", "argument", "ARG-B-H", "refutes", "Q2"),
    ]:
        write("relations", {"id": relation_id, "subject_kind": subject_kind, "subject_id": subject,
                            "predicate": predicate, "object_kind": "statement", "object_id": obj})
    for claim_id, statement_id, extra in [
        ("CLAIM-OBS", "F-OBS", {}), ("CLAIM-CG", "F-CG", {}),
        ("CLAIM-BR", "BR", {"witness": "unavailable"}), ("CLAIM-D2", "D", {"witness": "bibliographic"}),
    ]:
        write("claims", {"id": claim_id, "statement_id": statement_id, "source_id": "SRC", "locator": "1",
                         "interpretation": "i", "status": "accepted", **extra})
    migrate(root)


def python_frontier(root, frontier_root=U("statement", "ROOT")):
    """Python `frontier_report` with next steps on a fixture checkout, without
    the full `validate()` that `corpus.py frontier` runs first."""
    kinds = ("statements", "arguments", "results", "relations", "claims", "inferences")
    records = {kind: [json.loads(path.read_text()) for path in sorted((root / "corpus" / kind).glob("*.json"))]
               for kind in kinds}
    saved = corpus.ROOT
    corpus.ROOT = root
    try:
        flags = corpus.transcription_flags(records["results"], records["arguments"], records["statements"])
    finally:
        corpus.ROOT = saved
    return corpus.frontier_report(records["statements"], records["arguments"], records["results"],
                                  records["relations"], root=frontier_root, transcription=flags,
                                  claims=records["claims"], inferences=records["inferences"],
                                  _include_next_steps=True)


class TruthFrontierParity(ParityCase):
    """`truth frontier` and `frontier-diff` against `corpus.py`."""

    def run_truth(self, *args):
        result = subprocess.run([self.binary, *args], cwd=corpus.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def json_truth(self, *args):
        actual = json.loads(self.run_truth("--json", *args))
        self.assertTrue(actual.pop("input_identity").startswith("fnv1a64:"))
        return actual

    def assert_frontier(self, full, args, checkout=None):
        """Every `frontier` form against one Python report with next steps;
        text as the Python CLI prints it (uuids humanized)."""
        restricted = corpus.restrict_to_root(copy.deepcopy(full))
        for flags, report in (([], full), (["--reaching-root"], restricted)):
            if checkout is not None:
                without = {key: value for key, value in report.items() if key != "next_steps"}
                for extra, expected in (
                    ([], {"stdout_json": report}),
                    (["text"], {"stdout": humanize(corpus.format_frontier(without), checkout) + "\n"}),
                    (["--routes"], {"stdout_json": report["routes"]}),
                    (["text", "--routes"],
                     {"stdout": humanize(corpus.format_routes(report["routes"]), checkout) + "\n"}),
                ):
                    machine = [] if extra[:1] == ["text"] else ["--json"]
                    routes = ["--routes"] if "--routes" in extra else []
                    golden.record(self, [*machine, *args, "frontier", *routes, *flags], root=checkout, code=0,
                                  **expected)
            self.assertEqual(self.json_truth(*args, "frontier", *flags), report, flags)
            without = {key: value for key, value in report.items() if key != "next_steps"}
            self.assertEqual(self.run_truth(*args, "frontier", *flags),
                             humanize(corpus.format_frontier(without), checkout) + "\n")
            self.assertEqual(self.json_truth(*args, "frontier", "--routes", *flags), report["routes"], flags)
            self.assertEqual(self.run_truth(*args, "frontier", "--routes", *flags),
                             humanize(corpus.format_routes(report["routes"]), checkout) + "\n", flags)

    def test_real_corpus(self):
        root = corpus.DEFAULT_FRONTIER_ROOT
        self.assert_frontier(corpus.current_frontier(root, False), [])

    def assert_frontier_diff(self, base):
        root = corpus.DEFAULT_FRONTIER_ROOT
        head = corpus.current_frontier(root, True, next_steps=False)
        delta = corpus.frontier_delta(corpus.revision_frontier(base, root), head)
        delta.update(base=base, head="working tree")
        actual = self.json_truth("frontier-diff", "--base", base)
        engines = actual.pop("engines")
        self.assertEqual(engines["head"], "rust")
        self.assertIn(engines["base"], {"rust", "python"})
        self.assertEqual(actual, delta)
        self.assertEqual(self.run_truth("frontier-diff", "--base", base),
                         humanize(corpus.format_frontier_delta(delta)) + "\n")
        return delta

    def test_real_frontier_diff(self):
        # Base HEAD: the Rust engine when HEAD's corpus.py is the checkout's.
        if not migrated_revision("HEAD"):
            self.skipTest("HEAD's corpus predates the uuid migration (covered by the next test)")
        self.assert_frontier_diff("HEAD")

    def test_real_frontier_diff_across_the_migration(self):
        # A pre-migration base runs its own corpus.py on the root's legacy id;
        # its report is mapped to uuids, so the migration itself is no change.
        base = subprocess.run(["git", "-C", str(corpus.ROOT), "merge-base", "HEAD", "origin/main"],
                              capture_output=True, text=True, check=False).stdout.strip()
        if not base or migrated_revision(base) is not False:
            self.skipTest("no pre-migration base revision available")
        self.assert_frontier_diff(base)

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            frontier_fixture(root)
            full = python_frontier(root)
            # The frontier root may be named by legacy id, label or uuid.
            for token in ("ROOT", U("statement", "ROOT")):
                self.assert_frontier(full, ["--root", str(root), "--frontier-root", token], checkout=root)
            # The fixture exercises what it claims to.
            S = lambda legacy: U("statement", legacy)  # noqa: E731
            self.assertEqual({entry["statement_id"]: entry["met"] for entry in full["floor"]},
                             {S("F-LEG"): True, S("F-RET"): True, S("F-OBS"): False, S("F-CG"): False,
                              S("F-OWN"): True, S("F-STALE"): False})
            self.assertEqual(sorted(c["statement_id"] for c in full["closed_via_transcription"]),
                             sorted([S("B"), S("TC")]))
            flags = {flag["result_id"]: flag for flag in full["transcription_flags"]}
            self.assertTrue(flags[U("result", "RES-OPQ")]["opaque_atoms"])
            self.assertEqual(flags[U("result", "RES-OPQ")]["goal_consequent_premises"],
                             [{"hypothesis": "h", "statement_ids": [S("BR")]}])
            self.assertTrue(full["next_steps"]["partitions"])
            # #1476: no closure from an ungrounded cycle; a grounded one closes.
            closed = full["closed_statements"]
            self.assertNotIn(S("CY-A"), closed)
            self.assertNotIn(S("CY-B"), closed)
            self.assertEqual([closed[S(name)] for name in ("CY-D", "CY-G", "CY-H")], ["proved"] * 3)
            cycle_item = next(item for item in full["items"] if item["statement_id"] == S("CY-A"))
            self.assertTrue(cycle_item["ungrounded_cycle"])
            unknown = python_frontier(root, "NOT-A-STATEMENT")
            unknown_args = ["--root", str(root), "--frontier-root", "NOT-A-STATEMENT"]
            golden.record(self, ["--json", *unknown_args, "frontier"], root=root, code=0, stdout_json=unknown)
            self.assertEqual(self.json_truth(*unknown_args, "frontier"), unknown)

    def test_usage(self):
        for args in (["frontier", "--queue"], ["frontier-diff"], ["status", "--routes"],
                     ["frontier", "--base", "HEAD"]):
            result = subprocess.run([self.binary, "--json", *args], cwd=corpus.ROOT,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 2, args)
