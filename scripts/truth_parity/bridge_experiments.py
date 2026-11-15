"""`truth bridge-experiments` against `corpus.py bridge-experiments` (#953,
#954 slice B6).

The fixture follows `test_bridge_experiments.py`: Lean modules on disk, two
results whose Solutions import one profile module, and attempts citing them.
It keeps readable record ids so the named-control hint (an id containing
CONTROL, OMISSION or COUNTERMODEL) is exercised. Cases: a direct import, an
attempt without explicit focus, a witness mismatch, an unrelated module, a
shared profile without reuse, a missing peer, control hints with truncation,
a blocked attempt, a long blocker, and the errors (unknown result, invalid
profile, limit out of range, an anchor outside the profile, an unknown root).
The real corpus is compared on a spread sample of the results attempts cite, under its own
Solution module and under the module of the #953 note. Text is byte-identical
(stdout, stderr, exit code); `--json` equals Python's report plus
`input_identity`."""
import contextlib
import io
import json
import subprocess
import tempfile
from pathlib import Path

import corpus
from truth_parity import golden
from truth_parity.common import ParityCase

PROFILE = "TruthCore.Semantics.Shared"
SOURCE = "TruthCore.Results.Source.Solution"
CONSUMER = "TruthCore.Results.Consumer.Solution"


def write(root, relative, value):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value if isinstance(value, str) else json.dumps(value, indent=2) + "\n")


def module(root, name, source):
    write(root, name.replace(".", "/") + ".lean", source)


def result(rid, argument, solution, **extra):
    return {"id": rid, "label": rid.lower(), "argument_id": argument, "challenge_module": solution + "C",
            "solution_module": solution, "theorem": f"Test.{rid}", "comparator_config": "c.json",
            "status": "solution-present", **extra}


def argument(aid, premises, conclusion):
    return {"id": aid, "label": aid.lower(), "premise_statement_ids": premises,
            "conclusion_statement_id": conclusion, "meaning": "m", "inference_ids": [f"INF-{aid}"]}


class Fixture:
    def __init__(self, root):
        self.root = root
        self.results = {"RESULT-A": result("RESULT-A", "ARG-A", SOURCE),
                        "RESULT-B": result("RESULT-B", "ARG-B", CONSUMER)}
        self.attempts = {"ATTEMPT-X": {"id": "ATTEMPT-X", "label": "x", "outcome": "succeeded",
                                       "statement_ids": ["STMT-C", "STMT-D"], "evidence": ["RESULT-A", "RESULT-B"],
                                       "blocker": "One independently defended bridge is missing."}}
        module(root, PROFILE, "namespace TruthCore.Semantics.Shared\nend TruthCore.Semantics.Shared\n")
        module(root, SOURCE, f"import {PROFILE}\n")
        module(root, CONSUMER, f"public import {SOURCE}\n")
        for sid in ("STMT-A", "STMT-B", "STMT-C", "STMT-D", "STMT-E"):
            write(root, f"corpus/statements/{sid.lower()}.json",
                  {"id": sid, "label": sid.lower(), "paraphrase": f"Statement {sid}."})
        write(root, "corpus/arguments/a.json", argument("ARG-A", ["STMT-A", "STMT-B"], "STMT-C"))
        write(root, "corpus/arguments/b.json", argument("ARG-B", ["STMT-C", "STMT-E"], "STMT-D"))
        self.save()

    def save(self):
        for directory, records in (("results", self.results), ("attempts", self.attempts)):
            for path in (self.root / "corpus" / directory).glob("*.json"):
                path.unlink()
            for rid, record in records.items():
                write(self.root, f"corpus/{directory}/{rid.lower()}.json", record)


@contextlib.contextmanager
def checkout(root):
    saved = (corpus.ROOT, corpus.CORPUS, corpus._ALIASES)
    corpus.ROOT, corpus.CORPUS, corpus._ALIASES = root, root / "corpus", None
    try:
        yield
    finally:
        corpus.ROOT, corpus.CORPUS, corpus._ALIASES = saved


def python(args, root=None):
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.ExitStack() as stack:
        if root is not None:
            stack.enter_context(checkout(root))
        stack.enter_context(contextlib.redirect_stdout(stdout))
        stack.enter_context(contextlib.redirect_stderr(stderr))
        code = corpus.main_with(["bridge-experiments", *args])
    # The Python command returns None on success (exit status 0).
    return code or 0, stdout.getvalue(), stderr.getvalue()


def rust_args(args):
    """Python's `--root STATEMENT` is `--frontier-root` in Rust."""
    return ["--frontier-root" if arg == "--root" else arg for arg in args]


class TruthBridgeExperimentsParity(ParityCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.fixture = Fixture(self.root)

    def rust(self, args, root, machine=False):
        command = [self.binary, "--root", str(root), *(["--json"] if machine else []),
                   "bridge-experiments", *rust_args(args)]
        done = subprocess.run(command, capture_output=True, text=True)
        return done.returncode, done.stdout, done.stderr

    def compare(self, *args, root=None, code=None):
        root = root or self.root
        expected = python(list(args), root=None if root == corpus.ROOT else root)
        fixture = root != corpus.ROOT
        command = ["--root", root, "bridge-experiments", *rust_args(args)]
        if fixture:
            golden.record(self, command, root=root, code=expected[0], stdout=expected[1], stderr=expected[2])
        self.assertEqual(self.rust(list(args), root), expected)
        if code is not None:
            self.assertEqual(expected[0], code, expected)
        if expected[0] == 0:
            py_code, py_json, _ = python([*args, "--json"], root=None if root == corpus.ROOT else root)
            if fixture:
                golden.record(self, ["--root", root, "--json", *command[2:]], root=root, code=py_code,
                              stdout_json=json.loads(py_json))
            rs_code, rs_json, _ = self.rust(list(args), root, machine=True)
            self.assertEqual((rs_code, py_code), (0, 0))
            report = json.loads(rs_json)
            report.pop("input_identity")
            self.assertEqual(report, json.loads(py_json))
            return report
        if fixture:
            golden.record(self, ["--root", root, "--json", *command[2:]], root=root, code=expected[0])
        self.assertEqual(self.rust(list(args), root, machine=True)[0], expected[0])
        return None

    def run_case(self, *extra, code=0):
        self.fixture.save()
        return self.compare("RESULT-A", "--profile-module", PROFILE, "--root", "STMT-D", *extra, code=code)

    def test_direct_import(self):
        report = self.run_case()
        self.assertEqual(report["experiments"][0]["exact_import_edges"],
                         [{"consumer_result_id": "RESULT-B", "imported_result_id": "RESULT-A"}])

    def test_exclusions(self):
        self.fixture.attempts["ATTEMPT-X"]["statement_ids"] = ["STMT-D"]
        self.assertFalse(self.run_case()["experiments"])
        self.fixture.attempts["ATTEMPT-X"]["statement_ids"] = ["STMT-C", "STMT-D"]
        self.fixture.results["RESULT-A"]["witness_id"] = "PINNED-EDITION-A"
        self.fixture.results["RESULT-B"]["witness_id"] = "PINNED-EDITION-B"
        self.assertEqual(self.run_case()["summary"]["excluded_peer_reasons"]["different_witness"], 1)
        del self.fixture.results["RESULT-A"]["witness_id"]
        self.run_case()
        del self.fixture.results["RESULT-B"]["witness_id"]
        module(self.root, CONSUMER, "import TruthCore.Unrelated\n")
        module(self.root, "TruthCore.Unrelated", "namespace TruthCore.Unrelated\nend TruthCore.Unrelated\n")
        self.assertEqual(self.run_case()["summary"]["excluded_peer_reasons"]["cross_profile"], 1)
        module(self.root, CONSUMER, f"import {PROFILE}\n")
        self.assertEqual(self.run_case()["summary"]["excluded_peer_reasons"]["no_direct_reuse"], 1)
        self.fixture.attempts["ATTEMPT-X"]["evidence"] = ["RESULT-A", "RESULT-MISSING"]
        self.run_case()
        self.fixture.attempts["ATTEMPT-X"]["blocker"] = ""
        self.assertEqual(self.run_case()["summary"]["excluded_peer_reasons"]["no_remaining_question"], 1)

    def test_controls_truncation_and_long_blocker(self):
        self.fixture.attempts["ATTEMPT-Y"] = {
            "id": "ATTEMPT-Y", "label": "y", "outcome": "blocked", "statement_ids": ["STMT-C", "STMT-D", "STMT-NONE"],
            "evidence": ["RESULT-A", "RESULT-B", "OMISSION-CONTROL", "OMISSION-CONTROL"],
            "blocker": "A second unresolved test, " + "é" * 420}
        self.fixture.results["OMISSION-CONTROL"] = result("OMISSION-CONTROL", "ARG-A", SOURCE)
        self.assertEqual(self.run_case("--limit", "1")["truncated"], 1)
        self.fixture.results["OMISSION-CONTROL"]["semantic_profile_id"] = "different"
        self.run_case("--limit", "2")
        self.run_case("--root", "STMT-C", "--limit", "20")

    def test_errors(self):
        self.compare("RESULT-NOPE", "--profile-module", PROFILE, code=2)
        self.compare("RESULT-A", "--profile-module", "../../unsafe", code=2)
        self.compare("RESULT-A", "--profile-module", "TruthCore.Missing", code=2)
        for limit in ("0", "21", "-1"):
            self.compare("RESULT-A", "--profile-module", PROFILE, "--root", "STMT-D", "--limit", limit, code=2)
        self.compare("RESULT-A", "--profile-module", PROFILE, "--root", "STMT-NOPE", code=2)
        module(self.root, SOURCE, "import TruthCore.Elsewhere\n")
        self.compare("RESULT-A", "--profile-module", PROFILE, "--root", "STMT-D", code=2)

    def test_real_corpus(self):
        with checkout(corpus.ROOT):
            results = {record["id"]: record for _, record in corpus.load_dir("results")}
            cited = sorted({rid for _, attempt in corpus.load_dir("attempts")
                            for rid in attempt.get("evidence", []) if rid in results})
        self.assertTrue(cited)
        # A spread sample keeps the job short (each case computes the frontier twice per side).
        sample = cited[::max(1, len(cited) // 10)]
        compared = 0
        for rid in sample:
            with self.subTest(result=rid):
                self.compare(rid, "--profile-module", results[rid]["solution_module"], "--limit", "20",
                             root=corpus.ROOT, code=0)
                compared += 1
        self.compare("ULTIMATE-ADEQUACY-COMPARISON", "--profile-module", "TruthCore.Explanation.UltimateAdequacy",
                     root=corpus.ROOT, code=0)
        self.assertEqual(compared, len(sample))
