"""`truth configurations --registered`, `models` and `territory` against
`corpus.py configurations --registered`, `models` and `territory` (#954
slice B2): the real corpus, a fixture checkout with cores, an implication
rule, an inapplicable model, co-failures and a witness defect, and the
broken-registration errors."""
import contextlib
import copy
import io
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from territory import format_territory, territory_report
from truth_parity.check import check_records, write_check_fixture, mutate, CHECK_FAILURES
from truth_parity import golden
from truth_parity.common import U, ParityCase


def python_cli(*argv):
    """`corpus.py ARGV` in this process on the real corpus: (exit code, stdout, stderr)."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = corpus.main_with(list(argv))
    return code, out.getvalue(), err.getvalue()


def python_territory(root, max_atoms=512):
    """`corpus.py territory --json --root ROOT` on the real corpus, without the
    `validate()` the command runs first (the Rust run below validates)."""
    report = corpus.current_frontier(root, False, next_steps=False)
    load = {name: [record for _, record in corpus.load_dir(name)]
            for name in ("statements", "arguments", "results", "relations", "claims", "sources")}
    territory = territory_report(
        statements={record["id"]: record for record in load["statements"]},
        arguments={record["id"]: record for record in load["arguments"]},
        results={record["id"]: record for record in load["results"]},
        relations=load["relations"], claims=load["claims"],
        sources={record["id"]: record for record in load["sources"]},
        models=corpus.registered_models(),
        transcription_results=set(report["transcription_results"]),
        seeds=[item for item in report["items"] if item["path_to_root"] is not None],
        routes=report["routes"]["routes"], max_atoms=max_atoms)
    territory["root"] = root
    return territory


def configuration_records():
    """The `check` fixture plus a case with an incompatibility core, an
    implication rule, a fixed constant one model binds differently, two
    models whose violations co-fail, a model that satisfies a certified
    refutation core (a territory defect) and a result for that refutation."""
    records = check_records()
    lean = "TruthCore.Fix."
    records["results"].append({"id": "RES-AD", "argument_id": "ARG-AD", "challenge_module": lean + "Challenge",
                               "solution_module": lean + "Solution", "theorem": lean + "fixAB",
                               "comparator_config": "results/RES-AD/comparator.json", "status": "verified"})

    def model(mid, constant, evaluations):
        return {"id": mid, "description": "d", "vocabulary": "fix", "lean_declaration": lean + "model",
                "modules": [lean + "Solution"], "bindings": {"W": "Bool", "V": constant},
                "carriers": [{"binding": "W", "theorem": lean + "enum", "elements": ["true", "false"]}],
                "evaluations": [{"statement_id": sid, "value": value, "theorem": lean + "eval", "arguments": ["W"]}
                                for sid, value in evaluations]}

    records["models"] = [
        model("MODEL-FIX", "Bool", [("STMT-A", "satisfies"), ("STMT-B", "violates"), ("STMT-D", "violates")]),
        model("MODEL-NAT", "Nat", [("STMT-A", "satisfies"), ("STMT-B", "violates"), ("STMT-D", "violates"),
                                   ("STMT-E", "satisfies")]),
        model("MODEL-B", "Bool", [("STMT-A", "satisfies"), ("STMT-B", "satisfies"), ("STMT-C", "satisfies"),
                                ("STMT-D", "satisfies")]),
    ]
    case = records["configurations"][0]
    case["semantics"].update(constants={"V": "Bool"},
                             applications={sid: ["W"] for sid in ("STMT-A", "STMT-B", "STMT-C")})
    case["configurations"] = [{"id": "base", "statement_ids": ["STMT-A"]},
                              {"id": "pair", "statement_ids": ["STMT-B", "STMT-A"]},
                              {"id": "consequent", "statement_ids": ["STMT-C", "STMT-B"]},
                              {"id": "empty", "statement_ids": []}]
    case["incompatibility_result_ids"] = ["RES-AB"]
    case["implication_result_ids"] = ["RES-BC"]
    case["model_bindings"] = [{"model_id": mid, "parameters": {"W": "W", "V": "V"}}
                              for mid in ("MODEL-FIX", "MODEL-NAT", "MODEL-B")]
    second = copy.deepcopy(case)
    second.update(id="CONFIG-SECOND", seed_statement_id="STMT-B", incompatibility_result_ids=[],
                  implication_result_ids=[])
    records["configurations"].append(second)
    return records


class TruthConfigurationParity(ParityCase):
    """`truth configurations --registered`, `models` and `territory` against Python."""

    def truth(self, *args, root=None, code=0):
        command = [self.binary] + (["--root", str(root)] if root else []) + list(args)
        result = subprocess.run(command, cwd=corpus.ROOT, capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, code, (args, result.stderr))
        return result

    def assert_same(self, python, *args, root=None):
        """Python's (code, stdout, stderr) against Rust: text byte-identical,
        `--json` semantically equal (Rust adds `input_identity` to objects)."""
        code, stdout, stderr = python
        if root is not None:
            expected = ({"stderr": stderr, "stdout": ""} if code else
                        {"stdout_json": json.loads(stdout)} if "--json" in args else {"stdout": stdout})
            golden.record(self, ["--root", root, *args], root=root, code=code, **expected)
        result = self.truth(*args, root=root, code=code)
        if code:
            self.assertEqual(result.stderr, stderr, args)
            self.assertEqual(result.stdout, "", args)
            return
        if "--json" in args:
            actual = json.loads(result.stdout)
            if isinstance(actual, dict):
                self.assertTrue(actual.pop("input_identity").startswith("fnv1a64:"))
            self.assertEqual(actual, json.loads(stdout), args)
        else:
            self.assertEqual(result.stdout, stdout, args)

    def test_real_corpus_configurations(self):
        cases = {case["id"]: case for case in corpus.registered_configurations()}
        legacy = U("configuration", "CONFIG-NECESSARY-INDIVIDUAL")
        case = cases[legacy]
        premises = sorted(case["semantics"]["applications"])[:2]
        forms = [[], ["--case", legacy], ["--case", "CONFIG-NECESSARY-INDIVIDUAL"],
                 ["--seed", case["seed_statement_id"]],
                 ["--case", legacy, *[arg for sid in premises for arg in ("--premise", sid)]]]
        # The full run covers every case; one more filters a case by uuid.
        forms.append(["--case", sorted(cases)[0]])
        for form in forms:
            for machine in ([], ["--json"]):
                with self.subTest(form=form, json=bool(machine)):
                    argv = ["configurations", "--registered", *form, *machine]
                    self.assert_same(python_cli(*argv), *argv)
        for form in (["--case", "CONFIG-NONE"], ["--seed", "STMT-NONE"],
                     ["--premise", premises[0]],
                     ["--case", legacy, "--premise", premises[0], "--premise", premises[0]],
                     ["--case", legacy, "--premise", U("statement", "STMT-CATHOLICISM-TRUE")]):
            with self.subTest(error=form):
                self.assert_same(python_cli("configurations", "--registered", *form),
                                 "configurations", "--registered", *form)
        # Live verification runs Lean: Rust refuses and names the Python command.
        refused = self.truth("configurations", code=2)
        self.assertIn("python3 scripts/corpus.py configurations", refused.stderr)

    def test_real_corpus_models(self):
        self.assert_same(python_cli("models"), "models")
        self.assert_same(python_cli("models", "--json"), "models", "--json")
        statement = U("statement", "STMT-CATHOLICISM-TRUE")
        self.assert_same(python_cli("models", "--premise", statement), "models", "--premise", statement)
        for flags in (["--verify"], ["--check", statement], ["--argument", "ARG"]):
            refused = self.truth("models", *flags, code=2)
            self.assertIn("python3 scripts/corpus.py models", refused.stderr)

    def test_real_corpus_territory(self):
        root = corpus.DEFAULT_FRONTIER_ROOT
        expected = python_territory(root)
        actual = json.loads(self.truth("--json", "territory").stdout)
        actual.pop("input_identity")
        self.assertEqual(actual, expected)
        self.assertGreater(len(expected["conflicts"]), 0)
        self.assertEqual(self.truth("territory").stdout, corpus.humanize(format_territory(expected)) + "\n")
        for max_atoms in (40, -3):
            with self.subTest(max_atoms=max_atoms):
                actual = json.loads(self.truth("--json", "territory", "--max-atoms", str(max_atoms)).stdout)
                actual.pop("input_identity")
                self.assertEqual(actual, python_territory(root, max_atoms))
        self.assert_same(python_cli("territory", "--root", "STMT-NONE"),
                         "territory", "--frontier-root", "STMT-NONE")

    def fixture_python(self, root, *argv):
        result = subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), *argv],
                                capture_output=True, text=True, check=False)
        return result.returncode, result.stdout, result.stderr

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root, records=configuration_records())
            checked = self.fixture_python(root, "check")
            self.assertEqual(checked[0], 0, checked[2])
            for argv in (["configurations", "--registered"], ["configurations", "--registered", "--json"],
                         ["configurations", "--registered", "--seed", "STMT-B"],
                         ["configurations", "--registered", "--case", "CONFIG-SECOND", "--premise", "STMT-C",
                          "--premise", "STMT-A"],
                         ["configurations", "--registered", "--premise", "STMT-A"],
                         ["models"], ["models", "--json"]):
                with self.subTest(argv=argv):
                    self.assert_same(self.fixture_python(root, *argv), *argv, root=root)
            report = json.loads(self.fixture_python(root, "configurations", "--registered", "--json")[1])
            statuses = {entry["id"]: entry for entry in report[0]["configurations"]}
            self.assertEqual(len(statuses["pair"]["incompatible_cores"]), 1)
            self.assertEqual(statuses["base"]["model_ids"], sorted([U("model", "MODEL-B"), U("model", "MODEL-FIX")]))
            self.assertEqual(len(report[0]["inapplicable_models"]), 1)
            models = json.loads(self.fixture_python(root, "models", "--json")[1])
            self.assertTrue(models["cofailure_candidates"])
            for argv, rust in ((["territory", "--root", "STMT-C"], ["territory", "--frontier-root", "STMT-C"]),
                               (["territory", "--root", "STMT-C", "--max-atoms", "1"],
                                ["territory", "--frontier-root", "STMT-C", "--max-atoms", "1"]),
                               (["territory", "--root", "STMT-C", "--json"],
                                ["--json", "territory", "--frontier-root", "STMT-C"])):
                with self.subTest(argv=argv):
                    self.assert_same(self.fixture_python(root, *argv), *rust, root=root)
            territory = json.loads(self.fixture_python(root, "territory", "--root", "STMT-C", "--json")[1])
            self.assertTrue(territory["conflicts"])
            self.assertEqual({defect["kind"] for defect in territory["defects"]}, {"witness_satisfies_conflict"})
            self.assertIn("DEFECT witness_satisfies_conflict: {'kind'",
                          self.fixture_python(root, "territory", "--root", "STMT-C")[1])
            # A broken corpus: territory validates first, as Python does.
            (root / "corpus" / "statements" / "zz.json").write_text("[]")
            self.assert_same(self.fixture_python(root, "territory", "--root", "STMT-C"),
                             "territory", "--frontier-root", "STMT-C", root=root)

    def test_fixture_registration_errors(self):
        failures = {name: change for name, change in CHECK_FAILURES.items()
                    if name.startswith(("configuration", "model", "bad model"))}
        failures["configuration implication outside the profile"] = mutate("configurations", "CONFIG-SECOND",
                                                              implication_result_ids=[U("result", "RES-AD")])
        failures["configuration unknown model"] = mutate("configurations", "CONFIG-FIX", model_bindings=[
            {"model_id": U("model", "MODEL-NONE"), "parameters": {}}])
        self.assertGreaterEqual(len(failures), 5)
        for name, change in failures.items():
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                write_check_fixture(root, change, records=configuration_records())
                for argv in (["configurations", "--registered"], ["models"]):
                    python = self.fixture_python(root, *argv)
                    self.assert_same(python, *argv, root=root)
                python = self.fixture_python(root, "configurations", "--registered")
                self.assertEqual(python[0], 2, (name, python))
                self.assertTrue(python[2].startswith("corpus error: "), (name, python))
