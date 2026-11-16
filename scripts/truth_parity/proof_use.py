"""`truth unused-premises`, `truth lean-reuse` and `truth context
--proof-use` against `corpus.py`.

No Lean runs here. On the `check` fixture (with a copy of `scripts/*.py`)
both CLIs run under a stand-in `lake` that records the exporter input it is
given and prints a recorded `scripts/BindTypes.lean`,
`scripts/UnusedPremises.lean` or `scripts/LeanReuse.lean` output, so the
orchestration (exporter paths, inputs byte for byte, the bind step without
sense problems) is compared as well as the reports; the `--bind-json`,
`--usage-json` and `--proof-use-json` forms read the same recorded outputs.
Text stdout must be byte-identical, `unused-premises --json` too (Python
sorts its keys), the other `--json` reports semantically equal after
dropping `input_identity`; exit codes and `corpus error:` lines agree. On the
real corpus the exporter inputs are compared byte for byte, and with
`TRUTH_UNUSED_BIND_JSON` (a saved `bind-check --json` report),
`TRUTH_UNUSED_USAGE_JSON` (a saved UnusedPremises output) and
`TRUTH_LEAN_REUSE_JSON` (a saved LeanReuse output for every result) the
reports themselves."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from truth_parity.bind_check import FIX, described, hyp
from truth_parity.check import by_id, write_check_fixture
from truth_parity import golden
from truth_parity.common import U, NO_BIND_TYPES, ParityCase, without_bind_types, without_note_field, without_note_mentions

# Stands in for `lake env lean --run TOOL INPUT`: keeps a copy of INPUT under
# $FAKE_CAPTURE and prints the recorded output for TOOL from $FAKE_OUTPUTS.
FAKE_LAKE = """#!/bin/sh
[ "$3" = --run ] || { echo "unexpected lake call: $*" >&2; exit 1; }
[ -f "$4" ] || { echo "missing exporter $4" >&2; exit 1; }
name=$(basename "$4" .lean)
cp "$5" "$FAKE_CAPTURE/$name.json"
cat "$FAKE_OUTPUTS/$name.json"
"""

TOOLS = ("BindTypes", "UnusedPremises", "LeanReuse")


def usage_entry(theorem, *hypotheses):
    return {"theorem": FIX + theorem, "hypotheses": list(hypotheses)}


def used(position, flag=True, **extra):
    return {"position": position, "name": "h", "used": flag, **extra}


def usage():
    """The UnusedPremises output for the fixture: both premises used."""
    return [usage_entry("fixAB", used(0)), usage_entry("fixBC", used(0))]


def bind_output():
    """BindTypes output for the input without senses (no aliases element)."""
    return [entry for entry in described() if "theorem" in entry]


def reuse_rows(ab=(), bc=(FIX + "fixAB",)):
    return [{"theorem": FIX + "fixAB", "proof_theorems": list(ab)},
            {"theorem": FIX + "fixBC", "proof_theorems": list(bc)}]


def exemption(result, *statements, reason="intended bundle"):
    return {"result_id": U("result", result), "statement_ids": [U("statement", s) for s in statements],
            "reason": reason}


def unused_ab(bind, use):
    use[0]["hypotheses"][0]["used"] = False


def bundle_ab(bind, use):
    """fixAB binds STMT-A through a theory-bundle conjunct the proof ignores."""
    bind[0]["binders"] = [hyp("T", "TruthCore.Comparison.Theory", bundle=[hyp("", "fixA")])]
    use[0]["hypotheses"] = [used(0, True, conjuncts_used=[False])]


# name -> (change to (bind output, usage output), exemption file or None, extra arguments)
UNUSED_CASES = {
    "every premise used": (None, None, []),
    "unused premise": (unused_ab, None, []),
    "unused premise, strict": (unused_ab, None, ["--strict"]),
    "unused premise on the root path": (unused_ab, None, ["ROOT", "STMT-C"]),
    "unused bundle conjunct": (bundle_ab, None, ["--strict"]),
    "unfoldable bundle counts as used": (
        lambda bind, use: (bundle_ab(bind, use), use[0]["hypotheses"][0].update(conjuncts_used="cannot unfold")),
        None, ["--strict"]),
    "exempted finding": (unused_ab, {"exemptions": [exemption("RES-AB", "STMT-A")]}, ["--strict"]),
    "stale exemption": (None, {"exemptions": [exemption("RES-BC", "STMT-B")]}, ["--strict"]),
    "exempted and stale": (unused_ab, {"exemptions": [exemption("RES-AB", "STMT-A"),
                                                      exemption("RES-BC", "STMT-B", reason="gone")]}, []),
    "mismatch is skipped": (lambda bind, use: bind[0].update(binders=[hyp("h", "fixE")]), None, ["--strict"]),
    "exporter error is skipped": (lambda bind, use: use[0].update(error="unknown theorem"), None, []),
    "undescribed theorem is skipped": (lambda bind, use: use.pop(0), None, []),
    "missing hypothesis position is skipped": (
        lambda bind, use: use[0].update(hypotheses=[used(5)]), None, []),
    "exemption without a reason": (None, {"exemptions": [exemption("RES-AB", "STMT-A", reason=" ")]}, []),
    "exemption with an extra key": (None, {"exemptions": [dict(exemption("RES-AB", "STMT-A"), note=1)]}, []),
    "exemption without statements": (None, {"exemptions": [dict(exemption("RES-AB"), statement_ids=[])]}, []),
    "exemption with an empty result id": (None, {"exemptions": [dict(exemption("RES-AB", "STMT-A"),
                                                                      result_id="")]}, []),
    "exemption listed twice": (None, {"exemptions": [exemption("RES-AB", "STMT-A"),
                                                     exemption("RES-AB", "STMT-A")]}, []),
    "exemption file without a list": (None, {"exempt": []}, []),
}


class TruthProofUseParity(ParityCase):
    """The proof-term exporter commands from recorded exporter output."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        base = Path(self.temporary.name)
        self.tools = base / "bin"
        self.tools.mkdir()
        (self.tools / "lake").write_text(FAKE_LAKE)
        (self.tools / "lake").chmod(0o755)
        self.outputs = base / "outputs"
        self.outputs.mkdir()
        self.compared = set()

    def record(self, **outputs):
        for name, value in outputs.items():
            (self.outputs / f"{name}.json").write_text(json.dumps(value, ensure_ascii=False))

    def run_cli(self, command, root, arguments, capture):
        capture.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ, PATH=f"{self.tools}{os.pathsep}{os.environ['PATH']}",
                   FAKE_CAPTURE=str(capture), FAKE_OUTPUTS=str(self.outputs), **NO_BIND_TYPES)
        return subprocess.run(command + arguments, capture_output=True, text=True, check=False, env=env,
                              cwd=root)

    def compare(self, root, arguments, *, python_arguments=None, semantic_json=False):
        """Runs both in text and `--json` mode; returns the Python runs."""
        outputs = []
        for json_flag in ([], ["--json"]):
            python = self.run_cli([sys.executable, str(root / "scripts" / "corpus.py")], root,
                                  [*(python_arguments or arguments), *json_flag], root / "capture-python")
            if python.returncode == 2:
                expected = ({"error_message": python.stderr.removeprefix("corpus error: ").removesuffix("\n")}
                            if json_flag else {"stderr": python.stderr})
            elif json_flag and semantic_json:
                expected = {"stdout_json": json.loads(python.stdout)}
            else:
                expected = {"stdout": python.stdout}
            # The exporter inputs the stand-in `lake` captured from Python, which Rust's must equal.
            captured = {str(root / "capture-rust" / f"{tool}.json"): (root / "capture-python" / f"{tool}.json").read_text()
                        for tool in TOOLS if (root / "capture-python" / f"{tool}.json").exists()}
            (root / "capture-rust").mkdir(exist_ok=True)
            golden.record(self, ["--root", root, *arguments, *json_flag], root=root, code=python.returncode,
                          files=captured or None, normalize=["bind_types", "note_mentions"],
                          env={"FAKE_CAPTURE": root / "capture-rust", "FAKE_OUTPUTS": self.outputs, **NO_BIND_TYPES},
                          path_prepend=[self.tools], externals=[self.tools, self.outputs],
                          exclude=("capture-python",), **expected)
            rust = self.run_cli([str(self.binary), "--root", str(root)], root, [*arguments, *json_flag],
                                root / "capture-rust")
            if arguments[0] == "context" and rust.returncode == 0:
                rust.stdout = without_bind_types(rust.stdout)
            self.assertEqual(rust.returncode, python.returncode, (arguments, python.stderr, rust.stderr))
            if python.returncode == 2:
                message = json.loads(rust.stderr)["error"]["message"] if json_flag else None
                if json_flag:
                    self.assertEqual(f"corpus error: {message}\n", python.stderr)
                else:
                    self.assertEqual(rust.stderr, python.stderr)
            elif json_flag and semantic_json:
                report = without_note_field(json.loads(rust.stdout))
                report.pop("input_identity")
                self.assertEqual(report, json.loads(python.stdout), arguments)
            else:
                self.assertEqual(without_note_mentions(rust.stdout), python.stdout, arguments)
            for tool in TOOLS:
                ran = root / "capture-python" / f"{tool}.json"
                if ran.exists():
                    self.compared.add(tool)
                    self.assertEqual((root / "capture-rust" / f"{tool}.json").read_text(), ran.read_text(), tool)
                for side in ("capture-python", "capture-rust"):
                    (root / side / f"{tool}.json").unlink(missing_ok=True)
            outputs.append(python)
        return outputs

    def fixture(self, change=None):
        root = Path(self.temporary.name) / "checkout"
        if root.exists():
            shutil.rmtree(root)
        root.mkdir()
        write_check_fixture(root, change)
        for tool in TOOLS:
            (root / "scripts" / f"{tool}.lean").write_text("-- exporter stand-in\n")
        return root

    def test_unused_premises(self):
        for name, (change, exemptions, extra) in UNUSED_CASES.items():
            with self.subTest(name):
                root = self.fixture()
                bind, use = bind_output(), usage()
                if change is not None:
                    change(bind, use)
                self.record(BindTypes=bind, UnusedPremises=use)
                if exemptions is not None:
                    (root / "scripts" / "unused-premise-exemptions.json").write_text(json.dumps(exemptions))
                rust_arguments = ["unused-premises", *extra]
                python_arguments = ["unused-premises", *extra]
                if extra[:1] == ["ROOT"]:
                    rust_arguments = ["unused-premises", "--frontier-root", extra[1]]
                    python_arguments = ["unused-premises", "--root", extra[1]]
                text, machine = self.compare(root, rust_arguments, python_arguments=python_arguments)
                if name == "unused premise, strict":
                    self.assertEqual(text.returncode, 1)
                if name == "unused premise on the root path":
                    self.assertIn("[open, on root path]", text.stdout)
                if name.startswith("exemption") and name != "exempted and stale":
                    self.assertEqual(text.returncode, 2, text.stderr)
                if name == "every premise used":
                    self.assertEqual(json.loads(machine.stdout)["summary"]["checked"], 2)
        self.assertEqual(self.compared, {"BindTypes", "UnusedPremises"})

    def test_unused_premises_from_saved_reports(self):
        root = self.fixture()
        bind, use = bind_output(), usage()
        unused_ab(bind, use)
        self.record(BindTypes=bind, UnusedPremises=use)
        report = self.run_cli([sys.executable, str(root / "scripts" / "corpus.py")], root,
                              ["bind-check", "--json", "--lean-json", str(self.outputs / "BindTypes.json")],
                              root / "unused")
        (root / "bind.json").write_text(report.stdout)
        exemptions = root / "elsewhere.json"
        exemptions.write_text(json.dumps({"exemptions": [exemption("RES-AB", "STMT-A")]}))
        saved = ["--bind-json", str(root / "bind.json"), "--usage-json", str(self.outputs / "UnusedPremises.json")]
        for extra in (saved, [*saved, "--exemptions", str(exemptions), "--strict"],
                      ["--usage-json", str(self.outputs / "UnusedPremises.json")]):
            with self.subTest(extra=extra):
                self.compare(root, ["unused-premises", *extra])

    def test_unused_premises_validates_first(self):
        root = self.fixture(lambda records: by_id(records, "arguments", "ARG-AB").update(
            conclusion_statement_id="STMT-MISSING"))
        self.record(BindTypes=bind_output(), UnusedPremises=usage())
        text, _ = self.compare(root, ["unused-premises"])
        self.assertTrue(text.stderr.startswith("corpus error: "), text.stderr)

    def reuse_fixture(self):
        """The fixture whose Solution imports the shared Challenge, so the
        import closure reaches both results at depth 1."""
        root = self.fixture()
        solution = root / "TruthCore" / "Fix" / "Solution.lean"
        solution.write_text("import TruthCore.Fix.Challenge\n" + solution.read_text())
        return root

    def test_lean_reuse(self):
        cases = {
            "graph-linked use": (reuse_rows(), ["--review"]),
            "use outside the argument graph": (reuse_rows(ab=[FIX + "fixBC", FIX + "fixAB"], bc=()), ["--review"]),
            "review is required": (reuse_rows(), []),
            "a theorem not inspected": (reuse_rows()[:1], ["--review"]),
            "a duplicate entry": (reuse_rows() + reuse_rows()[:1], ["--review"]),
            "an exporter error": ([{"theorem": FIX + "fixAB", "error": "unknown theorem"}] + reuse_rows()[1:],
                                  ["--review"]),
            "proof_theorems not strings": ([{"theorem": FIX + "fixAB", "proof_theorems": [1]}] + reuse_rows()[1:],
                                           ["--review"]),
            "an entry without a theorem": ([{"proof_theorems": []}] + reuse_rows(), ["--review"]),
            "output not an array": ({"theorem": FIX + "fixAB"}, ["--review"]),
        }
        for name, (rows, extra) in cases.items():
            with self.subTest(name):
                root = self.reuse_fixture()
                self.record(LeanReuse=rows)
                text, machine = self.compare(root, ["lean-reuse", *extra], semantic_json=True)
                if name == "graph-linked use":
                    report = json.loads(machine.stdout)
                    self.assertEqual(report["summary"]["theorem-used, graph-linked"], 1)
                if name == "use outside the argument graph":
                    self.assertIn("review: ", text.stdout)
                saved = ["--usage-json", str(self.outputs / "LeanReuse.json")]
                self.compare(root, ["lean-reuse", *extra, *saved], semantic_json=True)

    def test_context_proof_use(self):
        root = self.reuse_fixture()
        for name, rows in {"used": reuse_rows(ab=[FIX + "fixBC"]), "unused": reuse_rows(bc=()),
                           "an exporter error": reuse_rows()[:1]}.items():
            self.record(LeanReuse=rows)
            for target in ("RES-AB", "RES-BC"):
                for flag in (["--proof-use"], ["--proof-use-json", str(self.outputs / "LeanReuse.json")]):
                    with self.subTest(name, target=target, flag=flag[0]):
                        common = ["context", target, "--related", "0", *flag]
                        text, _ = self.compare(root, [*common, "--frontier-root", "STMT-C"],
                                               python_arguments=[*common, "--root", "STMT-C"],
                                               semantic_json=True)
                        if name == "an exporter error" and target == "RES-BC":
                            self.assertEqual(text.returncode, 2, text.stderr)
                        else:
                            self.assertIn("theorem reuse: Lean proof-term reachability", text.stdout)
        self.assertEqual(self.compared, {"LeanReuse"})

    def test_options_apply_only_to_their_command(self):
        root = self.fixture()
        for arguments in (["status", "--strict"], ["lean-reuse", "--review", "--strict"],
                          ["unused-premises", "--review"], ["context", "RES-AB", "--usage-json", "x"]):
            with self.subTest(arguments=arguments):
                rust = subprocess.run([self.binary, "--root", str(root), *arguments], capture_output=True,
                                      text=True, check=False)
                self.assertEqual(rust.returncode, 2, rust.stderr)

    def test_real_corpus(self):
        """The exporter inputs are Python's byte for byte; with recorded
        exporter outputs the reports agree too."""
        sys.path.insert(0, str(corpus.ROOT / "scripts"))
        results = corpus.load_dir("results")
        self.record(BindTypes=[], UnusedPremises=[], LeanReuse=[
            {"theorem": record["theorem"], "proof_theorems": []} for _, record in results])
        capture = Path(self.temporary.name) / "real"
        unused = self.run_cli([str(self.binary), "--root", str(corpus.ROOT)], corpus.ROOT, ["unused-premises"],
                              capture)
        self.assertEqual(unused.returncode, 0, unused.stderr)
        expected = json.dumps(corpus.bind_tool_input(results))
        self.assertEqual((capture / "BindTypes.json").read_text(), expected)
        self.assertEqual((capture / "UnusedPremises.json").read_text(), expected)
        reuse = self.run_cli([str(self.binary), "--root", str(corpus.ROOT)], corpus.ROOT,
                             ["lean-reuse", "--review"], capture)
        self.assertEqual(reuse.returncode, 0, reuse.stderr)
        ordered = sorted((record for _, record in results), key=lambda record: record["id"])
        theorems = sorted({record["theorem"] for record in ordered})
        expected = json.dumps({"modules": sorted({record["solution_module"] for record in ordered}),
                               "theorems": theorems, "inspect": theorems})
        self.assertEqual((capture / "LeanReuse.json").read_text(), expected)

        def both(arguments, python_arguments=None, semantic=False):
            python = subprocess.run([sys.executable, str(corpus.ROOT / "scripts" / "corpus.py"),
                                     *(python_arguments or arguments)], capture_output=True, text=True, check=False)
            rust = subprocess.run([self.binary, "--root", str(corpus.ROOT), *arguments], capture_output=True,
                                  text=True, check=False, env=dict(os.environ, **NO_BIND_TYPES))
            if arguments[0] == "context" and rust.returncode == 0:
                rust.stdout = without_bind_types(rust.stdout)
            self.assertEqual(rust.returncode, python.returncode, (arguments, python.stderr, rust.stderr))
            if semantic:
                report = without_note_field(json.loads(rust.stdout))
                report.pop("input_identity")
                self.assertEqual(report, json.loads(python.stdout), arguments)
            else:
                self.assertEqual(without_note_mentions(rust.stdout), python.stdout, arguments)

        bind, use = os.environ.get("TRUTH_UNUSED_BIND_JSON"), os.environ.get("TRUTH_UNUSED_USAGE_JSON")
        reuse_json = os.environ.get("TRUTH_LEAN_REUSE_JSON")
        if bind and use:
            for extra in ([], ["--json"], ["--strict"]):
                both(["unused-premises", "--bind-json", bind, "--usage-json", use, *extra])
        if reuse_json:
            both(["lean-reuse", "--review", "--usage-json", reuse_json])
            both(["lean-reuse", "--review", "--json", "--usage-json", reuse_json], semantic=True)
            for _, record in sorted(results, key=lambda item: item[1]["id"])[:: max(1, len(results) // 8)]:
                for extra in ([], ["--json"]):
                    both(["context", record["id"], "--related", "0", "--proof-use-json", reuse_json, *extra],
                         semantic=bool(extra))
        if not (bind and use and reuse_json):
            self.skipTest("set TRUTH_UNUSED_BIND_JSON, TRUTH_UNUSED_USAGE_JSON and TRUTH_LEAN_REUSE_JSON "
                          "to recorded exporter outputs for this checkout")
