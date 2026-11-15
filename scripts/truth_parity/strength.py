"""`truth strength-comparisons` and `strength-report` against `corpus.py
strength-comparisons` and `strength-report`.

No Lean runs here. The Python oracle runs unmodified except that its Lean
subprocesses are replaced: `lake build` and `scripts/verify-result.sh`
succeed silently, and each `lean --run scripts/<Tool>.lean` prints the
recorded `<Tool>.json` (BindTypes, CheckStrength, PropositionStructure) from
an exporter directory; Rust replays the same directory with
`--recorded-exporters`. Everything else (registration and Comparator-config
validation, module location, binding validation, the degeneracy guard, the
projection, the input manifest and digest, the Git head, the written bundle
and `--check-input`) runs on both sides.

The fixture cases use the `check` fixture checkout (with a copy of
`scripts/*.py`, committed to a throwaway Git repository) with two registered
comparisons and synthetic exporter output; they cover text and `--json`
output, a selected comparison, `--registered`, the error paths and exit codes,
and `--check-input` on fresh, stale and forged bundles. The real-corpus
cases compare `--registered` always; given `TRUTH_STRENGTH_EXPORTERS` (a
directory recorded for this checkout by `python3 -m truth_parity.strength
record DIR` run from `scripts/`, which needs Lean), they also compare the
replayed reports, the written bundle byte for byte and `--check-input`."""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from truth_parity.bind_check import described
from truth_parity.check import by_id, write_check_fixture
from truth_parity.common import U, ParityCase

FIX = "TruthCore.Fix."

# Runs `corpus.py` at the checkout `argv[1]` with the Lean subprocesses
# replaced by the recorded exporter outputs in the directory `argv[2]`.
ORACLE = """
import subprocess, sys
root, recorded = sys.argv[1], sys.argv[2]
sys.path.insert(0, root + "/scripts")
real = subprocess.run
def fake(cmd, *args, **kwargs):
    if "--run" in cmd:
        tool = str(cmd[cmd.index("--run") + 1]).rsplit("/", 1)[-1].removesuffix(".lean")
        with open(f"{recorded}/{tool}.json", encoding="utf-8") as handle:
            return subprocess.CompletedProcess(cmd, 0, handle.read(), "")
    if ("lake" in cmd and "build" in cmd) or any(str(part).endswith("verify-result.sh") for part in cmd):
        return subprocess.CompletedProcess(cmd, 0, "", "")
    return real(cmd, *args, **kwargs)
subprocess.run = fake
import corpus
sys.exit(corpus.main_with(sys.argv[3:]))
"""

# Records each exporter's stdout of a live `corpus.py strength-comparisons
# --json` at the checkout `argv[1]` into `argv[2]` (Lean runs; Comparator
# does not).
RECORDER = """
import shutil, subprocess, sys
root, out = sys.argv[1], sys.argv[2]
sys.path.insert(0, root + "/scripts")
real = subprocess.run
def fake(cmd, *args, **kwargs):
    if any(str(part).endswith("verify-result.sh") for part in cmd):
        return subprocess.CompletedProcess(cmd, 0, "", "")
    result = real(cmd, *args, **kwargs)
    if "--run" in cmd:
        tool = str(cmd[cmd.index("--run") + 1]).rsplit("/", 1)[-1].removesuffix(".lean")
        with open(f"{out}/{tool}.json", "w", encoding="utf-8") as handle:
            handle.write(result.stdout)
    return result
subprocess.run = fake
import corpus
sys.exit(corpus.main_with(["strength-comparisons", "--json"]))
"""

STRENGTH_LEAN = """namespace TruthCore.Fix
/-- The comparison specification. -/
def spec : Prop := True
def setting : Prop := True
end TruthCore.Fix
"""

# The files the producer's input manifest requires besides the fixture's.
INPUT_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "TruthCore.lean",
               "scripts/BindTypes.lean", "scripts/verify-result.sh", "scripts/verifier-pins.env",
               "scripts/bootstrap-verifier.sh", "verifier/Cargo.toml", "verifier/Cargo.lock",
               "verifier/src/main.rs", "scripts/CheckStrength.lean", "scripts/PropositionStructure.lean")


def comparisons(records):
    """Two registered comparisons: an exact, separated one with a control
    and a background-free telescope, and one with a background, a
    remainder and a converse but no implication."""
    sid = lambda legacy: U("statement", legacy)
    rid = lambda legacy: U("result", legacy)
    by_id(records, "results", "RES-BC")["description"] = "Control: é is \"quoted\"."
    records["relations"] += [
        {"id": U("relation", "REL-CMP-EXACT"), "label": "exact comparison", "subject_kind": "statement",
         "subject_id": sid("STMT-A"), "predicate": "strength_comparison", "object_kind": "statement",
         "object_id": sid("STMT-B"), "delta_statement_id": sid("STMT-D"), "background_statement_ids": [],
         "comparison_spec": FIX + "spec", "note": "A adds D to B — fixture é.",
         "statement_parameter_indices": {"stronger": [], "weaker": [], "delta": []},
         "evidence_result_ids": {"implication": rid("RES-AB"), "equivalence": rid("RES-BC")},
         "explanatory_control_result_ids": [rid("RES-BC")],
         "separator": {"setting": FIX + "setting", "result_id": rid("RES-AB")}},
        {"id": U("relation", "REL-CMP-REMAINDER"), "label": "remainder comparison", "subject_kind": "statement",
         "subject_id": sid("STMT-C"), "predicate": "strength_comparison", "object_kind": "statement",
         "object_id": sid("STMT-D"), "delta_statement_id": sid("STMT-E"),
         "background_statement_ids": [sid("STMT-A")], "remainder_statement_id": sid("STMT-B"),
         "comparison_spec": FIX + "spec", "note": "With a background.",
         "statement_parameter_indices": {"stronger": [0], "weaker": [0, 1], "delta": [], "background.0": [1],
                                         "remainder": [0]},
         "evidence_result_ids": {"reconstruction": rid("RES-AB"), "converse": rid("RES-BC"),
                                 "allowed_cases": rid("RES-BC"), "remainder_identity": rid("RES-AB")}},
    ]


def checker_output(root):
    """The CheckStrength output that binds every registered comparison."""
    statements = {record["id"]: record for record in
                  (json.loads(path.read_text()) for path in (root / "corpus" / "statements").glob("*.json"))}
    results = {record["id"]: record for record in
               (json.loads(path.read_text()) for path in (root / "corpus" / "results").glob("*.json"))}
    output = []
    for path in sorted((root / "corpus" / "relations").glob("*.json")):
        relation = json.loads(path.read_text())
        if relation.get("predicate") != "strength_comparison":
            continue
        fields = [("stronger", relation["subject_id"]), ("weaker", relation["object_id"]),
                  ("delta", relation["delta_statement_id"])]
        fields += [(f"background.{i}", s) for i, s in enumerate(relation["background_statement_ids"])]
        if relation.get("remainder_statement_id"):
            fields.append(("remainder", relation["remainder_statement_id"]))
        binding = {"id": relation["id"], "specification": relation["comparison_spec"], "bound": True,
                   "parameters": [{"name": "x", "type": "Nat", "binder_info": "default"}],
                   "formulas": {"background": [], "stronger": "S x", "weaker": "W x", "delta": "D x ∧ True",
                                "remainder": ""},
                   "application": "spec x", "weight": 0.5, "big": 1e20,
                   "certificates": [{"role": role, "theorem": results[result]["theorem"], "bound": True,
                                     "expected_type": "∀ x, S x → W x", "actual_type": "S → W"}
                                    for role, result in relation["evidence_result_ids"].items()],
                   "field_bindings": [{"role": role, "declaration": statements[s]["lean_declaration"],
                                       "parameter_indices": relation["statement_parameter_indices"][role],
                                       "expected_application": statements[s]["lean_declaration"] + " x",
                                       "explicit_application": "@" + statements[s]["lean_declaration"],
                                       "expression": "e", "type": "Prop", "bound": True} for role, s in fields],
                   "delta_degenerate": False}
        if relation.get("separator"):
            binding["separator"] = {"setting": relation["separator"]["setting"], "bound": True,
                                    "theorem": results[relation["separator"]["result_id"]]["theorem"],
                                    "application": "setting", "axioms": []}
        output.append(binding)
    return output


def structure_output(names):
    """A PropositionStructure row for each declaration."""
    return [{"declaration": name, "coverage": "complete",
             "type": {"id": f"{name}/type", "kind": "sort", "text": "Prop ∧ é", "type": "Type", "coverage": "complete",
                      "children": [], "declaration": name}} for name in names]


def commit(root):
    git = ["git", "-C", str(root), "-c", "user.name=parity", "-c", "user.email=parity@example.invalid"]
    subprocess.run([*git, "init", "-q"], check=True)
    subprocess.run([*git, "add", "-A"], check=True)
    subprocess.run([*git, "commit", "-q", "-m", "fixture"], check=True)


def restore(root):
    subprocess.run(["git", "-C", str(root), "checkout", "-q", "--", "."], check=True)
    subprocess.run(["git", "-C", str(root), "clean", "-qfd", "-e", ".cache"], check=True)


class TruthStrengthParity(ParityCase):
    """`truth strength-comparisons` / `strength-report` against `corpus.py`."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.scratch = Path(cls.directory.name).resolve()
        cls.root = cls.scratch / "checkout"
        write_check_fixture(cls.root, comparisons)
        (cls.root / "TruthCore" / "Fix" / "Strength.lean").write_text(STRENGTH_LEAN)
        for name in INPUT_FILES:
            (cls.root / name).parent.mkdir(parents=True, exist_ok=True)
            (cls.root / name).write_text(name + "\n")
        commit(cls.root)
        cls.recorded = cls.scratch / "recorded"
        cls.recorded.mkdir()
        cls.record(cls.root, cls.recorded)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    @staticmethod
    def record(root, directory, check=None, bind=None, structure=None):
        """Writes the synthetic exporter outputs for `root` into `directory`."""
        names = [FIX + "spec", *(FIX + name for name in ("fixA", "fixB", "fixD", "fixC", "fixE"))]
        outputs = {"BindTypes": described()[:2] if bind is None else bind,
                   "CheckStrength": checker_output(root) if check is None else check,
                   "PropositionStructure": structure_output(names) if structure is None else structure}
        for tool, value in outputs.items():
            (directory / f"{tool}.json").write_text(value if isinstance(value, str)
                                                    else json.dumps(value, ensure_ascii=False))
        return directory

    def run_both(self, args, root=None, recorded=None, machine=False):
        root = root or self.root
        recorded = recorded or self.recorded
        python = subprocess.run([sys.executable, "-c", ORACLE, str(root), str(recorded), *args,
                                 *(["--json"] if machine else [])],
                                capture_output=True, text=True, check=False)
        rust = subprocess.run([self.binary, "--root", str(root), *(["--json"] if machine else []), *args,
                               "--recorded-exporters", str(recorded)],
                              capture_output=True, text=True, check=False,
                              env={**os.environ, "TRUTH_PARITY_REPLAY": "1"})
        return python, rust

    def assert_same(self, args, code=0, machine=False, **where):
        python, rust = self.run_both(args, machine=machine, **where)
        self.assertEqual(python.returncode, code, python.stderr)
        self.assertEqual(rust.returncode, code, rust.stderr)
        self.assertEqual(rust.stdout, python.stdout, args)
        if code and not machine:
            self.assertEqual(rust.stderr, python.stderr, args)
        return python

    def variant(self, name, change=None, **outputs):
        """A recorded directory with some exporter outputs replaced."""
        directory = self.scratch / name
        directory.mkdir(exist_ok=True)
        if change:
            check = checker_output(self.root)
            change(check)
            outputs["check"] = check
        return self.record(self.root, directory, **outputs)

    def test_reports_text_and_json(self):
        exact = U("relation", "REL-CMP-EXACT")
        only = self.variant("exact", lambda check: check.pop())
        for args in (["strength-comparisons"], ["strength-comparisons", "--registered"],
                     ["strength-comparisons", exact], ["strength-comparisons", exact, "--registered"]):
            for machine in (False, True):
                with self.subTest(args=args, machine=machine):
                    self.assert_same(args, machine=machine, recorded=only if exact in args else None)
        reports = json.loads(self.assert_same(["strength-comparisons"], machine=True).stdout)
        self.assertEqual([r["comparison_status"] for r in reports], ["strict strengthening", "unresolved"])
        self.assertEqual(reports[0]["delta_status"], "exact factorization proved")
        self.assertEqual(reports[1]["remainder_status"], "exact admitted-only remainder proved")
        self.assertTrue(reports[0]["definitions"] and reports[0]["disambiguations"])

    def test_errors_and_exit_codes(self):
        def degenerate(check):
            check[0]["delta_degenerate"] = True

        def unbound(check):
            check[1]["field_bindings"][0]["bound"] = False

        def uncovered(check):
            del check[1]

        def wrong_theorem(check):
            check[0]["certificates"][0]["theorem"] = "Other"

        def unseparated(check):
            check[0]["separator"]["bound"] = False

        def mismatch(check):
            check[0]["specification"] = "Other ∧ é"

        cases = {
            "unknown comparison": (["strength-comparisons", "REL-NOPE"], None),
            "degenerate delta": (["strength-comparisons"], self.variant("degenerate", degenerate)),
            "unbound field": (["strength-comparisons"], self.variant("unbound", unbound)),
            "uncovered comparison": (["strength-comparisons"], self.variant("uncovered", uncovered)),
            "certificate theorem": (["strength-comparisons"], self.variant("theorem", wrong_theorem)),
            "unbound separator": (["strength-comparisons"], self.variant("separator", unseparated)),
            "binding mismatch": (["strength-comparisons"], self.variant("mismatch", mismatch)),
            "checker not JSON": (["strength-comparisons"], self.variant("notjson", check="not json " * 100)),
            "structure missing": (["strength-comparisons"], self.variant("nostructure", structure=structure_output([FIX + "spec"]))),
            "structure error row": (["strength-comparisons"], self.variant("errorrow", structure=[{"declaration": "x", "error": "boom"}])),
            "outside cache": (["strength-report", "--output", str(self.scratch / "outside.json")], None),
        }
        for name, (args, recorded) in cases.items():
            with self.subTest(name):
                self.assert_same(args, code=2, recorded=recorded)
        # A failed canonical binding: the message prints the binding entry,
        # whose key order differs between the implementations.
        bind = described()[:2]
        bind[0]["result"]["head"] = FIX + "fixC"
        python, rust = self.run_both(["strength-comparisons"], recorded=self.variant("bind", bind=bind))
        self.assertEqual((python.returncode, rust.returncode), (2, 2), (python.stderr, rust.stderr))
        self.assertIn("canonical result binding failed", rust.stderr)
        for args in (["strength-comparisons", "--output", "x"], ["strength-report", "--registered"],
                     ["strength-report", "extra"], ["strength-comparisons", "a", "b"]):
            with self.subTest(args=args):
                python, rust = self.run_both(args)
                self.assertEqual((python.returncode, rust.returncode), (2, 2), (python.stderr, rust.stderr))

    def test_invalid_registrations(self):
        exact = U("relation", "REL-CMP-EXACT")
        def change(path_kind, mutate):
            directory = self.root / "corpus" / path_kind
            for path in sorted(directory.glob("*.json")):
                record = json.loads(path.read_text())
                if record["id"] == exact or (path_kind == "results" and record["id"] == U("result", "RES-AB")):
                    mutate(record)
                    path.write_text(json.dumps(record))
                    return
        mutations = {
            "status authority": ("relations", lambda r: r.update(verified=True)),
            "delta equals subject": ("relations", lambda r: r.update(delta_statement_id=r["subject_id"])),
            "unknown evidence": ("relations", lambda r: r.update(evidence_result_ids={"implication": "missing"})),
            "parameter map": ("relations", lambda r: r.update(statement_parameter_indices={"stronger": [1, 0]})),
            "separator shape": ("relations", lambda r: r.update(separator={"setting": ""})),
            "Comparator path": ("results", lambda r: r.update(comparator_config="results/other/comparator.json")),
        }
        for name, (kind, mutate) in mutations.items():
            with self.subTest(name):
                try:
                    change(kind, mutate)
                    self.assert_same(["strength-comparisons", "--registered"], code=2)
                finally:
                    restore(self.root)
        config = next((self.root / "results").glob("*/comparator.json"))
        try:
            config.write_text(json.dumps({**json.loads(config.read_text()), "enable_nanoda": False}))
            self.assert_same(["strength-report", "--check-input", "--output", ".cache/x.json"], code=2)
        finally:
            restore(self.root)

    def test_report_and_check_input(self):
        written = {}
        for side in ("python", "rust"):
            path = self.root / ".cache" / f"{side}.json"
            python, rust = self.run_both(["strength-report", "--output", f".cache/{side}.json"])
            result = python if side == "python" else rust
            self.assertEqual(result.returncode, 0, result.stderr)
            written[side] = (path.read_bytes(), result.stdout)
        self.assertEqual(written["rust"], written["python"])
        self.assert_same(["strength-report", "--output", ".cache/python.json"], machine=True)
        bundle = json.loads(written["python"][0])
        self.assertEqual(bundle["producer"]["mode"], "live-verified")
        artifact = self.root / ".cache" / "artifact.json"

        def check(value, code, mutate=None):
            artifact.write_text(value if isinstance(value, str) else json.dumps(value, ensure_ascii=False))
            try:
                if mutate:
                    mutate()
                for machine in (False, True):
                    self.assert_same(["strength-report", "--check-input", "--output", ".cache/artifact.json"],
                                     code=code, machine=machine)
            finally:
                restore(self.root)

        check(bundle, 0)
        check(bundle, 0, lambda: None)
        for name, mutate in {
            "digest": lambda b: b["producer"].update(input_digest="forged"),
            "trust": lambda b: b["producer"].update(trust="trust me"),
            "schema": lambda b: b.update(schema_version=1),
            "mode": lambda b: b["producer"].update(mode="replayed"),
            "status": lambda b: b["comparisons"][1].update(comparison_status="proved equivalence"),
            "order": lambda b: b["comparisons"].reverse(),
            "missing comparison": lambda b: b["comparisons"].pop(),
            "binding": lambda b: b["comparisons"][0]["binding"].update(bound=False),
            "degenerate": lambda b: b["comparisons"][0]["binding"].update(delta_degenerate=True),
        }.items():
            with self.subTest(name):
                forged = json.loads(json.dumps(bundle))
                mutate(forged)
                check(forged, 2)
        # Python equality: an integer field may be a float, key order is free.
        same = json.loads(json.dumps(bundle))
        same["schema_version"] = 2.0
        same["comparisons"][0] = dict(reversed(list(same["comparisons"][0].items())))
        check(same, 0)
        for name, mutate in {
            "Lean source": lambda: (self.root / "TruthCore" / "Fix" / "Strength.lean").write_text("changed"),
            "new Lean source": lambda: (self.root / "TruthCore" / "New.lean").write_text("new"),
            "claim": lambda: [path.write_text(path.read_text().replace('"i"', '"j"'))
                              for path in (self.root / "corpus" / "claims").glob("*.json")],
            "Python producer": lambda: (self.root / "scripts" / "strength_comparisons.py").open("a").write("# changed\n"),
            "missing input": lambda: (self.root / "verifier" / "Cargo.lock").unlink(),
            "symlinked input": lambda: ((self.root / "scripts" / "CheckStrength.lean").unlink(),
                                        (self.root / "scripts" / "CheckStrength.lean")
                                        .symlink_to(self.root / "lean-toolchain")),
        }.items():
            with self.subTest(name):
                check(bundle, 2, mutate)
        # Replay is gated and never writes the trusted presentation path.
        for env, args in (({}, ["strength-comparisons"]),
                          ({"TRUTH_PARITY_REPLAY": "1"}, ["strength-report"]),
                          ({"TRUTH_PARITY_REPLAY": "1"}, ["strength-report", "--output",
                                                          ".cache/sub/strength-comparisons.json"])):
            replay = subprocess.run([self.binary, "--root", str(self.root), *args, "--recorded-exporters",
                                     str(self.recorded)], capture_output=True, text=True, check=False,
                                    env={**{k: v for k, v in os.environ.items() if k != "TRUTH_PARITY_REPLAY"}, **env})
            self.assertEqual(replay.returncode, 2, replay.stderr)
            self.assertFalse((self.root / ".cache" / "strength-comparisons.json").exists())
        python, rust = self.run_both(["strength-report", "--check-input", "--output", ".cache/absent.json"])
        self.assertEqual((python.returncode, rust.returncode, rust.stderr), (2, 2, python.stderr))
        link = self.root / ".cache" / "link.json"
        link.symlink_to(self.root / ".cache" / "python.json")
        try:
            for args in (["strength-report", "--check-input", "--output", ".cache/link.json"],
                         ["strength-report", "--output", ".cache/link.json"]):
                self.assert_same(args, code=2)
        finally:
            link.unlink()
        artifact.write_text("not json")
        python, rust = self.run_both(["strength-report", "--check-input", "--output", ".cache/artifact.json"])
        self.assertEqual((python.returncode, rust.returncode), (2, 2), (python.stderr, rust.stderr))

    def test_real_registered(self):
        root = corpus.ROOT
        for machine in (False, True):
            with self.subTest(machine=machine):
                python = subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), "strength-comparisons",
                                         "--registered", *(["--json"] if machine else [])],
                                        capture_output=True, text=True, check=False)
                rust = subprocess.run([self.binary, *(["--json"] if machine else []), "strength-comparisons",
                                       "--registered"], cwd=root, capture_output=True, text=True, check=False)
                self.assertEqual((python.returncode, rust.returncode), (0, 0), (python.stderr, rust.stderr))
                self.assertEqual(rust.stdout, python.stdout)

    def test_real_replay(self):
        recorded = os.environ.get("TRUTH_STRENGTH_EXPORTERS")
        if not recorded:
            self.skipTest("TRUTH_STRENGTH_EXPORTERS names no recorded exporter directory for this checkout")
        root, recorded = corpus.ROOT, Path(recorded).resolve()
        for machine in (False, True):
            with self.subTest(machine=machine):
                self.assert_same(["strength-comparisons"], machine=machine, root=root, recorded=recorded)
        written = {}
        for side in ("python", "rust"):
            name = f".cache/strength-parity-{side}.json"
            python, rust = self.run_both(["strength-report", "--output", name], root=root, recorded=recorded)
            result = python if side == "python" else rust
            self.assertEqual(result.returncode, 0, result.stderr)
            written[side] = ((root / name).read_bytes(), result.stdout)
        self.assertEqual(written["rust"], written["python"])
        for machine in (False, True):
            self.assert_same(["strength-report", "--check-input", "--output", ".cache/strength-parity-python.json"],
                             machine=machine, root=root, recorded=recorded)
        for side in ("python", "rust"):
            (root / f".cache/strength-parity-{side}.json").unlink()


if __name__ == "__main__":
    # python3 -m truth_parity.strength record DIR (from scripts/; runs Lean)
    if sys.argv[1:2] != ["record"] or len(sys.argv) != 3:
        sys.exit("usage: python3 -m truth_parity.strength record DIR")
    out = Path(sys.argv[2]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    sys.exit(subprocess.run([sys.executable, "scripts/worker_env.py", "--", sys.executable, "-c", RECORDER,
                             str(corpus.ROOT), str(out)], cwd=corpus.ROOT, stdout=subprocess.DEVNULL).returncode)
