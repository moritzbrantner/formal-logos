"""`truth configuration-report`, live `configurations` and `models --check /
--argument / --verify` against `corpus.py` (#954 slice A6), with no Lean.

Both implementations run on the configuration fixture checkout with a
recorded toolchain on PATH: a `lake` that answers `lake build`, prints the
`#print axioms` lines Lean prints for a generated certificate file, and
describes the fixture theorems as `scripts/BindTypes.lean` would, plus a
`scripts/verify-result.sh` stub. Each fake logs its invocations, so the test
compares the Lean/verifier calls as well as the outputs: the written bundle
byte for byte (Rust adds only `producer.producer_sha256`), freshness errors,
and every failure message and exit code."""
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from truth_parity.check import write_check_fixture
from truth_parity.common import U, ParityCase
from truth_parity.configurations import configuration_records

FAKE_LAKE = r'''#!/usr/bin/env python3
"""Recorded Lean for the configuration parity fixture."""
import json, os, re, sys
from pathlib import Path

args = sys.argv[1:]
fail = os.environ.get("FAKE_FAIL", "")
root = Path.cwd()


def log(entry):
    with open(os.environ["FAKE_LOG"], "a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry) + "\n")


if args[:1] == ["build"]:
    log(["lake", *args])
    if fail == "build":
        print("build broke")
        sys.exit(1)
    sys.exit(0)
if args[:3] == ["env", "lean", "--run"]:
    request = json.loads(Path(args[4]).read_text(encoding="utf-8"))
    log(["bind", args[3], request])
    load = lambda kind: {r["id"]: r for r in (json.loads(p.read_text()) for p in (root / "corpus" / kind).glob("*.json"))}
    statements, arguments, results = load("statements"), load("arguments"), load("results")
    by_theorem = {result["theorem"]: result for result in results.values()}
    described = []
    for theorem in request["theorems"]:
        argument = arguments[by_theorem[theorem]["argument_id"]]
        head = lambda sid: statements[sid]["lean_declaration"]
        binders = [{"name": f"h{i}", "prop": True, "head": head(sid), "type": head(sid), "senses": []}
                   for i, sid in enumerate(argument["premise_statement_ids"])]
        conclusion = head(argument["conclusion_statement_id"])
        if fail == "bind":
            conclusion = "TruthCore.Fix.fixE"
        described.append({"theorem": theorem, "binders": binders,
                          "result": {"name": None, "prop": True, "head": conclusion, "type": conclusion, "senses": []}})
    print(json.dumps(described))
    sys.exit(0)
if args[:2] == ["env", "lean"]:
    source = Path(args[2]).read_text(encoding="utf-8")
    namespace = re.search(r"^namespace (\S+)", source, re.M).group(1)
    log(["lean", namespace, source])
    if fail == namespace:
        print(f"{namespace} rejected")
        print("lean error", file=sys.stderr)
        sys.exit(1)
    for index, name in enumerate(re.findall(r"^#print axioms (\S+)", source, re.M)):
        if fail == "axioms" and index == 0:
            print(f"'{namespace}.{name}' depends on axioms: [Classical.choice,\n propext]")
        else:
            print(f"'{namespace}.{name}' does not depend on any axioms")
    sys.exit(0)
sys.exit(f"unexpected lake call {args}")
'''

FAKE_VERIFY = r'''#!/usr/bin/env python3
import json, os, sys
with open(os.environ["FAKE_LOG"], "a", encoding="utf-8") as handle:
    handle.write(json.dumps(["verify-result", *sys.argv[1:]]) + "\n")
if os.environ.get("FAKE_FAIL") == "verify":
    print("comparator rejected")
    sys.exit(1)
'''

# The configuration report's fixed inputs besides the copied scripts/*.py.
STUB_INPUTS = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "TruthCore.lean",
               "scripts/BindTypes.lean", "scripts/verifier-pins.env", "scripts/bootstrap-verifier.sh",
               "verifier/Cargo.toml", "verifier/Cargo.lock", "verifier/src/main.rs")


def write_fixture(root, defect=False):
    """The configuration fixture as a Git checkout with the recorded toolchain.
    Its applicable models satisfy the certified core {STMT-A} (a verification
    defect) unless they are changed to violate STMT-A."""
    records = configuration_records()
    for model in records["models"] if not defect else ():
        for evaluation in model["evaluations"]:
            if evaluation["statement_id"] == "STMT-A":
                evaluation["value"] = "violates"
    write_check_fixture(root, records=records)
    for path in STUB_INPUTS:
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(f"stub {path}\n")
    for path, text in (("bin/lake", FAKE_LAKE), ("scripts/verify-result.sh", FAKE_VERIFY)):
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text)
        (root / path).chmod(0o755)
    git = ["git", "-C", str(root), "-c", "user.name=fixture", "-c", "user.email=fixture@example.org"]
    subprocess.run([*git, "init", "-q"], check=True)
    subprocess.run([*git, "add", "-A"], check=True)
    subprocess.run([*git, "commit", "-qm", "fixture"], check=True)


class TruthConfigurationReportParity(ParityCase):
    """Live configuration paths through a recorded toolchain."""

    def run_both(self, root, argv, rust_argv=None, fail="", path=None):
        """(Python, Rust) results of one command, each with its normalized
        toolchain log."""
        outcomes = []
        for command in ([sys.executable, str(root / "scripts" / "corpus.py"), *argv],
                        [str(self.binary), "--root", str(root), *(rust_argv or argv)]):
            log = root / "fake.log"
            log.unlink(missing_ok=True)
            environment = {**os.environ, "FAKE_LOG": str(log), "FAKE_FAIL": fail,
                           "PATH": path if path is not None else f"{root / 'bin'}{os.pathsep}{os.environ['PATH']}"}
            for name in ("TRUTH_CORE_CONFIGURATION_REPORT", "TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT"):
                environment.pop(name, None)
            result = subprocess.run(command, cwd=root, env=environment, capture_output=True, text=True, check=False)
            calls = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
            outcomes.append((result, calls))
        return outcomes

    @staticmethod
    def scratch(text):
        """Temporary certificate paths differ by design (Python `tmp*.lean`)."""
        return re.sub(r"'[^']*/[^'/]*\.lean'", "'<scratch>.lean'", text)

    def assert_same(self, root, argv, rust_argv=None, code=0, fail="", path=None, compare=None, same_calls=True):
        (python, python_calls), (rust, rust_calls) = self.run_both(root, argv, rust_argv, fail, path)
        self.assertEqual(python.returncode, code, (argv, python.stderr))
        self.assertEqual(rust.returncode, code, (argv, rust.stderr))
        if same_calls:
            self.assertEqual(rust_calls, python_calls, argv)
        else:
            self.assertEqual(rust_calls, [], argv)
        if code:
            self.assertEqual(self.scratch(rust.stderr), self.scratch(python.stderr), argv)
            self.assertEqual(rust.stdout, python.stdout, argv)
        elif compare is not None:
            compare(python.stdout, rust.stdout)
        else:
            self.assertEqual(rust.stdout, python.stdout, argv)
        return python_calls

    def json_equal(self, python, rust):
        actual = json.loads(rust)
        if isinstance(actual, dict):
            self.assertTrue(actual.pop("input_identity").startswith("fnv1a64:"))
        self.assertEqual(actual, json.loads(python))

    def test_bundle_and_freshness(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(root)
            python_bundle = root / ".cache" / "configuration-explorer.json"
            rust_bundle = root / ".cache" / "rust.json"
            (python, python_calls), (rust, rust_calls) = self.run_both(
                root, ["configuration-report", "--output", str(python_bundle)],
                ["configuration-report", "--output", ".cache/rust.json"])
            self.assertEqual(python.returncode, 0, python.stderr)
            self.assertEqual(rust.returncode, 0, rust.stderr)
            self.assertEqual(rust_calls, python_calls)
            kinds = [call[0] for call in python_calls]
            self.assertEqual(kinds.count("verify-result"), 2)
            self.assertEqual(kinds[-1], "lean", "family cores are replayed last")
            self.assertIn("bind", kinds)
            self.assertEqual(rust.stdout, python.stdout)
            # Byte-identical except the producer fingerprint line.
            rust_text = rust_bundle.read_text(encoding="utf-8")
            fingerprint = re.compile(r'^    "producer_sha256": "[0-9a-f]{64}",\n', re.M)
            self.assertEqual(len(fingerprint.findall(rust_text)), 1)
            self.assertEqual(fingerprint.sub("", rust_text), python_bundle.read_text(encoding="utf-8"))
            bundle = json.loads(rust_text)
            self.assertTrue(any(node["kind"] == "decision" for case in bundle["cases"]
                                for node in case["assumption_space"]["nodes"]))
            self.assertTrue(any(case["family_verification"]["cores"] for case in bundle["cases"]))
            # Freshness: each accepts its own bundle; Python ignores the
            # fingerprint, Rust requires it.
            for flags in ([], ["--json"]):
                python_check = self.run_both(root, ["configuration-report", "--check", str(python_bundle), *flags])[0][0]
                rust_check = self.run_both(root, ["configuration-report", "--check", ".cache/rust.json", *flags])[1][0]
                self.assertEqual((python_check.returncode, rust_check.returncode), (0, 0), rust_check.stderr)
                if flags:
                    projection = json.loads(rust_check.stdout)
                    self.assertNotIn("inputs", projection["producer"])
                    self.assertEqual(projection["producer"].pop("producer_sha256"),
                                     bundle["producer"]["producer_sha256"])
                    self.assertEqual(projection, json.loads(python_check.stdout))
                    self.assertEqual(rust_check.stdout,
                                     json.dumps(json.loads(rust_check.stdout), indent=2, ensure_ascii=False,
                                                sort_keys=True) + "\n")
                else:
                    self.assertEqual(rust_check.stdout, python_check.stdout)
            self.assertEqual(self.run_both(root, ["configuration-report", "--check", ".cache/rust.json"])[0][0].returncode, 0)
            missing = self.run_both(root, ["configuration-report", "--check", str(python_bundle)])[1][0]
            self.assertEqual((missing.returncode, missing.stderr),
                             (2, "corpus error: configuration report lacks producer provenance\n"))
            stale = dict(bundle)
            stale["producer"] = {**bundle["producer"], "producer_sha256": "0" * 64}
            (root / ".cache" / "stale.json").write_text(json.dumps(stale))
            refused = self.run_both(root, ["configuration-report", "--check", ".cache/stale.json"])[1][0]
            self.assertEqual(refused.stderr, "corpus error: stale configuration report producer: truth sources changed\n")
            # --build-input: development mode, the certified path and its guards.
            self.assert_same(root, ["configuration-report", "--build-input"])
            self.assert_same(root, ["configuration-report", "--build-input", "--json"])
            for environment, code in (({"TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT": "true"}, 2),
                                      ({"TRUTH_CORE_CONFIGURATION_REPORT": ".cache/rust.json"}, 2),
                                      ({"TRUTH_CORE_CONFIGURATION_REPORT": ".cache/configuration-explorer.json"}, None)):
                with self.subTest(environment=environment):
                    results = []
                    for command in ([sys.executable, str(root / "scripts" / "corpus.py"), "configuration-report", "--build-input"],
                                    [str(self.binary), "--root", str(root), "configuration-report", "--build-input"]):
                        results.append(subprocess.run(command, cwd=root, env={**os.environ, **environment},
                                                      capture_output=True, text=True, check=False))
                    if code is None:
                        # The certified path reads Python's bundle: Rust needs its fingerprint.
                        self.assertEqual(results[0].returncode, 0, results[0].stderr)
                        self.assertEqual(results[1].stderr, "corpus error: configuration report lacks producer provenance\n")
                    else:
                        self.assertEqual([r.returncode for r in results], [code, code])
                        self.assertEqual(results[1].stderr, results[0].stderr)
            # Stale inputs, malformed bundles and a projection change.
            (root / "corpus" / "configurations" / "extra.txt").write_text("not an input")
            self.assertEqual(self.run_both(root, ["configuration-report", "--check", ".cache/rust.json"])[1][0].returncode, 0)
            (root / "lean-toolchain").write_text("changed\n")
            self.assert_same(root, ["configuration-report", "--check", str(python_bundle)], code=2)
            (root / "lean-toolchain").write_text("stub lean-toolchain\n")
            for name, change in (("schema", lambda b: b.update(schema_version=True)),
                                 ("producer", lambda b: b["producer"].update(mode="registered")),
                                 ("cases", lambda b: b["cases"].pop()),
                                 ("verified", lambda b: b["cases"][0].update(verified=False)),
                                 ("projection", lambda b: b["cases"][0].update(scope="other")),
                                 ("provenance", lambda b: b["cases"][0]["verification"].update(result_ids=[])),
                                 ("models", lambda b: b["cases"][0]["verification"].update(models={})),
                                 ("implications", lambda b: b["cases"][0].update(verified_implications=[])),
                                 ("tree", lambda b: b["cases"][0]["assumption_space"].update(root="n1")),
                                 ("family", lambda b: b["cases"][0].update(family_verification={"cores": 99}))):
                with self.subTest(malformed=name):
                    broken = json.loads(python_bundle.read_text())
                    change(broken)
                    (root / ".cache" / "broken.json").write_text(json.dumps(broken))
                    self.assert_same(root, ["configuration-report", "--check", ".cache/broken.json"], code=2)
            self.assert_same(root, ["configuration-report", "--check", ".cache/absent.json"], code=2)
            # Rust refuses an output outside .cache before verifying; Python after.
            self.assert_same(root, ["configuration-report", "--output", "outside.json"], code=2, same_calls=False)

    def test_live_commands_and_failures(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(root)
            statement, argument = U("statement", "STMT-A"), U("argument", "ARG-AB")
            for argv in (["configurations"], ["configurations", "--json"],
                         ["configurations", "--case", "CONFIG-SECOND", "--premise", "STMT-C", "--premise", "STMT-A"],
                         ["models", "--verify"], ["models", "--check", statement], ["models", "--check", "STMT-A", "--json"],
                         ["models", "--argument", argument], ["models", "--argument", "ARG-AB", "--json"],
                         ["models", "--argument", "ARG-AB", "--premise", "STMT-D"]):
                with self.subTest(argv=argv):
                    calls = self.assert_same(root, argv, compare=self.json_equal if "--json" in argv else None)
                    self.assertTrue(calls, argv)
            for argv in (["models", "--argument", "ARG-NONE"], ["models", "--argument", "ARG-AB", "--check", "STMT-C"],
                         ["models", "--check", "STMT-NONE"], ["models", "--premise", "STMT-A"]):
                with self.subTest(error=argv):
                    self.assert_same(root, argv, code=2)
            # Failures at every Lean step, in both commands.
            for fail in ("build", "ConfigurationCertificates", "axioms", "verify", "FiniteModelCertificates",
                         "ConfigurationCompositions", "bind"):
                for argv in (["configurations"], ["configuration-report", "--output", ".cache/out.json"]):
                    with self.subTest(fail=fail, argv=argv):
                        self.assert_same(root, argv, code=2, fail=fail)
                        self.assertFalse((root / ".cache" / "out.json").exists())
            # A verified report that finds a defect.
            with tempfile.TemporaryDirectory() as other:
                defective = Path(other)
                write_fixture(defective, defect=True)
                for argv in (["configurations"], ["configuration-report", "--output", ".cache/out.json"]):
                    with self.subTest(defect=argv):
                        self.assert_same(defective, argv, code=2)
            # No `lake` at all.
            bare = os.pathsep.join(entry for entry in os.environ["PATH"].split(os.pathsep)
                                   if not (Path(entry) / "lake").exists())
            for argv in (["configurations"], ["models", "--verify"]):
                with self.subTest(no_lake=argv):
                    self.assert_same(root, argv, code=2, path=bare)
