"""`truth structure` and `structure-report` against `corpus.py structure`
and `structure-report`.

No Lean runs here. The Python oracle runs unmodified except that its two
Lean subprocesses (`lake build` and `lean --run scripts/PropositionStructure.lean`)
are replaced by a recorded exporter stdout; Rust reads the same stdout with
`--extractor-json`. Everything else (module location, the input manifest and
digest, the frontier statuses, semantic links, Git head, the written
artifact and `--check-input`) runs on both sides.

The fixture cases use the `check` fixture checkout (with a copy of
`scripts/*.py`, committed to a throwaway Git repository) and a synthetic
exporter output; they cover text and `--json` output, ID resolution, the
error paths and exit codes, and `--check-input` on fresh, stale and forged
artifacts. The real-corpus cases replay
`fixtures/proposition-structure-first-slice.json`: the exporter's output for
the explorer's first slice, recorded from `scripts/PropositionStructure.lean`
with expression trees cut below depth 3 to keep the file small. If the first
slice's declarations change, re-record it (see `docs/proposition-structure.md`).

Rust's reports add one field Python's lack: `revision.producer_sha256`, the
fingerprint of the truth crate that produced them (`truth/build.rs`), which
Rust's `--check-input` requires to match the running binary. It lies outside
the input digest and the node ids, so the comparisons strip that one field
from Rust's output (`without_producer`) and compare everything else byte for
byte; `test_producer_provenance` checks the field itself."""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from truth_parity.check import by_id, write_check_fixture
from truth_parity.common import U, ParityCase

FIRST_SLICE_FIXTURE = Path(__file__).resolve().parent / "fixtures" / "proposition-structure-first-slice.json"

# Runs `corpus.py` at the checkout `argv[1]` with the Lean subprocesses
# replaced by the exporter stdout in `argv[2]`.
ORACLE = """
import subprocess, sys
root, fixture = sys.argv[1], sys.argv[2]
sys.path.insert(0, root + "/scripts")
real = subprocess.run
def fake(cmd, *args, **kwargs):
    if "lake" in cmd and "build" in cmd:
        return subprocess.CompletedProcess(cmd, 0, "", "")
    if "--run" in cmd:
        with open(fixture, encoding="utf-8") as handle:
            return subprocess.CompletedProcess(cmd, 0, handle.read(), "")
    return real(cmd, *args, **kwargs)
subprocess.run = fake
import corpus
sys.exit(corpus.main_with(sys.argv[3:]))
"""

FIX = "TruthCore.Fix."

PRODUCER = re.compile(r'"producer_sha256": "[0-9a-f]{64}",\s*')


def without_producer(text):
    """Rust's output with its `revision.producer_sha256` entries removed: the
    only field Python's reports do not have (see the module docstring)."""
    return PRODUCER.sub("", text)

STRUCTURE_LEAN = """public import TruthCore.Fix.Solution
import Mathlib.Order.Basic

namespace TruthCore.Fix
/- def hidden : Prop := True
   still a comment -/
def fixA : Prop := True
@[simp] noncomputable def fixB : Prop := True
theorem fixC : Prop := True
structure Frame where
  holds : Prop
def _root_.TruthCore.Fix.fixD : Prop := True
def fixE : Prop := True
end TruthCore.Fix
"""


def node(nid, kind, text, declaration=None, children=(), **extra):
    value = {"id": nid, "kind": kind, "text": text, "type": "Prop", "coverage": "complete",
             "children": [{"role": f"argument.{i}", "node": child} for i, child in enumerate(children)]}
    if declaration:
        value["declaration"] = declaration
    value.update(extra)
    return value


def exporter_rows():
    """A synthetic exporter output: each fixture declaration's type tree,
    with references, Unicode text, floats and bindings."""
    def row(name, *children, **extra):
        decl = FIX + name
        return {"declaration": decl, "coverage": "structural; é",
                "type": node(f"{decl}/type", "application", f"{name} ∧ x", decl, children,
                             weight=0.1, big=1e20, binding=f"{decl}/type"),
                "references": [{"declaration": FIX + "fixC", "kind": "definition", "type": "Prop"}],
                **extra}
    return [
        row("fixA", node(f"{FIX}fixA/b", "constant", "fixB", FIX + "fixB", binding="")),
        row("fixB", node(f"{FIX}fixB/c", "constant", "fixC", FIX + "fixC")),
        row("fixC"),
        row("fixD", unfold_status="unfolded"),
        {"declaration": FIX + "Frame.holds", "type": node("frame", "sort", "Prop")},
    ]


def link_definitions(records):
    """Give the fixture's definitions Lean declarations, so semantic links
    and disambiguation expression ids have something to find."""
    by_id(records, "definitions", "DEF-X")["lean_declaration"] = FIX + "fixB"
    by_id(records, "definitions", "DEF-Y")["lean_declaration"] = FIX + "fixC"
    by_id(records, "statements", "STMT-A")["definition_ids"] = [U("definition", "DEF-Y")]
    del by_id(records, "statements", "STMT-E")["lean_declaration"]


def commit(root):
    git = ["git", "-C", str(root), "-c", "user.name=parity", "-c", "user.email=parity@example.invalid"]
    subprocess.run([*git, "init", "-q"], check=True)
    subprocess.run([*git, "add", "-A"], check=True)
    subprocess.run([*git, "commit", "-q", "-m", "fixture"], check=True)


class TruthStructureParity(ParityCase):
    """`truth structure` / `structure-report` against `corpus.py`."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name).resolve() / "checkout"
        write_check_fixture(cls.root, link_definitions)
        (cls.root / "TruthCore" / "Fix" / "Structure.lean").write_text(STRUCTURE_LEAN)
        for name in ("lean-toolchain", "lakefile.toml"):
            (cls.root / name).write_text(name + "\n")
        commit(cls.root)
        cls.scratch = Path(cls.directory.name)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def exporter(self, value):
        path = self.scratch / "exporter.json"
        path.write_text(value if isinstance(value, str) else json.dumps(value, ensure_ascii=False))
        return path

    def run_both(self, root, fixture, args, machine=False, rust_args=None):
        python = subprocess.run([sys.executable, "-c", ORACLE, str(root), str(fixture), *args,
                                 *(["--json"] if machine and args[0] == "structure" else [])],
                                capture_output=True, text=True, check=False)
        rust = subprocess.run([self.binary, "--root", str(root), *(["--json"] if machine else []),
                               *(args if rust_args is None else rust_args),
                               "--extractor-json", str(fixture)],
                              capture_output=True, text=True, check=False)
        return python, rust

    def assert_same(self, args, value=None, code=0, machine=False, root=None, fixture=None):
        root = root or self.root
        fixture = fixture or self.exporter(exporter_rows() if value is None else value)
        python, rust = self.run_both(root, fixture, args, machine)
        self.assertEqual(python.returncode, code, python.stderr)
        self.assertEqual(rust.returncode, code, rust.stderr)
        self.assertEqual(without_producer(rust.stdout), python.stdout, args)
        if code and not machine:
            self.assertEqual(rust.stderr, python.stderr, args)
        return python, rust

    def test_statement_reports_text_and_json(self):
        for args in (["structure", "STMT-B"], ["structure", U("statement", "STMT-A"), "--unfold", FIX + "fixA"],
                     ["structure", "STMT-C", "--unfold", FIX + "fixB", "--unfold", FIX + "fixB"]):
            for machine in (False, True):
                with self.subTest(args=args, machine=machine):
                    out, _ = self.assert_same(args, machine=machine)
                    self.assertIn("TruthCore.Fix.fixB", out.stdout)
        report = json.loads(self.assert_same(["structure", "STMT-A"], machine=True)[0].stdout)
        self.assertEqual(report["semantic_links"]["definitions"][0]["expression_ids"][0].split("@")[0],
                         U("statement", "STMT-A"))
        self.assertTrue(report["revision"]["head"])

    def test_errors_and_exit_codes(self):
        cases = {
            "unknown statement": (["structure", "STMT-NOPE"], None),
            "no Lean declaration": (["structure", "STMT-E"], None),
            "library unfold": (["structure", "STMT-A", "--unfold", "Mathlib.Order"], None),
            "unlocatable": (["structure", "STMT-A", "--unfold", FIX + "nowhere"], None),
            "invalid JSON": (["structure", "STMT-A"], "not json " * 100),
            "error row": (["structure", "STMT-A"], [{"declaration": FIX + "fixA", "error": "boom", "n": None}]),
            "not a list": (["structure", "STMT-A"], {"declaration": FIX + "fixA"}),
            "omitted root": (["structure", "STMT-A"], exporter_rows()[1:]),
            "first slice missing": (["structure-report", "--output", str(self.scratch / "never.json")], None),
        }
        for name, (args, value) in cases.items():
            with self.subTest(name):
                self.assert_same(args, value, code=2)
        for args in (["structure"], ["structure-report", "--unfold", FIX + "fixA"],
                     ["structure", "STMT-A", "--check-input"]):
            with self.subTest(args=args):
                python, rust = self.run_both(self.root, self.exporter(exporter_rows()), args)
                self.assertEqual((python.returncode, rust.returncode), (2, 2), (python.stderr, rust.stderr))

    def test_check_input(self):
        # Rust's report: Python ignores its producer field, Rust requires it.
        report = json.loads(self.assert_same(["structure", "STMT-B"], machine=True)[1].stdout)
        artifact = self.scratch / "artifact.json"

        def check(value, code, mutate=None):
            artifact.write_text(value if isinstance(value, str) else json.dumps(value, ensure_ascii=False))
            if mutate:
                mutate()
            try:
                self.assert_same(["structure-report", "--check-input", "--output", str(artifact)], code=code)
            finally:
                subprocess.run(["git", "-C", str(self.root), "checkout", "-q", "--", "."], check=True)
                subprocess.run(["git", "-C", str(self.root), "clean", "-qfd"], check=True)

        fresh = {"schema_version": 1, "reports": [report]}
        check(fresh, 0)
        forged = json.loads(json.dumps(fresh))
        forged["reports"][0]["revision"]["input_digest"] = "forged"
        check(forged, 2)
        check(fresh, 2, lambda: (self.root / "TruthCore" / "Fix" / "Structure.lean").write_text("changed"))
        check(fresh, 2, lambda: (self.root / "TruthCore" / "Fix" / "New.lean").write_text("new"))
        check(fresh, 2, lambda: (self.root / "corpus" / "claims" / "zz.json").write_text("{}"))
        check(fresh, 2, lambda: (self.root / "lean-toolchain").unlink())
        for value in ({}, {"schema_version": 1, "reports": []}, {"schema_version": 2, "reports": [{}]},
                      {"schema_version": 1, "reports": [{}]}, {"schema_version": 1, "reports": [{"revision": {}}]}):
            check(value, 2)
        python, rust = self.run_both(self.root, self.exporter([]),
                                     ["structure-report", "--check-input", "--output", str(self.scratch / "absent.json")])
        self.assertEqual((python.returncode, rust.returncode, rust.stderr), (2, 2, python.stderr))

    def test_producer_provenance(self):
        """Rust records the producing crate's fingerprint and `--check-input`
        rejects an artifact without it (Python's) or from other Rust code;
        Python's checker ignores the field."""
        python, rust = self.assert_same(["structure", "STMT-B"], machine=True)
        report = json.loads(rust.stdout)
        producer = report["revision"]["producer_sha256"]
        self.assertRegex(producer, r"^[0-9a-f]{64}$")
        self.assertNotIn("producer_sha256", python.stdout)
        artifact = self.scratch / "producer.json"
        args = ["structure-report", "--check-input", "--output", str(artifact)]
        for name, value, message in (
            ("stale", "0" * 64, "stale structure artifact producer: truth sources changed"),
            ("missing", None, "structure artifact lacks producer provenance"),
        ):
            with self.subTest(name):
                revision = dict(report["revision"])
                if value is None:
                    del revision["producer_sha256"]
                else:
                    revision["producer_sha256"] = value
                artifact.write_text(json.dumps({"schema_version": 1, "reports": [{**report, "revision": revision}]}))
                python, rust = self.run_both(self.root, self.exporter([]), args)
                self.assertEqual(python.returncode, 0, python.stderr)
                self.assertEqual(rust.returncode, 2, rust.stderr)
                self.assertIn(message, rust.stderr)

    def test_real_first_slice_artifact(self):
        root = corpus.ROOT
        paths = {side: self.scratch / f"{side}-structure.json" for side in ("python", "rust")}
        python, rust = self.run_both(root, FIRST_SLICE_FIXTURE, ["structure-report", "--output", str(paths["python"])],
                                     rust_args=["structure-report", "--output", str(paths["rust"])])
        written = {}
        for side, result in (("python", python), ("rust", rust)):
            self.assertEqual(result.returncode, 0,
                             f"{side}: {result.stderr}\nre-record {FIRST_SLICE_FIXTURE.name} if the first slice changed")
            self.assertEqual(result.stdout, f"wrote {paths[side]}\n")
            written[side] = paths[side].read_bytes()
        self.assertEqual(without_producer(written["rust"].decode()), written["python"].decode())
        artifact = json.loads(written["rust"])
        self.assertEqual(len(artifact["reports"]), 8)
        self.assertTrue(all(report["revision"]["producer_sha256"] for report in artifact["reports"]))
        path = self.scratch / "rust-structure.json"
        self.assert_same(["structure-report", "--check-input", "--output", str(path)], root=root,
                         fixture=FIRST_SLICE_FIXTURE)

    def test_real_statement_text(self):
        for machine in (False, True):
            with self.subTest(machine=machine):
                self.assert_same(["structure", "STMT-MAXIME-ENS-IS-GOD", "--unfold",
                                  "TruthCore.Case.Catholicism.MaximeEnsIsGod"], machine=machine,
                                 root=corpus.ROOT, fixture=FIRST_SLICE_FIXTURE)
