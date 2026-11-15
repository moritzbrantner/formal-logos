"""`truth thickness --base` and `truth orphans --base` against
`corpus.py thickness --base` and `scripts/orphan_summary.py --base`.

Both read a base revision as `frontier-diff` does: a `git archive` extract,
computed by the Rust engine when the revision's `scripts/corpus.py` is the
checkout's, otherwise by that revision's own Python. The fixtures are Git
repositories whose `scripts/corpus.py` is a stub serving a frontier report
precomputed by the real Python `frontier_report`, so both engines run on
them: a base commit with a different stub runs its own Python, one with the
same stub the Rust engine. A pre-migration (readable-id) base is asked for
the root's legacy id; its stub rejects a root it does not know."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
import orphan_summary
from truth_parity.common import U, migrate, humanize, ParityCase
from truth_parity.thickness import thickness_fixture, python_thickness

ROOT_ID = U("statement", "ROOT")
SCRIPTS = Path(__file__).resolve().parents[1]

# A stand-in for a revision's `scripts/corpus.py`: `frontier --json` prints the
# precomputed report, and the module answers `orphan_summary.tree_count`.
STUB = '''"""Fixture corpus.py: serves frontier.json."""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_FRONTIER_ROOT = "%s"


def current_frontier(root, reaching_root, next_steps=True):
    # Like the real walk, a root this corpus does not know reaches nothing.
    if root is not None and root not in {record["id"] for _, record in load_dir("statements")}:
        raise SystemExit(f"unknown root {root}")
    return json.loads((HERE / "frontier.json").read_text())


def refutation_support(arguments, results, relations, root_path):
    support, refuters = json.loads((HERE / "support.json").read_text())
    return set(support), set(refuters)


def load_dir(kind):
    paths = sorted((HERE.parent / "corpus" / kind).glob("*.json"))
    return [(path, json.loads(path.read_text())) for path in paths]


if __name__ == "__main__":
    if sys.argv[1:3] != ["frontier", "--json"]:
        sys.exit("unsupported")
    print(json.dumps(current_frontier(sys.argv[4] if sys.argv[3:4] == ["--root"] else None, False)))
''' % ROOT_ID


def write_state(repo, extra, legacy=False):
    """The thickness fixture plus `extra` (kind, legacy record) records, in
    uuid identity (readable ids when `legacy`), as `repo`'s corpus, and its
    Python frontier report as `scripts/frontier.json`."""
    with tempfile.TemporaryDirectory() as temporary:
        state = Path(temporary)
        thickness_fixture(state, convert=False)
        for kind, record in extra:
            (state / "corpus" / kind / f"{record['id']}.json").write_text(json.dumps(record))
        if not legacy:
            migrate(state)
        shutil.rmtree(repo / "corpus", ignore_errors=True)
        shutil.copytree(state / "corpus", repo / "corpus")
        if not (repo / "Fixture").exists():
            shutil.copytree(state / "Fixture", repo / "Fixture")
    records = {kind: [json.loads(path.read_text()) for path in sorted((repo / "corpus" / kind).glob("*.json"))]
               for kind in ("statements", "arguments", "results", "relations", "claims")}
    saved = corpus.ROOT
    corpus.ROOT = repo
    try:
        flags = corpus.transcription_flags(records["results"], records["arguments"], records["statements"])
    finally:
        corpus.ROOT = saved
    report = corpus.frontier_report(records["statements"], records["arguments"], records["results"],
                                    records["relations"], root="ROOT" if legacy else ROOT_ID, transcription=flags,
                                    claims=records["claims"])
    (repo / "scripts" / "frontier.json").write_text(json.dumps(report))
    records["results"] = [json.loads(path.read_text()) for path in sorted((repo / "corpus" / "results").glob("*.json"))]
    support, refuters = corpus.refutation_support(records["arguments"], records["results"], records["relations"],
                                                  set(report["reaching_root_statements"]))
    (repo / "scripts" / "support.json").write_text(json.dumps([sorted(support), sorted(refuters)]))


EXTRA_DERIVATION = [  # A second verified derivation of A, so A is multiply derived.
    ("arguments", {"id": "ARG-A2", "premise_statement_ids": ["C"], "conclusion_statement_id": "A",
                   "inference_ids": ["INF"], "meaning": "ARG-A2"}),
    ("results", {"id": "RES-A2", "argument_id": "ARG-A2", "challenge_module": "Fixture.Challenge",
                 "solution_module": "Fixture.Solution", "theorem": "Fixture.none",
                 "comparator_config": "c.json", "status": "verified"}),
]
EXTRA_IDLE = [  # A verified result whose conclusion does not reach the root.
    ("statements", {"id": "IDLE", "paraphrase": "IDLE", "definition_ids": []}),
    ("arguments", {"id": "ARG-IDLE", "premise_statement_ids": ["U"], "conclusion_statement_id": "IDLE",
                   "inference_ids": ["INF"], "meaning": "ARG-IDLE"}),
    ("results", {"id": "RES-IDLE", "argument_id": "ARG-IDLE", "challenge_module": "Fixture.Challenge",
                 "solution_module": "Fixture.Solution", "theorem": "Fixture.none",
                 "comparator_config": "c.json", "status": "verified"}),
]


def revision_fixture(repo):
    """Commits LEGACY (readable ids, before the uuid migration; its own
    Python is asked for the root's legacy id), OLD (the fixture; a stub with other bytes, so its own Python
    runs) and SAME (plus a derivation; the checkout's stub, so the Rust engine
    runs), and a working tree adding a disconnected result."""
    def git(*args):
        subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)

    git("init", "-q")
    git("config", "user.email", "fixture@example.invalid")
    git("config", "user.name", "fixture")
    (repo / "scripts").mkdir()
    (repo / "docs" / "notes").mkdir(parents=True)
    (repo / "docs" / "notes" / "README.md").write_text("fixture\n")
    (repo / "scripts" / "corpus.py").write_text(STUB.replace(ROOT_ID, "ROOT") + "\ndel refutation_support\n")
    write_state(repo, [], legacy=True)
    git("add", "-A")
    git("commit", "-q", "-m", "legacy")
    git("tag", "LEGACY")
    # Older rules: no refutation support (orphan_summary's `hasattr` branch).
    (repo / "scripts" / "corpus.py").write_text(STUB + "\ndel refutation_support\n")
    write_state(repo, [])
    git("add", "-A")
    git("commit", "-q", "-m", "old")
    git("tag", "OLD")
    (repo / "scripts" / "corpus.py").write_text(STUB)
    write_state(repo, EXTRA_DERIVATION)
    git("add", "-A")
    git("commit", "-q", "-m", "same")
    git("tag", "SAME")
    write_state(repo, EXTRA_DERIVATION + EXTRA_IDLE)
    # The checkout's uuid migration, which converts a pre-migration base.
    for name in ("migrate_uuid.py", "corpus_ids.py", "uuid_labels.py"):
        shutil.copy(SCRIPTS / name, repo / "scripts" / name)


class TruthRevisionParity(ParityCase):
    """`thickness --base` and `orphans --base` against the Python reports."""

    def truth(self, *args, cwd=None):
        return subprocess.run([self.binary, *args], cwd=cwd or corpus.ROOT,
                              capture_output=True, text=True, check=False)

    def run_truth(self, *args, cwd=None):
        result = self.truth(*args, cwd=cwd)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def json_truth(self, *args):
        actual = json.loads(self.run_truth("--json", *args))
        self.assertTrue(actual.pop("input_identity").startswith("fnv1a64:"))
        return actual

    @staticmethod
    def available(revision):
        return subprocess.run(["git", "-C", str(corpus.ROOT), "rev-parse", "--verify", "--quiet",
                               f"{revision}^{{commit}}"], capture_output=True, check=False).returncode == 0

    @staticmethod
    def same_rules(revision, root=None):
        root = root or corpus.ROOT
        at = subprocess.run(["git", "-C", str(root), "rev-parse", f"{revision}:scripts/corpus.py"],
                            capture_output=True, text=True, check=False).stdout.strip()
        current = subprocess.run(["git", "-C", str(root), "hash-object", "scripts/corpus.py"],
                                 capture_output=True, text=True, check=True).stdout.strip()
        return at == current

    def real_bases(self):
        """HEAD (always fetched; the Rust engine unless corpus.py is edited),
        HEAD~1 and the parent of the last corpus.py change (its own Python),
        when fetched, and any in TRUTH_PARITY_BASES."""
        last = subprocess.run(["git", "-C", str(corpus.ROOT), "log", "-1", "--format=%H", "--",
                               "scripts/corpus.py"], capture_output=True, text=True, check=False).stdout.strip()
        bases = ["HEAD", "HEAD~1", *([f"{last}~1"] if last else []),
                 *os.environ.get("TRUTH_PARITY_BASES", "").split()]
        return [base for base in bases if self.available(base)]

    def test_real_thickness_base(self):
        root = corpus.DEFAULT_FRONTIER_ROOT
        frontier = corpus.current_frontier(root, False, next_steps=False)
        head = corpus.thickness_report(frontier, [r for _, r in corpus.load_dir("arguments")],
                                       [r for _, r in corpus.load_dir("results")])
        for base in self.real_bases():
            with self.subTest(base=base):
                delta = corpus.thickness_delta(corpus.revision_thickness(base, root), head)
                actual = self.json_truth("thickness", "--base", base)
                engines = actual.pop("engines")
                self.assertEqual(engines, {"base": "rust" if self.same_rules(base) else "python", "head": "rust"})
                self.assertEqual(actual, {"report": head, "delta": delta})
                self.assertEqual(self.run_truth("thickness", "--base", base),
                                 humanize(corpus.format_thickness(head, delta)) + "\n")

    def test_real_orphans_base(self):
        head = orphan_summary.tree_count(corpus.ROOT)
        bases = self.real_bases()
        for base in bases:
            with self.subTest(base=base):
                previous = orphan_summary.base_count(corpus.ROOT, base)
                self.assertEqual(self.run_truth("orphans", "--base", base),
                                 orphan_summary.summary(base, head, previous) + "\n")
                actual = self.json_truth("orphans", "--base", base)
                self.assertEqual((actual["base_count"], actual["head_count"], actual["delta"]),
                                 (previous, head, head - previous))
                self.assertEqual(actual["engines"],
                                 {"base": "rust" if self.same_rules(base) else "python", "head": "rust"})
        # The CI caller itself, byte for byte, on the first base.
        python = subprocess.run([sys.executable, str(SCRIPTS / "orphan_summary.py"), "--base", bases[0]],
                                cwd=corpus.ROOT, capture_output=True, text=True, check=False)
        rust = self.truth("orphans", "--base", bases[0])
        self.assertEqual((rust.returncode, rust.stdout), (python.returncode, python.stdout))

    def test_real_errors(self):
        # A revision that does not exist: thickness fails as Python's
        # CorpusError (exit 2), orphans reports the base unavailable (exit 0).
        bad = "no-such-revision-b4"
        python = subprocess.run([sys.executable, str(SCRIPTS / "corpus.py"), "thickness", "--base", bad],
                                cwd=corpus.ROOT, capture_output=True, text=True, check=False)
        rust = self.truth("thickness", "--base", bad)
        self.assertEqual((rust.returncode, rust.stdout, rust.stderr),
                         (python.returncode, python.stdout, python.stderr))
        self.assertEqual(rust.returncode, 2)
        self.assertTrue(rust.stderr.startswith(f"corpus error: cannot archive revision {bad}: "), rust.stderr)
        python = subprocess.run([sys.executable, str(SCRIPTS / "orphan_summary.py"), "--base", bad],
                                cwd=corpus.ROOT, capture_output=True, text=True, check=False)
        rust = self.truth("orphans", "--base", bad)
        self.assertEqual((rust.returncode, rust.stdout), (python.returncode, python.stdout))
        self.assertEqual(rust.returncode, 0)
        self.assertIn("| unavailable |", rust.stdout)
        self.assertTrue(rust.stderr.startswith("Orphan baseline unavailable: "), rust.stderr)
        self.assertTrue(python.stderr.startswith("Orphan baseline unavailable: "), python.stderr)
        unavailable = json.loads(self.truth("--json", "orphans", "--base", bad).stdout)
        self.assertEqual((unavailable["base_count"], unavailable["delta"], unavailable["engines"]["base"]),
                         (None, None, None))
        self.assertIn(bad, unavailable["base_error"])
        # --queue with --base: Python's CorpusError, also after the head report.
        python = subprocess.run([sys.executable, str(SCRIPTS / "corpus.py"), "thickness", "--queue", "--base",
                                 "HEAD"], cwd=corpus.ROOT, capture_output=True, text=True, check=False)
        rust = self.truth("thickness", "--queue", "--base", "HEAD")
        self.assertEqual((rust.returncode, rust.stdout, rust.stderr),
                         (python.returncode, python.stdout, python.stderr))

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            revision_fixture(repo)
            args = ["--root", str(repo), "--frontier-root", "ROOT"]
            head = python_thickness(repo, False)["report"]
            saved = corpus.ROOT
            corpus.ROOT = repo
            try:
                bases = {base: corpus.revision_thickness(base, ROOT_ID) for base in ("LEGACY", "OLD", "SAME")}
            finally:
                corpus.ROOT = saved
            head_count = orphan_summary.tree_count(repo)
            for base, engine in (("LEGACY", "python"), ("OLD", "python"), ("SAME", "rust")):
                with self.subTest(base=base):
                    delta = corpus.thickness_delta(bases[base], head)
                    actual = self.json_truth(*args, "thickness", "--base", base)
                    self.assertEqual(actual.pop("engines"), {"base": engine, "head": "rust"})
                    self.assertEqual(actual, {"report": head, "delta": delta})
                    self.assertEqual(self.run_truth(*args, "thickness", "--base", base),
                                     humanize(corpus.format_thickness(head, delta), repo) + "\n")
                    previous = orphan_summary.base_count(repo, base)
                    # Python names the default root whatever the corpus; Rust the root used.
                    expected = orphan_summary.summary(base, head_count, previous).replace(
                        "Root: STMT-CATHOLICISM-TRUE.", "Root: ROOT.")
                    self.assertEqual(self.run_truth(*args, "orphans", "--base", base), expected + "\n")
                    counts = self.json_truth(*args, "orphans", "--base", base)
                    self.assertEqual((counts["base_count"], counts["head_count"], counts["engines"]["base"]),
                                     (previous, head_count, engine))
            # The fixture exercises what it claims to: OLD lacks the second
            # derivation of A, and only the working tree has the idle result.
            delta = corpus.thickness_delta(bases["OLD"], head)
            self.assertEqual(delta["changed"], {U("statement", "A"): {"added": [U("argument", "ARG-A2")],
                                                                     "removed": []}})
            self.assertEqual(corpus.thickness_delta(bases["SAME"], head)["changed"], {})
            self.assertEqual(head_count - orphan_summary.base_count(repo, "SAME"), 1)

    def test_usage(self):
        for args in (["thickness", "--head", "HEAD"], ["orphans", "--base", "HEAD", "--senses"],
                     ["orphans", "--by", "module", "--base", "HEAD"], ["status", "--base", "HEAD"],
                     ["frontier", "--base", "HEAD"]):
            result = self.truth("--json", *args)
            self.assertEqual(result.returncode, 2, args)
