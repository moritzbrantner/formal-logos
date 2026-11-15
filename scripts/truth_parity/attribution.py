"""`truth attribution-check` against `corpus.py attribution-check` (#989,
#954 slice B5).

Fixture checkouts are Git repositories whose working tree changes claims,
statements and passages against a base commit; both sides read the same tree.
The cases follow `test_attribution_check.py`: a missing, malformed or
recorded attribution, cached, missing and stale passage text, a
bibliographic span, selection by stable id (moved files), statement
paraphrase and passage changes, clipping, a pre-migration (readable-id) base,
errors (an unresolvable passage, an unknown base) and `--materialize`, which
both sides delegate to the fixture's stub `scripts/source_evidence.py
materialize` (Python patched to the same stub behaviour). The real corpus is
compared against a few base revisions. Text is compared byte for byte
(stdout, stderr and exit code); `--json` carries the same selection and
problems."""
import contextlib
import io
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from unittest import mock

import attribution_check as ac
import corpus
import source_evidence as se
from truth_parity.common import U, ParityCase

GOOD = "The passage states that whatever is changed in any way is in potency, which is the premise."
UUID = r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}"
CACHED = "Omne quod mutatur est in potentia.\r\nSecond line.  \n"
SOURCE = U("source", "SRC")
BOOK = U("source", "BOOK")
TEXT = U("passage", "TEXT-1")
BIB = U("passage", "BIB-1")
STMT = U("statement", "STMT-P")
STMT_Q = U("statement", "STMT-Q")
CLAIM = U("claim", "C")
CLAIM_Q = U("claim", "CQ")

# A stand-in for `scripts/source_evidence.py materialize`: a passage named in
# `fail.json` fails with its message, any other is written to the cache.
STUB = '''import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
passage = sys.argv[2]
failures = json.loads((ROOT / "fail.json").read_text()) if (ROOT / "fail.json").is_file() else {}
if passage in failures:
    print(f"source evidence error: {failures[passage]}", file=sys.stderr)
    sys.exit(2)
cache = ROOT / ".cache" / "truth-core" / "sources"
cache.mkdir(parents=True, exist_ok=True)
(cache / f"{passage}.txt").write_text("Freshly materialized text.\\n")
print(f"materialized {passage}")
'''


def statement(legacy, paraphrase):
    return {"id": U("statement", legacy), "label": legacy.lower(), "paraphrase": paraphrase}


def claim(legacy="C", **extra):
    record = {"id": U("claim", legacy), "label": f"claim {legacy}", "statement_id": STMT, "source_id": SOURCE,
              "locator": "I q.9 a.1 co.", "interpretation": "reading", "status": "accepted"}
    record.update(extra)
    return record


def passages(text_extra=None):
    text = {"snapshot": {"source_id": SOURCE, "edition_urn": "urn:cts:x.y.z", "repository": "org/repo",
                         "revision": "0" * 40, "path": "a.xml", "git_blob_sha": "1" * 40,
                         "source_url": f"https://raw.example.org/org/repo/{'0' * 40}/a.xml",
                         "language": "lat", "license": "CC0"},
            "passages": [{"id": TEXT, "label": "text one", "locator": "I q.9 a.1",
                          "claim_locator_prefixes": ["I q.9 a.1"], "cts_path": [{"subtype": "q", "n": "9"}],
                          **(text_extra or {})}]}
    book = {"snapshot": {"source_id": BOOK, "kind": "bibliographic_span", "author": "A", "title": "T",
                         "publisher": "P", "year": 2000, "isbn": "9780306406157", "language": "en",
                         "why_bibliographic": "copyrighted, no pinnable witness exists"},
            "passages": [{"id": BIB, "label": "book pages", "locator": "pp. 1-2", "claim_locator_prefixes": ["pp. 1"],
                          "pages": "1-2"}]}
    return {"text.json": text, "book.json": book}


def write(root, relative, value):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n" if not isinstance(value, str) else value)


def git(root, *args):
    subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)


def base_tree(root):
    """The base commit: sources, two statements, the passages and claim CQ."""
    write(root, "corpus/sources/src.json", {"id": SOURCE, "label": "source", "kind": "text", "author": "Thomas",
                                            "work": "W", "citation_system": "q/a", "work_urn": "urn:cts:x.y",
                                            "catalog_url": "https://example.org"})
    write(root, "corpus/sources/book.json", {"id": BOOK, "label": "book", "kind": "book", "author": "A", "work": "T",
                                             "citation_system": "pages", "work_urn": "urn:isbn:9780306406157",
                                             "catalog_url": "https://example.org/b"})
    write(root, "corpus/statements/p.json", statement("STMT-P", "Whatever is changed is in potency."))
    write(root, "corpus/statements/q.json", statement("STMT-Q", "Something is moved."))
    for name, manifest in passages().items():
        write(root, f"corpus/passages/{name}", manifest)
    write(root, "corpus/claims/cq.json", claim("CQ", statement_id=STMT_Q, attribution=GOOD))
    write(root, ".gitignore", ".cache/\n")
    write(root, f".cache/truth-core/sources/{TEXT}.txt", CACHED)
    write(root, "scripts/source_evidence.py", STUB)
    git(root, "init", "-q")
    git(root, "add", "-A")
    git(root, "-c", "user.name=t", "-c", "user.email=t@example.org", "commit", "-q", "-m", "base")


@contextlib.contextmanager
def checkout(root):
    """`corpus.py` and the attribution check reading the checkout at `root`;
    `--materialize` runs the fixture's stub as Rust does."""
    saved = (corpus.ROOT, corpus.CORPUS, corpus._ALIASES, ac.ROOT, se.ROOT, se.CORPUS, se.PASSAGES, se.CACHE)

    def materialize(passage_id, output):
        result = subprocess.run(["python3", "scripts/source_evidence.py", "materialize", passage_id], cwd=root,
                                capture_output=True, text=True)
        if result.returncode:
            raise se.SourceEvidenceError(result.stderr.strip().removeprefix("source evidence error: "))
        return 0

    corpus.ROOT, corpus.CORPUS, corpus._ALIASES = root, root / "corpus", None
    ac.ROOT, se.ROOT, se.CORPUS, se.PASSAGES = root, root, root / "corpus", root / "corpus" / "passages"
    se.CACHE = root / ".cache" / "truth-core" / "sources"
    try:
        with mock.patch.object(se, "materialize", side_effect=materialize):
            yield
    finally:
        (corpus.ROOT, corpus.CORPUS, corpus._ALIASES, ac.ROOT, se.ROOT, se.CORPUS, se.PASSAGES,
         se.CACHE) = saved


def python(args, root=None):
    """`corpus.py attribution-check ARGS`: exit code, stdout and stderr."""
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.ExitStack() as stack:
        if root is not None:
            stack.enter_context(checkout(root))
        stack.enter_context(contextlib.redirect_stdout(stdout))
        stack.enter_context(contextlib.redirect_stderr(stderr))
        code = corpus.main_with(["attribution-check", *args])
    return code, stdout.getvalue(), stderr.getvalue()


class TruthAttributionParity(ParityCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        base_tree(self.root)

    def rust(self, args, root=None, machine=False):
        root = root or self.root
        result = subprocess.run([self.binary, "--root", str(root), *(["--json"] if machine else []),
                                 "attribution-check", *args], cwd=root, capture_output=True, text=True)
        return result.returncode, result.stdout, result.stderr

    def compare(self, *args, root=None, code=None):
        """Text parity on `root` (the fixture by default) and the `--json`
        selection and problems; returns Python's stdout."""
        root = root or self.root
        expected = python(list(args), root=None if root == corpus.ROOT else root)
        self.assertEqual(self.rust(list(args), root=root), expected)
        if code is not None:
            self.assertEqual(expected[0], code, expected)
        machine_code, machine, _ = self.rust(list(args), root=root, machine=True)
        self.assertEqual(machine_code, expected[0])
        if expected[0] != 2:
            report = json.loads(machine)
            problems = [line[2:] for line in expected[2].splitlines() if line.startswith("  ")]
            self.assertEqual(report["problems"], problems)
            self.assertEqual(report["ok"], not problems)
            headers = [line for line in expected[1].splitlines() if line.startswith("== ")]
            self.assertEqual(len(report["claims"]), len(headers))
            for entry, header in zip(report["claims"], headers):
                self.assertIn(entry["claim_id"][:8], header)
                # Text names records `label [uuid8]`; JSON keeps the uuids.
                reason = re.sub(UUID, lambda m: f"__{m.group(0)[:8]}__", entry["reason"])
                pattern = re.escape(f"({reason}) -> ")
                self.assertRegex(header, re.sub(r"__([0-9a-f]{8})__", r".*\\[\1\\]", pattern))
        return expected[1]

    def test_no_changed_claims(self):
        out = self.compare("--base", "HEAD", code=0)
        self.assertIn("no new or changed stating claim since HEAD", out)

    def test_missing_attribution_fails_beside_cached_text(self):
        write(self.root, "corpus/claims/c.json", claim())
        out = self.compare("--base", "HEAD", code=1)
        self.assertIn("premise: Whatever is changed is in potency.", out)
        self.assertIn("Omne quod mutatur est in potentia.", out)
        self.assertIn("attribution: MISSING", out)

    def test_recorded_and_malformed_attribution(self):
        write(self.root, "corpus/claims/c.json", claim(attribution=GOOD))
        self.compare("--base", "HEAD", code=0)
        write(self.root, "corpus/claims/c.json", claim(attribution="A citation is enough."))
        self.compare("--base", "HEAD", code=1)
        write(self.root, "corpus/claims/c.json", claim(attribution=7))
        self.compare("--base", "HEAD", code=1)

    def test_clipping(self):
        write(self.root, "corpus/claims/c.json", claim(attribution=GOOD))
        for limit in ("0", "1", "10", "-3", "6000"):
            with self.subTest(limit=limit):
                self.compare("--base", "HEAD", "--max-chars", limit, code=0)

    def test_offline_without_cache_is_not_checked(self):
        (self.root / ".cache" / "truth-core" / "sources" / f"{TEXT}.txt").unlink()
        write(self.root, "corpus/claims/c.json", claim(attribution=GOOD))
        self.assertIn("passage text: NOT CHECKED", self.compare("--base", "HEAD", code=0))

    def test_changed_passage_selects_its_claims_and_hides_stale_text(self):
        write(self.root, "corpus/passages/text.json", passages({"incipit": "Omne"})["text.json"])
        write(self.root, "corpus/claims/cq.json", claim("CQ", statement_id=STMT_Q, attribution=GOOD))
        out = self.compare("--base", "HEAD", code=0)
        self.assertRegex(out, r"\(passage .*\[[0-9a-f]{8}\] changed\) -> ")
        self.assertNotIn("Omne quod mutatur", out)

    def test_label_only_passage_change_selects_nothing(self):
        manifest = passages()["text.json"]
        manifest["passages"][0]["label"] = "renamed"
        write(self.root, "corpus/passages/text.json", manifest)
        self.compare("--base", "HEAD", code=0)

    def test_bibliographic_claim(self):
        write(self.root, "corpus/claims/c.json", claim(source_id=BOOK, locator="pp. 1", witness="bibliographic",
                                                       attribution=GOOD))
        self.assertIn("read A, T (P, 2000; ISBN 9780306406157), pp. 1-2", self.compare("--base", "HEAD", code=0))

    def test_selection_by_stable_id(self):
        git(self.root, "mv", "corpus/claims/cq.json", "corpus/claims/moved.json")
        self.compare("--base", "HEAD", code=0)
        write(self.root, "corpus/claims/moved.json", claim("CQ", statement_id=STMT_Q, interpretation="broader",
                                                           attribution=GOOD))
        self.compare("--base", "HEAD", code=0)
        write(self.root, "corpus/claims/moved.json", claim("CQ", statement_id=STMT_Q))
        self.compare("--base", "HEAD", code=1)

    def test_renamed_statement_with_new_paraphrase_selects_its_claims(self):
        (self.root / "corpus/statements/q.json").unlink()
        write(self.root, "corpus/statements/q2.json", statement("STMT-Q", "Something is moved by another."))
        self.compare("--base", "HEAD", code=0)

    def test_pre_migration_base(self):
        """A base with readable ids is compared under the uuid ids."""
        legacy = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, legacy)
        write(legacy, "corpus/claims/cq.json", {"id": "CQ", "statement_id": "STMT-Q", "source_id": "SRC",
                                                 "locator": "I q.9 a.1 co.", "interpretation": "reading",
                                                 "attribution": GOOD})
        write(legacy, "corpus/statements/q.json", {"id": "STMT-Q", "paraphrase": "Something is moved."})
        manifest = passages()["text.json"]
        manifest["snapshot"]["source_id"] = "SRC"
        manifest["passages"][0]["id"] = "TEXT-1"
        del manifest["passages"][0]["label"]
        write(legacy, "corpus/passages/text.json", manifest)
        branch = subprocess.run(["git", "-C", str(self.root), "symbolic-ref", "--short", "HEAD"], check=True,
                                capture_output=True, text=True).stdout.strip()
        git(self.root, "checkout", "-q", "--orphan", "legacy")
        git(self.root, "rm", "-rq", "--cached", ".")
        for path in legacy.rglob("*.json"):
            relative = path.relative_to(legacy)
            subprocess.run(["git", "-C", str(self.root), "update-index", "--add", "--cacheinfo",
                            f"100644,{self.blob(path)},{relative}"], check=True)
        git(self.root, "-c", "user.name=t", "-c", "user.email=t@example.org", "commit", "-q", "-m", "legacy")
        git(self.root, "checkout", "-q", "-f", branch)
        self.compare("--base", "legacy", code=0)

    def blob(self, path):
        return subprocess.run(["git", "-C", str(self.root), "hash-object", "-w", str(path)], check=True,
                              capture_output=True, text=True).stdout.strip()

    def test_errors(self):
        write(self.root, "corpus/claims/c.json", claim(locator="II q.1", attribution=GOOD))
        self.compare("--base", "HEAD", code=2)
        (self.root / "corpus/claims/c.json").unlink()
        self.compare("--base", "no-such-revision", code=2)

    def test_materialize(self):
        write(self.root, "corpus/claims/c.json", claim(attribution=GOOD))
        self.assertIn("Freshly materialized text.", self.compare("--base", "HEAD", "--materialize", code=0))
        write(self.root, "fail.json", {TEXT: "byte drift"})
        self.assertIn("cannot materialize: byte drift", self.compare("--base", "HEAD", "--materialize", code=1))
        write(self.root, "corpus/claims/c.json", claim(source_id=BOOK, locator="pp. 1", witness="bibliographic",
                                                       attribution=GOOD))
        self.compare("--base", "HEAD", "--materialize", code=0)

    def test_real_corpus_against_base_revisions(self):
        compared = 0
        for revision in ("HEAD", "HEAD~1", "HEAD~25", "origin/main~40"):
            if subprocess.run(["git", "-C", str(corpus.ROOT), "rev-parse", "--verify", "-q", f"{revision}^{{commit}}"],
                              capture_output=True).returncode:
                continue
            with self.subTest(revision=revision):
                self.compare("--base", revision, "--max-chars", "2000", root=corpus.ROOT)
                compared += 1
        self.assertGreater(compared, 0)
