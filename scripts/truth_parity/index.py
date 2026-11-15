"""`truth index` against `scripts/research_index.py` (#954 slice B7): every
table of the projection row for row, and the query subcommands' JSON, on the
real corpus and on the `test_research_index.py` fixture; the stale-index
refresh, atomic failed rebuild and error exit codes.

Ranking: both sides run the same FTS5 `bm25` over the same rows, inserted in
the same order, so equal ranks keep the same (insertion) order; the search
comparison is exact, ties included. Digests differ by design (Rust binds the
index to its own input identity, Python hashes its script), so the
`metadata` digest row is the one row not compared."""
import json
import sqlite3
import subprocess
import tempfile
from contextlib import closing
from pathlib import Path

import corpus
import research_index
from truth_parity import golden
from truth_parity.common import ParityCase

TABLES = {
    "records": "SELECT key,id,kind,path,body FROM records ORDER BY rowid",
    "refs": "SELECT owner,target FROM refs ORDER BY owner,target",
    "arguments": "SELECT id,signature,conclusion FROM arguments ORDER BY id",
    "source_files": "SELECT path,content FROM source_files ORDER BY path",
    "search": "SELECT rowid,id,text FROM search ORDER BY rowid",
    "schema": "SELECT value FROM metadata WHERE key='schema'",
}

SEARCHES = ["common nature", "cause", "act potency", "god", "necessary being", "Aquinas", 'say "hello"',
            "first mover", "zzzz-no-such-word"]


def tables(path):
    with closing(sqlite3.connect(path)) as db:
        return {name: db.execute(query).fetchall() for name, query in TABLES.items()}


class TruthIndexParity(ParityCase):
    """The Rust projection and queries against Python's."""

    def truth(self, root, *args, code=0):
        result = subprocess.run([self.binary, "--root", str(root), *args], capture_output=True, check=False)
        self.assertEqual(result.returncode, code, (args, result.stderr.decode()))
        return result.stdout, result.stderr.decode()

    def expect(self, root, args, value):
        """A golden case (fixture checkouts only): `index ARGS` in text and
        `--json` prints Python's `value`. The database under `.cache/` is not
        recorded: Rust builds it on the first query."""
        if root != corpus.ROOT:
            for machine in ([], ["--json"]):
                golden.record(self, ["--root", root, *machine, "index", *args], root=root, code=0,
                              stdout_json=value, exclude=(".cache",))

    def truth_json(self, root, *args):
        value = json.loads(self.truth(root, "--json", "index", *args)[0])
        text = json.loads(self.truth(root, "index", *args)[0])
        self.assertEqual(text, value, args)
        return value

    def python_index(self, root, directory):
        path = Path(directory) / "research-index.sqlite"
        research_index.build(root, path)
        return path, research_index.connect(root, path)

    def compare_queries(self, root, db, shows, cases=(), export_stride=1):
        """Every query subcommand of both sides on the checkout at `root`."""
        for words in SEARCHES:
            for limit in (20, 3):
                expression = " AND ".join('"' + word.replace('"', '""') + '"' for word in words.split())
                expected = [dict(row) for row in db.execute(
                    "SELECT r.id,r.kind,r.path FROM search JOIN records r ON r.key=search.id "
                    "WHERE search MATCH ? ORDER BY rank LIMIT ?", (expression, limit))]
                self.expect(root, ["search", words, "--limit", str(limit)], expected)
                self.assertEqual(self.truth_json(root, "search", words, "--limit", str(limit)), expected,
                                 (words, limit))
        for token in shows:
            self.expect(root, ["show", token], research_index.lookup(db, token))
            self.assertEqual(self.truth_json(root, "show", token), research_index.lookup(db, token), token)
        self.expect(root, ["duplicates"], research_index.duplicates(db))
        self.assertEqual(self.truth_json(root, "duplicates"), research_index.duplicates(db))
        expected = {"mode": "registered inventory, not certified progress",
                    "records_by_kind": {row[0]: row[1] for row in db.execute(
                        "SELECT kind,count(*) FROM records GROUP BY kind")},
                    "exact_duplicate_argument_groups": len(research_index.duplicates(db))}
        self.expect(root, ["summary"], expected)
        self.assertEqual(self.truth_json(root, "summary"), expected)
        self.expect(root, ["parity"], research_index.parity(db, root))
        self.assertEqual(self.truth_json(root, "parity"), research_index.parity(db, root))
        for path in sorted(row[0] for row in db.execute("SELECT path FROM source_files"))[::export_stride]:
            if root != corpus.ROOT:
                golden.record(self, ["--root", root, "index", "export", path], root=root, code=0,
                              stdout=(root / path).read_text(), exclude=(".cache",))
            self.assertEqual(self.truth(root, "index", "export", path)[0], (root / path).read_bytes(), path)
        for case_id, left, right in cases:
            argv = ["--case", case_id]
            for premise in left:
                argv += ["--premise", premise]
            self.expect(root, ["bundle", *argv], research_index.bundle(db, case_id, left))
            self.assertEqual(self.truth_json(root, "bundle", *argv), research_index.bundle(db, case_id, left),
                             case_id)
            argv = ["--case", case_id]
            for premise in left:
                argv += ["--left", premise]
            for premise in right:
                argv += ["--right", premise]
            self.expect(root, ["compare", *argv], research_index.compare(db, case_id, left, right))
            self.assertEqual(self.truth_json(root, "compare", *argv),
                             research_index.compare(db, case_id, left, right), case_id)

    def test_real_corpus(self):
        root = corpus.ROOT
        with tempfile.TemporaryDirectory() as directory:
            python_path, db = self.python_index(root, directory)
            db.row_factory = sqlite3.Row
            self.truth(root, "index", "build")
            self.assertEqual(tables(root / ".cache/truth-index.sqlite"), tables(python_path))
            shows = []
            for kind in ("statements", "arguments", "results", "passages", "definitions", "attempts", "lexicon"):
                ids = [row[0] for row in db.execute("SELECT id FROM records WHERE kind=? ORDER BY id", (kind,))]
                shows += ids[:: max(1, len(ids) // 4)][:4]
            cases = []
            for row in db.execute("SELECT body FROM records WHERE kind='configurations' ORDER BY id"):
                case = json.loads(row[0])
                applications = sorted(case.get("semantics", {}).get("applications", {}))
                cases.append((case["id"], applications[:2], applications[-2:]))
            self.assertGreaterEqual(len(cases), 5)
            self.compare_queries(root, db, shows, cases, export_stride=997)
            db.close()
        # Errors: Python exits 1 with `research index: MESSAGE`; Rust exits 1 too.
        for args, message in ((["show", "NO-SUCH-RECORD"], "unknown record: NO-SUCH-RECORD"),
                              (["export", "corpus/none.json"], "unknown indexed path: corpus/none.json"),
                              (["search", " "], "search requires at least one word"),
                              (["bundle", "--case", shows[0]], "bundle requires a configuration case ID"),
                              (["bundle", "--case", cases[0][0], "--premise", "NO-SUCH"],
                               "statements outside selected profile: NO-SUCH")):
            self.assertIn(message, self.truth(root, "index", *args, code=1)[1], args)
        for args in (["nonsense"], ["show"], ["search"], ["build", "--premise", "X"], ["summary", "--limit", "3"]):
            self.truth(root, "index", *args, code=2)
        self.truth(root, "related", shows[0], "--left", "X", code=2)

    def test_legacy_ids_and_labels_resolve(self):
        statement = next(record for _, record in corpus.load_dir("statements") if record.get("legacy_id"))
        by_id = self.truth_json(corpus.ROOT, "show", statement["id"])
        self.assertEqual(self.truth_json(corpus.ROOT, "show", statement["legacy_id"]), by_id)
        self.assertEqual(self.truth_json(corpus.ROOT, "show", "statements:" + statement["label"]), by_id)
        # A label may contain a colon; `statements:` prefixes premise tokens.
        case = next(record for _, record in corpus.load_dir("configurations")
                    if ":" in record.get("label", "") and record.get("semantics", {}).get("applications"))
        premise = sorted(case["semantics"]["applications"])[0]
        expected = self.truth_json(corpus.ROOT, "bundle", "--case", case["id"], "--premise", premise)
        self.assertEqual(self.truth_json(corpus.ROOT, "bundle", "--case", case["label"],
                                         "--premise", "statements:" + premise), expected)

    def fixture(self, directory):
        root = Path(directory)

        def put(kind, value):
            (root / "corpus" / kind).mkdir(parents=True, exist_ok=True)
            (root / "corpus" / kind / (value["id"] + ".json")).write_text(json.dumps(value))

        put("statements", {"id": "S", "paraphrase": "distinctive causal explanation", "definition_ids": ["DEF-X"]})
        put("statements", {"id": "T", "paraphrase": "another commitment"})
        put("arguments", {"id": "A", "premise_statement_ids": ["S"], "conclusion_statement_id": "T"})
        put("arguments", {"id": "B", "premise_statement_ids": ["S"], "conclusion_statement_id": "T"})
        put("results", {"id": "A", "argument_id": "A", "theorem": "Fix.a", "status": "verified"})
        put("attempts", {"id": "ATTEMPT-X", "statement_ids": ["S"], "outcome": "blocked"})
        put("configurations", {"id": "CONFIG-X", "seed_statement_id": "S", "implication_result_ids": ["A"],
                               "semantics": {"applications": {"S": [], "T": []}},
                               "configurations": [{"id": "base", "statement_ids": ["S"]}]})
        (root / "corpus/passages").mkdir()
        (root / "corpus/passages/collection.json").write_text(json.dumps(
            {"snapshot": {"source_id": "SOURCE", "revision": "pinned"}, "notes": "shared",
             "passages": [{"id": "PASSAGE-1", "locator": "chapter 1"}, {"id": "PASSAGE-2", "locator": "chapter 2"}]}))
        (root / "corpus/schema.json").write_bytes(b'{ "title": "schema without an entity ID", "x": 91.0 }\n')
        return root, put

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as directory, tempfile.TemporaryDirectory() as python_directory:
            root, put = self.fixture(directory)
            python_path, db = self.python_index(root, python_directory)
            db.row_factory = sqlite3.Row
            self.truth(root, "index", "build")
            index = root / ".cache/truth-index.sqlite"
            self.assertEqual(tables(index), tables(python_path))
            self.compare_queries(root, db, ["S", "T", "results:A", "arguments:A", "PASSAGE-1", "ATTEMPT-X"],
                                 [("CONFIG-X", ["S"], ["T"]), ("CONFIG-X", ["S", "T"], [])])
            db.close()
            self.assertIn("ambiguous ID; use kind:ID, for example results:A",
                          self.truth(root, "index", "show", "A", code=1)[1])
            # Stale: Python's query commands reject it; Rust rebuilds before answering.
            put("statements", {"id": "U", "paraphrase": "newly indexed sentence"})
            with self.assertRaisesRegex(ValueError, "stale"):
                research_index.connect(root, python_path)
            self.assertEqual(self.truth_json(root, "search", "newly"),
                             [{"id": "U", "kind": "statements", "path": "corpus/statements/U.json"}])
            research_index.build(root, python_path)
            self.assertEqual(tables(index), tables(python_path))
            # A failed rebuild exits 1 and keeps the previous database.
            previous = index.read_bytes()
            (root / "corpus/statements/broken.json").write_text("{broken")
            self.truth(root, "index", "build", code=1)
            self.truth(root, "index", "summary", code=1)
            self.assertEqual(index.read_bytes(), previous)
            self.assertEqual(sorted(path.name for path in index.parent.iterdir()), ["truth-index.sqlite"])
            # A corrupt projection fails `parity` with its report, exit 1.
            (root / "corpus/statements/broken.json").unlink()
            with closing(sqlite3.connect(index)) as writer:
                writer.execute("UPDATE records SET body='{}' WHERE id='S'")
                writer.commit()
            report = json.loads(self.truth(root, "--json", "index", "parity", code=1)[1])["error"]["message"]
            self.assertEqual(json.loads(report)["issues"],
                             [{"path": "statements:S", "issue": "missing or unequal query record"}])
