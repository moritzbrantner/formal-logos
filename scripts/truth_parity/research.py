"""`truth related|dossier|context` against `corpus.py related|dossier|context`."""
import contextlib
import io
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from truth_parity import golden
from truth_parity.check import write_check_fixture
from truth_parity.common import U, humanize, ParityCase


def spread(items, count):
    """`count` entries evenly spaced over a sorted list (deterministic sample)."""
    items = sorted(items)
    if len(items) <= count:
        return items
    return [items[index * len(items) // count] for index in range(count)]


class TruthResearchParity(ParityCase):
    """`truth related|dossier|context` against `corpus.py related|dossier|context`
    on a broad real-corpus sample, one frontier report shared by both sides."""
    real_corpus_only = True

    @classmethod
    def setUpClass(cls):
        from premise_dossiers import dossier_index

        directories = ("statements", "claims", "definitions", "disambiguations", "inferences", "arguments",
                       "results", "relations", "attempts", "models", "configurations", "candidates")
        cls.data = {name: [record for _, record in corpus.load_dir(name)] for name in directories}
        data = cls.data
        # The report `corpus.py dossier` and `context` compute, handed to Rust as a file.
        cls.report = corpus.frontier_report(
            data["statements"], data["arguments"], data["results"], data["relations"],
            root=corpus.DEFAULT_FRONTIER_ROOT,
            transcription=corpus.transcription_flags(data["results"], data["arguments"], data["statements"]),
            claims=data["claims"])
        cls.temporary = tempfile.TemporaryDirectory()
        cls.frontier = str(Path(cls.temporary.name) / "frontier.json")
        Path(cls.frontier).write_text(json.dumps(cls.report, ensure_ascii=False))
        cls.dossiers = dossier_index(data, cls.report)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def truth(self, *args, code=0):
        result = subprocess.run([self.binary, *args], cwd=corpus.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, code, (args, result.stderr))
        return result.stdout, result.stderr

    def truth_json(self, *args):
        value = json.loads(self.truth("--json", *args)[0])
        self.assertTrue(value.pop("input_identity").startswith("fnv1a64:"))
        return value

    def statement_sample(self):
        report = self.report
        closed = list(report["closed_statements"])
        by_depth = {}
        for item in report["items"]:
            by_depth.setdefault(item["depth"], []).append(item["statement_id"])
        listed = set(closed) | {item["statement_id"] for item in report["items"]}
        others = [entry["id"] for entry in self.data["statements"] if entry["id"] not in listed]
        sample = set(spread(closed, 6)) | set(spread(others, 6))
        for depth in ("stated", "supported", "bare"):
            sample |= set(spread(by_depth.get(depth, []), 6))
        sample |= set(spread([entry["statement_id"] for entry in report["floor"]], 3))
        return sorted(sample)

    def test_related(self):
        for sid in self.statement_sample()[:30]:
            for limit in ("10", "3"):
                expected = io.StringIO()
                with contextlib.redirect_stdout(expected):
                    corpus.main_with(["related", sid, "--limit", limit])
                self.assertEqual(self.truth("related", sid, "--limit", limit)[0], expected.getvalue(), sid)
            from research_index import cached_related
            self.assertEqual(self.truth_json("related", sid), cached_related(corpus.ROOT, sid, 10), sid)
        self.assertEqual(json.loads(self.truth("--json", "related", "STMT-NO-SUCH", code=3)[1])["error"]["code"],
                         "unknown_id")
        argument = self.data["arguments"][0]["id"]
        self.assertIn("related requires a statement ID",
                      self.truth("related", f"arguments:{argument}", code=2)[1])

    def test_dossier(self):
        from premise_dossiers import format_dossier

        sample = self.statement_sample()
        self.assertGreaterEqual(len(sample), 30)
        for sid in sample:
            dossier = self.dossiers[sid]
            self.assertEqual(self.truth_json("dossier", sid, "--frontier-json", self.frontier), dossier, sid)
            for limit in (8, 0, 2):
                expected = humanize(format_dossier(dossier, self.data, limit=None if limit <= 0 else limit))
                actual = self.truth("dossier", sid, "--frontier-json", self.frontier, "--limit", str(limit))[0]
                self.assertEqual(actual, expected + "\n", (sid, limit))
        everything = json.loads(self.truth("dossier", "--all", "--frontier-json", self.frontier)[0])
        self.assertEqual(everything, self.dossiers)
        self.assertEqual(json.loads(self.truth("--json", "dossier", "STMT-NO-SUCH", "--frontier-json",
                                               self.frontier, code=3)[1])["error"]["code"], "unknown_id")
        # Without --frontier-json the Rust frontier computes the same report in-process.
        for sid in sample[:8]:
            self.assertEqual(self.truth_json("dossier", sid), self.dossiers[sid], sid)
            self.assertEqual(self.truth("dossier", sid)[0],
                             self.truth("dossier", sid, "--frontier-json", self.frontier)[0], sid)
        self.assertEqual(json.loads(self.truth("dossier", "--all")[0]), self.dossiers)
        self.assertEqual(json.loads(self.truth("--json", "dossier", sample[0], "--frontier-root", "STMT-NO-SUCH",
                                               code=1)[1])["error"]["message"],
                         "unknown root statement: STMT-NO-SUCH")

    def test_context(self):
        from argument_context import context_pack, format_context, resolve_target
        from research_index import cached_related

        arguments = {entry["id"]: entry for entry in self.data["arguments"]}
        results = {entry["id"]: entry for entry in self.data["results"]}
        concluded = {}
        for entry in self.data["arguments"]:
            concluded.setdefault(entry["conclusion_statement_id"], []).append(entry["id"])
        unique = [sid for sid, ids in concluded.items() if len(ids) == 1 and sid not in arguments]
        targets = (spread(arguments, 12) + spread([rid for rid in results if rid not in arguments], 3)
                   + spread(unique, 3))
        self.assertGreaterEqual(len(targets), 15)
        for target in targets:
            argument_id, _ = resolve_target(target, arguments, results)
            related = cached_related(corpus.ROOT, arguments[argument_id]["conclusion_statement_id"], 8)["matches"]
            pack = context_pack(corpus.ROOT, self.data, self.report, argument_id, related=related)
            self.assertEqual(self.truth_json("context", target, "--frontier-json", self.frontier), pack, target)
            for limit in (6, 2, -1):
                actual = self.truth("context", target, "--frontier-json", self.frontier, "--limit", str(limit))[0]
                self.assertEqual(actual, humanize(format_context(pack, limit=limit)) + "\n", (target, limit))
        for target in targets[:5]:
            self.assertEqual(self.truth_json("context", target),
                             self.truth_json("context", target, "--frontier-json", self.frontier), target)
            self.assertEqual(self.truth("context", target)[0],
                             self.truth("context", target, "--frontier-json", self.frontier)[0], target)
        # A target may be named by legacy id or label as well as by uuid.
        # Legacy aliases are optional on UUID-native records. Exercise both
        # identity shapes explicitly rather than depending on corpus ordering.
        for has_alias in (True, False):
            argument = next(entry for entry in self.data["arguments"]
                            if bool(entry.get("legacy_id")) == has_alias)
            tokens = [argument["id"], argument["label"]]
            if has_alias:
                tokens.append(argument["legacy_id"])
            expected = self.truth_json("context", argument["id"], "--frontier-json", self.frontier)
            for token in tokens:
                self.assertEqual(self.truth_json("context", token, "--frontier-json", self.frontier),
                                 expected, token)
            statement = next(entry for entry in self.data["statements"]
                             if bool(entry.get("legacy_id")) == has_alias)
            tokens = [statement["id"], statement["label"]]
            if has_alias:
                tokens.append(statement["legacy_id"])
            for token in tokens:
                self.assertEqual(self.truth_json("dossier", token, "--frontier-json", self.frontier),
                                 self.dossiers[statement["id"]], token)
        no_related = self.truth_json("context", targets[0], "--frontier-json", self.frontier, "--related", "0")
        self.assertEqual(no_related["related_statements"], [])
        self.assertEqual(json.loads(self.truth("--json", "context", "NO-SUCH-TARGET", "--frontier-json",
                                               self.frontier, code=3)[1])["error"]["code"], "unknown_id")
        several = next(sid for sid, ids in concluded.items() if len(ids) > 1)
        self.assertIn("is concluded by several arguments",
                      self.truth("context", several, "--frontier-json", self.frontier, code=2)[1])


class TruthResearchFixtureParity(ParityCase):
    """`truth related|dossier|context` against the Python CLI on a fixture checkout."""

    def test_fixture(self):
        """The Python CLI on the `check` fixture (with a copy of `scripts/*.py`):
        text and `--json` of `related`, `dossier` and `context`, which the
        golden snapshots freeze before the Python commands retire."""
        statement, argument = U("statement", "STMT-B"), U("argument", "ARG-BC")
        cases = [
            (["related", "STMT-B"], None), (["related", statement, "--limit", "1"], None),
        ]
        # Python names the frontier root `--root`; Rust's `--root` is the checkout.
        for args in (["dossier", "STMT-B"], ["dossier", "STMT-C", "--limit", "0"], ["dossier", "STMT-A"],
                     ["context", "ARG-BC"], ["context", argument, "--limit", "1", "--related", "0"],
                     ["context", "RES-AB"]):
            cases.append(([*args, "--root", "STMT-C"], [*args, "--frontier-root", "STMT-C"]))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root)
            for python_args, rust_args in cases:
                rust_args = rust_args or python_args
                for machine in (False, True):
                    with self.subTest(args=python_args, json=machine):
                        python = subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), *python_args,
                                                 *(["--json"] if machine else [])],
                                                capture_output=True, text=True, check=False)
                        self.assertEqual(python.returncode, 0, python.stderr)
                        expected = {"stdout_json": json.loads(python.stdout)} if machine else {"stdout": python.stdout}
                        command = ["--root", root, *(["--json"] if machine else []), *rust_args]
                        golden.record(self, command, root=root, code=0, exclude=(".cache",), **expected)
                        rust = subprocess.run([self.binary, *map(str, command)], capture_output=True, text=True,
                                              check=False)
                        self.assertEqual(rust.returncode, 0, rust.stderr)
                        if machine:
                            actual = json.loads(rust.stdout)
                            actual.pop("input_identity", None)
                            self.assertEqual(actual, expected["stdout_json"])
                        else:
                            self.assertEqual(rust.stdout, python.stdout)
