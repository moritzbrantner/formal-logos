"""`truth next`, `next-steps`, `arguments`, `results` and `sort-lists`
against the same `corpus.py` subcommands, on the real corpus and on the
`check` fixture checkout (which carries a copy of `scripts/*.py`, so the
unmodified Python CLI runs on it)."""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import corpus
from truth_parity.check import CHECK_FAILURES, by_id, write_check_fixture
from truth_parity.common import U, ParityCase


def python_cli(root, *args):
    return subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), *args],
                          capture_output=True, text=True, check=False)


def extra_candidates(records):
    """Candidates whose order exercises the (priority, id) choice."""
    first = by_id(records, "candidates", "CAND-1")
    first["priority"] = 5
    for legacy, priority, name in (("CAND-2", 3, "second"), ("CAND-3", 3, "third"), ("CAND-4", 9, "fourth")):
        records["candidates"].append({**first, "id": U("candidate", legacy), "label": f"the {name} candidate",
                                      "legacy_id": legacy, "priority": priority,
                                      "goal": "é “quoted” \"goal\"\n", "locator": legacy})
    # A settlement action, so the next-steps text has a recorded decision.
    by_id(records, "statements", "STMT-A")["settlement_actions"] = [
        {"kind": "floor", "status": "needs-owner-decision", "description": "decide A"}]


class TruthNavigationParity(ParityCase):
    """`truth next`, `next-steps`, `arguments`, `results`, `sort-lists`."""

    def truth(self, root, *args):
        return subprocess.run([self.binary, "--root", str(root), *args],
                              capture_output=True, text=True, check=False)

    def assert_same(self, root, *args, rust_args=None):
        python, rust = python_cli(root, *args), self.truth(root, *(rust_args or args))
        self.assertEqual((rust.returncode, rust.stdout, rust.stderr),
                         (python.returncode, python.stdout, python.stderr), args)
        return python

    def test_real_corpus(self):
        root = corpus.ROOT
        for command in ("next", "arguments", "results"):
            self.assertTrue(self.assert_same(root, command).stdout, command)
        machine = json.loads(self.truth(root, "--json", "next").stdout)
        candidates = [record for _, record in corpus.load_dir("candidates")]
        self.assertEqual(machine, min(candidates, key=lambda c: (c["priority"], c["id"])))
        for kind in ("arguments", "results"):
            ids = json.loads(self.truth(root, "--json", kind).stdout)
            self.assertEqual(ids["ids"], [record["id"] for _, record in corpus.load_dir(kind)])

    def test_real_next_steps(self):
        report = corpus.current_frontier(corpus.DEFAULT_FRONTIER_ROOT, False)["next_steps"]
        from next_steps import format_next_steps
        rust = self.truth(corpus.ROOT, "next-steps")
        self.assertEqual(rust.returncode, 0, rust.stderr)
        self.assertEqual(rust.stdout, corpus.humanize(format_next_steps(report)) + "\n")
        machine = json.loads(self.truth(corpus.ROOT, "--json", "next-steps").stdout)
        self.assertTrue(machine.pop("input_identity").startswith("fnv1a64:"))
        self.assertEqual(machine, report)

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root, extra_candidates)
            self.assertEqual(python_cli(root, "check").returncode, 0, python_cli(root, "check").stderr)
            for command in ("next", "arguments", "results"):
                self.assert_same(root, command)
            self.assertIn('"legacy_id": "CAND-2"', python_cli(root, "next").stdout)
            self.assert_same(root, "next-steps")  # the default root is absent here
            for token in ("STMT-C", U("statement", "STMT-C"), "C"):
                text = self.assert_same(root, "next-steps", "--root", token,
                                        rust_args=("next-steps", "--frontier-root", token)).stdout
                self.assertIn("floor / needs-owner-decision: decide A", text)
                self.assertIn("    verified results: ", text)
                python = python_cli(root, "next-steps", "--json", "--root", token)
                machine = json.loads(self.truth(root, "--json", "next-steps", "--frontier-root", token).stdout)
                machine.pop("input_identity")
                self.assertEqual(machine, json.loads(python.stdout))
            for candidate in (root / "corpus" / "candidates").glob("*.json"):
                candidate.unlink()
            self.assertEqual(self.assert_same(root, "next").returncode, 1)
            self.assertEqual(self.truth(root, "--json", "next").returncode, 1)

    def test_broken_corpus(self):
        # Every validate-first command reports the first corpus error, exit 2.
        for name in list(CHECK_FAILURES)[:12]:
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                write_check_fixture(root, CHECK_FAILURES[name])
                for command in ("next", "arguments", "results", "next-steps"):
                    python = self.assert_same(root, command)
                    self.assertEqual(python.returncode, 2, (name, command))
                    self.assertTrue(python.stderr.startswith("corpus error: "))

    def test_sort_lists(self):
        def unsorted(records):
            source = records["sources"][0]
            source["edition_urns"] = list(reversed(source["edition_urns"]))
            records["sources"].append({**source, "id": U("source", "SRC-2"), "label": "the second source",
                                       "legacy_id": "SRC-2", "work": "W “2”",
                                       "edition_urns": ["urn:cts:fix:w.c", "urn:cts:fix:w.b"]})

        with tempfile.TemporaryDirectory() as temporary:
            python_root, rust_root = Path(temporary) / "py", Path(temporary) / "rs"
            write_check_fixture(python_root, unsorted)
            # One record compact, as a hand-written record may be.
            compact = sorted((python_root / "corpus" / "sources").glob("*.json"))[-1]
            compact.write_text(json.dumps(json.loads(compact.read_text()), ensure_ascii=False) + "\n")
            shutil.copytree(python_root, rust_root)
            python, rust = python_cli(python_root, "sort-lists"), self.truth(rust_root, "sort-lists")
            self.assertEqual((rust.returncode, rust.stdout, rust.stderr), (python.returncode, python.stdout, ""))
            self.assertEqual(python.stdout.count("sorted edition_urns in corpus/sources/"), 2)
            for path in sorted((python_root / "corpus").rglob("*.json")):
                self.assertEqual((rust_root / path.relative_to(python_root)).read_bytes(), path.read_bytes(), path)
            # Sorted lists are left alone; the corpus now passes check.
            self.assert_same(rust_root, "sort-lists")
            self.assertEqual(self.truth(rust_root, "sort-lists").stdout, "")
            self.assertEqual(self.truth(rust_root, "check").returncode, 0)
            self.assertEqual(json.loads(self.truth(rust_root, "--json", "sort-lists").stdout)["sorted"], [])

    def test_usage(self):
        for args in (["next", "extra"], ["arguments", "--queue"], ["results", "--frontier-root", "X"],
                     ["sort-lists", "--routes"], ["next-steps", "--base", "HEAD"]):
            result = subprocess.run([self.binary, "--json", *args], cwd=corpus.ROOT,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 2, args)
