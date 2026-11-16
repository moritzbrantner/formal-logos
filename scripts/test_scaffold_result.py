"""Offline scaffold contract: linked drafts, no overwrites."""
import argparse
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import corpus_records as corpus
import scaffold_result as scaffold


class ScaffoldResultTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        for kind in ("statements", "arguments", "inferences", "results"):
            (self.root / "corpus" / kind).mkdir(parents=True)
        for sid in ("P", "C"):
            (self.root / f"corpus/statements/{sid}.json").write_text(json.dumps({
                "id": f"STMT-{sid}", "paraphrase": sid,
                "lean_declaration": f"TruthCore.Test.{sid}",
                "definition_ids": ["DEF-TEST"],
            }))
        meaning = self.root / "meaning.txt"
        meaning.write_text("Explicitly supplied conditional meaning.")
        self.args = argparse.Namespace(
            id="TEST-DRAFT", premise=["STMT-P"], conclusion="STMT-C", meaning_file=meaning,
            rule="direct-proof", challenge_module="TruthCore.Results.Test.Challenge",
            solution_module="TruthCore.Results.Test.Solution", theorem="TruthCore.Results.Test.checks",
            axiom=[],
        )
        self.patch = patch.multiple(corpus, ROOT=self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_linked_drafts_and_new_directory_only(self):
        before = sorted(p.relative_to(self.root) for p in self.root.rglob("*"))
        draft = scaffold.bundle(self.args)
        records = draft["records"]
        argument = records["corpus/arguments/TEST-DRAFT.json"]
        inference = records["corpus/inferences/test-draft.json"]
        result = records["corpus/results/TEST-DRAFT.json"]
        config = records[result["comparator_config"]]
        self.assertEqual(argument["inference_ids"], [inference["id"]])
        self.assertEqual(argument["premise_statement_ids"], inference["input_statement_ids"])
        self.assertEqual(argument["conclusion_statement_id"], inference["output_statement_id"])
        self.assertEqual(result["argument_id"], argument["id"])
        self.assertEqual(config["theorem_names"], [result["theorem"]])
        self.assertEqual(argument["definition_ids"], ["DEF-TEST"])
        self.assertNotIn("status", result)
        self.assertEqual(config["permitted_axioms"], [])
        self.assertTrue(draft["solution_header"].startswith("module\n\npublic import "))
        self.assertIn("@[expose] public section", draft["solution_header"])
        self.assertEqual(before, sorted(p.relative_to(self.root) for p in self.root.rglob("*")))
        output = self.root / "drafts"
        scaffold.write_drafts(output, draft)
        snapshot = {p: p.read_bytes() for p in output.rglob("*.json")}
        self.assertEqual(len(snapshot), 5)
        with self.assertRaises(FileExistsError):
            scaffold.write_drafts(output, draft)
        self.assertEqual(snapshot, {p: p.read_bytes() for p in output.rglob("*.json")})
        for output in (self.root, self.root / "corpus/drafts", self.root / "results/drafts"):
            with self.assertRaises(corpus.CorpusError):
                scaffold.write_drafts(output, draft)

    def test_unknown_statement_is_rejected(self):
        self.args.premise = ["STMT-MISSING"]
        with self.assertRaisesRegex(corpus.CorpusError, "unknown statement"):
            scaffold.bundle(self.args)

    def test_id_and_path_collisions_and_empty_meaning_are_rejected(self):
        for kind, filename, record_id in (("arguments", "different.json", "TEST-DRAFT"),
                                          ("inferences", "different.json", "INF-TEST-DRAFT"),
                                          ("results", "different.json", "TEST-DRAFT")):
            path = self.root / "corpus" / kind / filename
            path.write_text(json.dumps({"id": record_id}))
            with self.assertRaisesRegex(corpus.CorpusError, "existing .* ID"):
                scaffold.bundle(self.args)
            path.unlink()
        canonical = self.root / "results/TEST-DRAFT/comparator.json"
        canonical.parent.mkdir(parents=True)
        canonical.write_text("do not overwrite")
        with self.assertRaisesRegex(corpus.CorpusError, "canonical path already exists"):
            scaffold.bundle(self.args)
        self.assertEqual(canonical.read_text(), "do not overwrite")
        canonical.unlink()
        self.args.meaning_file.write_text(" ")
        with self.assertRaisesRegex(corpus.CorpusError, "meaning and inference rule"):
            scaffold.bundle(self.args)


if __name__ == "__main__":
    unittest.main()
