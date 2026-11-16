"""Schema registrations require proof obligations, not resemblance or source support."""

from __future__ import annotations

import argparse
import contextlib
import copy
import io
import unittest
from pathlib import Path
from unittest.mock import patch

import corpus


class SchemaRegistrationTest(unittest.TestCase):
    def setUp(self):
        self.path = corpus.ROOT / "corpus/relations/test.json"
        self.relation = {
            "id": "REL-INSTANCE",
            "predicate": "instance_of_schema",
            "subject_kind": "statement",
            "subject_id": "INSTANCE",
            "object_kind": "statement",
            "object_id": "SCHEMA",
            "verification_result_id": "PACKAGE",
            "instance_theorem": "TruthCore.Results.Test.instanceProof",
            "schema_theorem": "TruthCore.Results.Test.schemaProof",
            "note": "Conditional instance, not source support or frontier closure.",
        }
        self.results = {"PACKAGE": {"solution_module": "TruthCore.Results.Test.Solution"}}
        self.configs = {"PACKAGE": {"theorem_names": [
            self.relation["instance_theorem"], self.relation["schema_theorem"],
        ]}}

    def validate(self, relation):
        corpus.validate_premise_program_relation(self.path, relation)
        corpus.validate_schema_registration(self.path, relation, self.results, self.configs)

    def test_requires_two_statement_endpoints(self):
        self.validate(self.relation)
        for field in ("subject_kind", "object_kind"):
            with self.subTest(field=field), self.assertRaises(corpus.CorpusError):
                self.validate({**self.relation, field: "claim"})

    def test_rejects_missing_unknown_or_unlisted_proof_evidence(self):
        for field in ("verification_result_id", "instance_theorem", "schema_theorem", "note"):
            altered = {key: value for key, value in self.relation.items() if key != field}
            with self.subTest(missing=field), self.assertRaises(corpus.CorpusError):
                self.validate(altered)
        for note in (" ", 1):
            with self.subTest(note=note), self.assertRaises(corpus.CorpusError):
                self.validate({**self.relation, "note": note})
        for field in ("verification_result_id", "instance_theorem", "schema_theorem"):
            with self.subTest(unknown=field), self.assertRaises(corpus.CorpusError):
                self.validate({**self.relation, field: "UNKNOWN"})


    def test_registration_neither_sources_nor_closes_statements(self):
        statements = [{"id": name, "paraphrase": name} for name in ("INSTANCE", "SCHEMA")]
        baseline = corpus.frontier_report(statements, [], [], [], root="SCHEMA")
        registered = corpus.frontier_report(statements, [], [], [self.relation], root="SCHEMA")
        self.assertEqual(registered, baseline)
        self.assertEqual(registered["established_statements"], [])


if __name__ == "__main__":
    unittest.main()
