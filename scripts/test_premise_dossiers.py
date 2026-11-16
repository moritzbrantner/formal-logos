#!/usr/bin/env python3
import copy
import unittest

from premise_dossiers import validate_attempt


def attempt(**overrides):
    return {"id": "0b6f3a52-6d0e-4c3b-8f43-6a0d3c1f9e21", "statement_ids": ["P"], "date": "2026-10-26",
            "kind": "derivation", "outcome": "failed", "summary": "The proposed inference did not follow.",
            "evidence": ["RESULT", "CLAIM", "PR-413"], **overrides}


class AttemptValidationTests(unittest.TestCase):
    def test_accepts_local_evidence_and_canonical_pr_reference(self):
        validate_attempt(attempt(), {"P"}, {"RESULT", "CLAIM"})
        validate_attempt(attempt(evidence=[]), {"P"}, set())

    def test_rejects_unknown_references_and_malformed_fields(self):
        cases = [dict(statement_ids=[]), dict(statement_ids=["UNKNOWN"]), dict(statement_ids=["P", "P"]),
                 dict(date="2026-02-30"), dict(date="20261026"), dict(kind="proof"), dict(kind=[]),
                 dict(outcome="proved"), dict(outcome={}), dict(summary=" "), dict(evidence=["UNKNOWN"]),
                 dict(evidence=["PR-0"]), dict(evidence=["PR-413", "PR-413"]), dict(evidence=[{}]),
                 dict(outcome="blocked"), dict(blocker=""), dict(id="P")]
        for fields in cases:
            with self.subTest(fields=fields), self.assertRaises(ValueError):
                validate_attempt(attempt(**fields), {"P"}, {"RESULT", "CLAIM"})
        validate_attempt(attempt(outcome="blocked", blocker="A pinned witness is missing."), {"P"}, {"RESULT", "CLAIM"})


if __name__ == "__main__":
    unittest.main()
