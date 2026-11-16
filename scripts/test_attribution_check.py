"""Tests for the claim `attribution` field shape (#989; the self-check is `truth attribution-check`)."""

from __future__ import annotations

import unittest

import attribution_check as ac

GOOD = "The passage states that whatever is changed in any way is in potency, which is the premise."


def claim(**extra) -> dict:
    return {"id": "C", "statement_id": "STMT-P", "source_id": "SRC", "locator": "I q.9 a.1 co.",
            "interpretation": "reading", **extra}


class ValidateAttributionTest(unittest.TestCase):
    def test_shape(self) -> None:
        ac.validate_attribution("c.json", claim())
        ac.validate_attribution("c.json", claim(attribution=GOOD))
        for bad in ("It is stated somewhere in the passage, I think.", "The passage states X.", 7):
            with self.subTest(bad=bad), self.assertRaisesRegex(ac.AttributionError, "attribution must be"):
                ac.validate_attribution("c.json", claim(attribution=bad))


if __name__ == "__main__":
    unittest.main()
