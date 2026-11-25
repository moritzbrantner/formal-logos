import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from attempt_deliveries import change


class AttemptDeliveriesTest(unittest.TestCase):
    def test_metadata_and_research_are_distinguished(self):
        old = {"summary": "Same case", "current_assessment": {"assessment": "Open"}}
        self.assertIsNone(change(old, dict(old, evidence=["PR-21"])))
        disposition = {"assessment": "Open", "review": "accepted_qualified"}
        self.assertIsNone(change(old, dict(old, current_assessment=disposition)))
        self.assertEqual(change(old, dict(old, blocker="A new test")), "revised account")
        next_test = {"assessment": "Open", "next_test": "Compare the same bearer"}
        self.assertEqual(change(old, dict(old, current_assessment=next_test)), "revised assessment")

    def test_checkout_can_credit_a_delivery_after_an_identity_migration(self):
        script = Path(__file__).resolve().with_name("attempt_deliveries.py")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args):
                command = ["git", "-c", "user.name=Fixture", "-c", "user.email=test@example.com",
                           "-c", "commit.gpgsign=false", *args]
                return subprocess.check_output(command, cwd=root, text=True).strip()

            git("init", "-q", "-b", "main")
            git("commit", "-q", "--allow-empty", "-m", "Initial")
            since = git("rev-parse", "HEAD")
            git("switch", "-qc", "research")
            folder = root / "corpus" / "attempts"
            folder.mkdir(parents=True)
            path = folder / "original.json"
            attempt = {"id": "OLD", "summary": "A finding", "evidence": []}
            path.write_text(json.dumps(attempt))
            git("add", ".")
            git("commit", "-qm", "Research (#123)")
            git("switch", "-q", "main")
            git("merge", "--no-ff", "-qm", "Merge pull request #42 from owner/research", "research")

            def report():
                return subprocess.check_output([sys.executable, script, "--since", since], cwd=folder, text=True)

            self.assertIn("PR-42  introduced record", report())
            path.unlink()
            migrated = dict(attempt, id="CURRENT", legacy_id="OLD", evidence=["PR-42"])
            (folder / "current.json").write_text(json.dumps(migrated))
            self.assertIn("0 changed research records", report())


if __name__ == "__main__":
    unittest.main()
