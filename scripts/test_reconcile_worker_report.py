import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("reconcile_worker_report.py").resolve()


class WorkerReportTest(unittest.TestCase):
    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True).strip()

    def save(self, message):
        self.git("add", ".")
        self.git("commit", "-qm", message)
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.git("init", "-qb", "main")
        self.git("config", "user.email", "test@example.com")
        self.git("config", "user.name", "Fixture")
        self.git("config", "commit.gpgsign", "false")
        self.note = self.root / "note.md"
        self.note.write_text("Initial")
        self.base = self.save("Start")
        self.git("switch", "-qc", "worker")
        self.note.write_text("Proposed")
        self.worker = self.save("Proposal")
        self.note.write_text("Qualified")
        self.reviewed = self.save("Corrected scope")
        self.path = self.root / "corpus/attempts/example.json"
        self.path.parent.mkdir(parents=True)
        self.assessment = {"reviewed_revision": self.reviewed, "scope": "A single case",
                           "assessment": "Qualified result", "review": "accepted_qualified",
                           "publication": "published", "evidence": "Independent review of the correction."}
        self.path.write_text(json.dumps({"id": "example-id", "evidence": ["PR-7"],
                                         "current_assessment": self.assessment}))
        self.head = self.save("Record review")
        self.git("switch", "-q", "main")
        self.git("merge", "--no-ff", "-qm", "Merge pull request #42 from owner/worker", "worker")
        self.merge = self.git("rev-parse", "HEAD")
        (self.root / "other-work").write_text("Unrelated change on main")
        self.main = self.save("Other work")

    def lookup(self, reported, *args, env=None):
        output = subprocess.check_output([sys.executable, SCRIPT, reported, "--main", "main", *args],
                                         cwd=self.path.parent, text=True, env=env)
        return json.loads(output)

    def assessment_row(self, report):
        return report["assessments"]["corpus/attempts/example.json"]

    def test_old_report_and_corrected_review_through_main_merge(self):
        for selector in (["--pr", "42"], ["--attempt", "example-id"]):
            report = self.lookup(self.worker, *selector)
            self.assertEqual(report["uncertainties"], [])
            self.assertEqual(report["pr"]["head"], self.head)
            self.assertEqual(report["pr"]["merge"], self.merge)
            self.assertEqual(report["pr"]["merge_to_main"], "ancestor")
            self.assertEqual(report["reported_to_main"], "ancestor")
            self.assertEqual(self.assessment_row(report)["reported_to_reviewed"], "ancestor")
            self.assertEqual(self.assessment_row(report)["recorded"], self.assessment)
        report = self.lookup(self.reviewed, "--pr", "42")
        self.assertEqual(self.assessment_row(report)["reported_to_reviewed"], "same")

    def test_new_work_omits_integrated_changes_and_reverted_edits(self):
        self.git("switch", "-qc", "continuation")
        self.note.write_text("A new argument")
        self.save("New argument")
        other = self.root / "other-work"
        other.write_text("Temporary")
        self.save("Temporary change")
        other.write_text("Unrelated change on main")
        reported = self.save("Restore")
        report = self.lookup(reported, "--pr", "42")
        row = self.assessment_row(report)
        self.assertEqual(row["reported_to_reviewed"], "descendant")
        self.assertEqual(row["report_diff_base"], self.main)
        self.assertEqual(row["changed_report_paths"], ["note.md"])
        self.note.write_text("Qualified")
        restored = self.lookup(self.save("Restore argument too"), "--pr", "42")
        self.assertEqual(self.assessment_row(restored)["changed_report_paths"], [])

    def test_published_work_after_review_is_still_visible(self):
        report = self.lookup(self.head, "--pr", "42")
        row = self.assessment_row(report)
        self.assertEqual(row["reported_to_reviewed"], "descendant")
        self.assertEqual(row["changed_report_paths"], [])
        self.assertEqual(row["integrated_paths_changed_since_review"], ["corpus/attempts/example.json"])

    def test_missing_report_and_divergence_remain_unresolved(self):
        missing = self.lookup("f" * 40, "--pr", "42")
        self.assertEqual(self.assessment_row(missing)["reported_to_reviewed"], "unknown")
        self.assertTrue(missing["uncertainties"])
        self.git("switch", "-qc", "independent", self.base)
        self.note.write_text("Independent")
        divergent = self.save("Different report")
        self.git("switch", "-q", "main")
        report = self.lookup(divergent, "--pr", "42")
        row = self.assessment_row(report)
        self.assertEqual(row["reported_to_reviewed"], "divergent")
        self.assertNotIn("changed_report_paths", row)

    def test_squash_metadata_does_not_establish_head_ancestry(self):
        self.git("switch", "-qc", "squash", self.base)
        self.git("merge", "--squash", "worker")
        squashed = self.save("Squashed (#42)")
        snapshot = self.root / "pr.json"
        snapshot.write_text(json.dumps({"number": 42, "baseRefOid": self.base, "headRefOid": self.head,
                                        "mergeCommit": {"oid": squashed}, "state": "MERGED"}))
        report = self.lookup(self.reviewed, "--pr", "42", "--snapshot", str(snapshot), "--main", "squash")
        self.assertEqual(report["pr"]["head_to_merge"], "divergent")
        self.assertEqual(report["reported_to_main"], "divergent")
        self.assertIn("squash", " ".join(report["uncertainties"]))

    def test_unavailable_publication_is_queried_once_and_remains_unresolved(self):
        gh = self.root / "gh"
        gh.write_text('#!/bin/sh\necho query >> "$QUERY_LOG"\nexit 1\n')
        gh.chmod(0o755)
        log = self.root / "queries"
        env = {**os.environ, "PATH": str(self.root) + os.pathsep + os.environ["PATH"], "QUERY_LOG": str(log)}
        report = self.lookup(self.worker, "--pr", "7", env=env)
        self.assertEqual(log.read_text(), "query\n")
        self.assertTrue(report["uncertainties"])
        self.assertEqual(report["assessments"], {})  # historical PR-7 evidence is outside the scoped judgment


if __name__ == "__main__":
    unittest.main()
