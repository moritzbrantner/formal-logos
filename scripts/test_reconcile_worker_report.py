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
        return report["assessments"]["corpus/attempts/example.json"][0]

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

    def test_conflicting_checkout_published_and_main_assessments_keep_source_commits(self):
        def revise(review, text, evidence):
            record = json.loads(self.path.read_text())
            record["current_assessment"].update(review=review, assessment=text, evidence=evidence)
            self.path.write_text(json.dumps(record))
            return self.save(text)

        self.git("switch", "-qc", "next-review")
        stale = revise("unreviewed", "Pending review", "PR #43")
        published = revise("accepted_qualified", "Revised publication", "PR #43")
        self.git("switch", "-q", "main")
        self.git("merge", "--no-ff", "-qm", "Merge pull request #43 from owner/next-review", "next-review")
        on_main = revise("changes_requested", "Main reassessment", "Later review of the same scope")
        self.git("switch", "-q", "--detach", stale)
        report = self.lookup(self.reviewed, "--pr", "43")
        rows = report["assessments"]["corpus/attempts/example.json"]
        sources = {row["recorded"]["review"]: row["sources"] for row in rows}
        self.assertEqual(sources, {
            "unreviewed": {"checkout_head": stale},
            "accepted_qualified": {"published_head": published},
            "changes_requested": {"main": on_main},
        })
        for row in rows:
            if row["recorded"]["review"] != "accepted_qualified":
                self.assertIn("supplies no acceptance", row["review_guidance"])

    def test_new_report_keeps_intervening_published_note_change_visible(self):
        self.git("switch", "-qc", "updated-publication", self.head)
        self.note.write_text("Intervening change to the qualified note")
        published = self.save("Revise the note after review")
        (self.root / "continuation.md").write_text("A new worker test")
        reported = self.save("Continue from published revision")
        snapshot = self.root / "snapshot.json"
        snapshot.write_text(json.dumps({"number": 42, "baseRefOid": self.base,
                                        "headRefOid": published, "state": "OPEN", "mergeCommit": None}))
        row = self.assessment_row(self.lookup(reported, "--pr", "42", "--snapshot", str(snapshot)))
        self.assertEqual(row["changed_report_paths"], ["continuation.md"])
        self.assertIn("note.md", row["integrated_paths_changed_since_review"])
        self.assertEqual(row["integrated_changes_command"], f"git diff --stat {self.reviewed} {published}")
        self.assertIn("intervening integration changes", row["review_guidance"])

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

    def test_shallow_boundary_matters_only_for_the_histories_compared(self):
        self.git("switch", "-qc", "sibling", self.base)
        self.note.write_text("Independent sibling")
        sibling = self.save("Sibling")
        with tempfile.TemporaryDirectory() as checkout:
            def git(*args):
                subprocess.run(["git", *args], cwd=checkout, check=True, capture_output=True)

            def relation(left, right):
                report = subprocess.check_output(
                    [sys.executable, SCRIPT, left, "--main", right, "--attempt", "example-id"],
                    cwd=checkout, text=True)
                return json.loads(report)["reported_to_main"]

            git("init", "-q")
            git("remote", "add", "local", self.root.as_uri())
            git("fetch", "--no-tags", "--depth=1", "local", self.main)
            git("fetch", "--no-tags", "local", self.worker, sibling)
            self.assertEqual(relation(self.worker, self.main), "unknown")
            self.assertEqual(relation(self.worker, sibling), "divergent")
            # The sibling's complete side of a merge cannot vouch for its shallow side.
            merged = subprocess.check_output(
                ["git", "-c", "user.name=Test", "-c", "user.email=test@example.org",
                 "-c", "commit.gpgsign=false", "commit-tree", f"{sibling}^{{tree}}",
                 "-p", sibling, "-p", self.main, "-m", "Join the two histories"],
                cwd=checkout, text=True).strip()
            self.assertEqual(relation(self.worker, merged), "unknown")
            git("fetch", "--no-tags", "--unshallow", "local", self.main)
            self.assertEqual(relation(self.worker, self.main), "ancestor")

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
