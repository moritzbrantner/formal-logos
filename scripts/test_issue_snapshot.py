import unittest

from issue_snapshot import snapshot


class IssueSnapshotTests(unittest.TestCase):
    def test_paginated_issue_timeline_keeps_local_history_and_actual_merge_state(self):
        repo = "https://api.github.com/repos/research/project"
        target = {
            "number": 12, "title": "Does the case distinguish the rival?",
            "html_url": "https://github.com/research/project/issues/12",
            "user": {"login": "reporter"},
            "body": "Original scope", "state": "open", "repository_url": repo,
            "updated_at": "2026-11-25T00:00:00Z",
        }

        def pull(number, merged_at):
            return {
                **target, "number": number, "state": "closed", "body": None,
                "html_url": f"https://github.com/research/project/pull/{number}",
                "pull_request": {"merged_at": merged_at},
            }

        def reference(source):
            return {"event": "cross-referenced", "source": {"issue": source}}

        merged = pull(30, target["updated_at"])
        closed = pull(28, None)
        foreign = {**merged, "repository_url": repo + "-other"}
        comment = {
            "event": "commented", "html_url": target["html_url"] + "#issuecomment-123",
            "user": {"login": "coordinator"}, "author_association": "OWNER",
            "body": "Narrowed scope", "created_at": target["updated_at"],
        }
        result = snapshot(target, [
            [comment, reference(merged), reference(foreign)],
            [reference(merged), reference(closed), reference(target)],
        ], target["updated_at"])
        issue, prior, delivered = result["items"]
        self.assertEqual([issue["number"], prior["number"], delivered["number"]], [12, 28, 30])
        self.assertEqual(issue["body"], "Original scope")
        self.assertEqual(issue["author"], {"login": "reporter"})
        self.assertEqual(issue["comments"][0], {
            "author": {"login": "coordinator"}, "authorAssociation": "OWNER",
            "url": comment["html_url"], "body": "Narrowed scope", "createdAt": comment["created_at"],
        })
        self.assertEqual(issue["crossReferences"], [closed["html_url"], merged["html_url"]])
        self.assertEqual(prior["state"], "CLOSED")
        self.assertEqual(delivered["state"], "MERGED")
        self.assertEqual(delivered["mergedAt"], merged["updated_at"])


if __name__ == "__main__":
    unittest.main()
