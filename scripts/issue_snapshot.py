#!/usr/bin/env python3
"""Capture one GitHub issue and its timeline references for offline truth briefs."""

import argparse
from datetime import datetime, timezone
import json
import subprocess
import sys


def authorship(record):
    fields = {}
    login = (record.get("user") or {}).get("login")
    if login:
        fields["author"] = {"login": login}
    if record.get("author_association"):
        fields["authorAssociation"] = record["author_association"]
    return fields


def item(issue):
    row = {
        **authorship(issue),
        "number": issue["number"],
        "title": issue["title"],
        "url": issue["html_url"],
        "body": issue.get("body") or "",
        "state": issue["state"].upper(),
        "updatedAt": issue["updated_at"],
    }
    if "pull_request" in issue:
        row["mergedAt"] = issue["pull_request"].get("merged_at")
        if row["mergedAt"]:
            row["state"] = "MERGED"
    return row


def snapshot(issue, pages, captured_at):
    if "pull_request" in issue:
        raise ValueError("expected a research issue number, received a pull request")
    target = item(issue)
    target["comments"] = []
    references = {}
    for page in pages:
        for event in page:
            if event["event"] == "commented":
                target["comments"].append({
                    **authorship(event),
                    "url": event["html_url"],
                    "body": event.get("body") or "",
                    "createdAt": event["created_at"],
                })
            elif event["event"] == "cross-referenced":
                source = event.get("source", {}).get("issue")
                if source and source["repository_url"] == issue["repository_url"]:
                    reference = item(source)
                    if reference["number"] != target["number"]:
                        references[reference["number"]] = reference
    neighbors = [references[number] for number in sorted(references)]
    target["crossReferences"] = [row["url"] for row in neighbors]
    return {"captured_at": captured_at, "items": [target, *neighbors]}


def api(*args):
    return json.loads(subprocess.check_output(["gh", "api", *args]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("number", type=int)
    parser.add_argument("--repo", default="{owner}/{repo}", help="defaults to this checkout")
    args = parser.parse_args()
    if args.number < 1:
        parser.error("expected a positive issue number")
    endpoint = f"repos/{args.repo}/issues/{args.number}"
    try:
        issue = api(endpoint)
        pages = api("--paginate", "--slurp", f"{endpoint}/timeline?per_page=100")
        data = snapshot(issue, pages, datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))
    except (OSError, subprocess.CalledProcessError, ValueError, KeyError) as error:
        sys.exit(f"issue snapshot failed: {error}")
    json.dump(data, sys.stdout, ensure_ascii=False)
    print()


if __name__ == "__main__":
    main()
