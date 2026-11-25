#!/usr/bin/env python3
"""Find merged revisions of research attempts still missing a delivery reference."""

import argparse
from functools import lru_cache
import json
from pathlib import Path
import re
import subprocess


def git(*args):
    return subprocess.check_output(["git", *args], text=True)


@lru_cache(maxsize=128)
def record(blob):
    return json.loads(git("cat-file", "blob", blob))


def change(before, after):
    if before is None:
        return "introduced record"
    if any(before.get(key) != after.get(key) for key in ("summary", "blocker", "outcome")):
        return "revised account"
    old = before.get("current_assessment", {})
    new = after.get("current_assessment", {})
    if any(old.get(key) != new.get(key) for key in ("assessment", "next_test")):
        return "revised assessment"
    return None


def missing(since, head, current):
    history = git(
        "log", "--first-parent", "--diff-merges=first-parent", "--raw", "--no-abbrev",
        "--find-renames", "--diff-filter=AMR", "--format=@%H%x09%P%x09%s", f"{since}..{head}",
        "--", ":(top)corpus/attempts",
    )
    for line in history.splitlines():
        if line.startswith("@"):
            revision, parents, subject = line[1:].split("\t", 2)
            match = re.fullmatch(r"Merge pull request #([1-9][0-9]*) from .+", subject)
            pr = f"PR-{match[1]}" if match and len(parents.split()) > 1 else None
        elif line.startswith(":"):
            header, *paths = line.split("\t")
            if not paths[-1].endswith(".json"):
                continue
            _, _, old, new, _ = header.split()
            after = record(new)
            dest = current.get(after["id"])
            if dest and pr and pr in dest["evidence"]:
                continue
            finding = change(None if not old.strip("0") else record(old), after)
            if finding:
                yield revision, pr, finding, paths[-1], dest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--since", required=True, help="previously inspected commit (exclusive)")
    parser.add_argument("--head", default="HEAD", help="local revision to inspect (inclusive)")
    args = parser.parse_args()
    since, head = [
        git("rev-parse", "--verify", "--end-of-options", ref + "^{commit}").strip()
        for ref in (args.since, args.head)
    ]
    if subprocess.run(["git", "merge-base", "--is-ancestor", since, head]).returncode:
        parser.error("--since must be an ancestor of --head")

    root = Path(git("rev-parse", "--show-toplevel").strip())
    current = {}
    for path in (root / "corpus/attempts").glob("*.json"):
        attempt = json.loads(path.read_text())
        for identity in (attempt["id"], attempt.get("legacy_id")):
            if identity:
                current[identity] = attempt
    count = 0
    for revision, pr, finding, path, dest in missing(since, head, current):
        count += 1
        reference = pr or "PR unknown from commit subject"
        status = dest["id"] if dest else "identity absent from checkout"
        print(f"{revision[:12]}  {reference}  {finding}  {path}  [{status}]")
    print(f"{count} changed research records to inspect against the current checkout.")


if __name__ == "__main__":
    main()
