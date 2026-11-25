#!/usr/bin/env python3
"""Look up a delayed worker revision against a PR or an owning research attempt."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from corpus_records import CorpusError, load_dir

PR_MERGE = re.compile(r"Merge pull request #(\d+) from .+")
SCOPED_PR = re.compile(r"\bPR(?:-| #)([1-9][0-9]*)\b")
FIELDS = "number,state,baseRefOid,headRefOid,mergeCommit"


def git(*args):
    return subprocess.run(["git", *args], text=True, capture_output=True,
                          env={**os.environ, "GIT_NO_LAZY_FETCH": "1"})


def commit(ref):
    if ref:
        result = git("rev-parse", "--verify", "--end-of-options", ref + "^{commit}")
        if result.returncode == 0:
            return result.stdout.strip()
    return None


def relation(left, right):
    """Describe left relative to right. Negative results need complete history."""
    if not left or not right:
        return "unknown"
    if left == right:
        return "same"
    forward = git("merge-base", "--is-ancestor", left, right).returncode
    if forward == 0:
        return "ancestor"
    backward = git("merge-base", "--is-ancestor", right, left).returncode
    if backward == 0:
        return "descendant"
    if forward == backward == 1 and git("rev-parse", "--is-shallow-repository").stdout.strip() == "false":
        return "divergent"
    return "unknown"


def local_publication(number, main):
    if main:
        log = git("log", "-1", "--first-parent", "--merges",
                  f"--grep=^Merge pull request #{number} from ", "--format=%H %P%x09%s", main)
        parents, _, subject = log.stdout.strip().partition("\t")
        parts = parents.split()
        if len(parts) == 3 and subject.startswith(f"Merge pull request #{number} from "):
            merged, base, head = parts
            return {"number": number, "state": "MERGED", "baseRefOid": base,
                    "headRefOid": head, "mergeCommit": {"oid": merged}}


def publication(number, main, snapshot):
    if snapshot:
        row = json.loads(snapshot.read_text())
        source = str(snapshot)
    else:
        row = local_publication(number, main)
        if row:
            return row, "local first-parent PR merge"
        raw = subprocess.check_output(["gh", "pr", "view", str(number), "--json", FIELDS],
                                      text=True, timeout=20, stderr=subprocess.PIPE)
        row = json.loads(raw)
        source = "gh pr view"
    if not isinstance(row, dict) or row["number"] != number or row["state"] not in ("OPEN", "CLOSED", "MERGED"):
        raise ValueError("PR number or state mismatch")
    merge = row.get("mergeCommit")
    if merge is not None and not isinstance(merge, dict):
        raise ValueError("invalid PR merge metadata")
    for oid in (row["headRefOid"], row["baseRefOid"], (merge or {}).get("oid")):
        if oid is not None and not re.fullmatch(r"[0-9a-f]{40}", oid):
            raise ValueError("invalid PR commit hash")
    return row, source


def assessment_at(rev, path):
    result = git("show", f"{rev}:{path}")
    if result.returncode:
        raise ValueError(f"assessment blob unavailable: {rev}:{path}")
    return json.loads(result.stdout).get("current_assessment")


def pr_assessments(row):
    """Only assessments introduced or revised on the published PR branch."""
    base, head = commit(row.get("baseRefOid")), commit(row.get("headRefOid"))
    if not base or not head:
        return {}
    fork = git("merge-base", "--all", base, head).stdout.split()
    if len(fork) != 1:
        return {}
    changes = git("diff", "--name-status", "--no-renames", "--diff-filter=AM", "-z",
                  fork[0], head, "--", "corpus/attempts/*.json")
    if changes.returncode:
        raise ValueError("PR attempt diff unavailable")
    found = {}
    fields = iter(changes.stdout.split("\0")[:-1])
    for status, path in zip(fields, fields):
        assessment = assessment_at(head, path)
        if assessment and (status == "A" or assessment != assessment_at(fork[0], path)):
            found[path] = assessment
    return found


def scoped_prs(assessment):
    return {int(n) for n in SCOPED_PR.findall(assessment.get("evidence", ""))}


def owning_pr(path, assessment, main):
    references = scoped_prs(assessment)
    if len(references) == 1:
        return references.pop()
    if main and not references and assessment.get("reviewed_revision"):
        # Some assessments predate the PR number. Locate their introduction on main.
        log = git("log", "-1", "--first-parent", "--diff-merges=first-parent", "--no-patch",
                  "-S" + assessment["reviewed_revision"], "--format=%s", main, "--", path)
        match = PR_MERGE.fullmatch(log.stdout.strip())
        if match:
            number = int(match[1])
            row = local_publication(number, main)
            if row and pr_assessments(row).get(path) == assessment:
                return number


def comparison(assessment, reported, publication_head, main):
    """Suggest net report-side changes beyond known integration baselines."""
    reviewed = commit(assessment["reviewed_revision"])
    status = relation(reported, reviewed)
    result = {"recorded": assessment, "reported_to_reviewed": status}
    if status in ("ancestor", "same"):
        result["review_guidance"] = "No later worker changes in this report. Consult the recorded review for its exact scope."
        return result
    if status != "descendant":
        result["review_guidance"] = "Unresolved revision relationship. Compare the deliveries before reusing the assessment."
        return result

    # A worker can continue from the integration branch. Avoid attributing
    # its intervening merges and publication bookkeeping to the new report.
    result["changes_since_review_command"] = f"git diff --stat {reviewed} {reported}"
    bases = {reviewed}
    for tip in (publication_head, main):
        if tip:
            base = git("merge-base", "--all", reported, tip)
            if base.returncode not in (0, 1):
                result["review_guidance"] = "Integration baseline unavailable. Inspect history before assigning changes."
                return result
            bases.update(base.stdout.split())
    newest = [base for base in bases
              if all(relation(other, base) in ("same", "ancestor") for other in bases)]
    if len(newest) != 1:
        result["review_guidance"] = "No unique comparison base. Inspect the histories before reusing the assessment."
        return result
    base = newest[0]
    result["report_diff_base"] = base
    diff = git("diff", "--name-only", "-z", base, reported, "--")
    if diff.returncode:
        result["review_guidance"] = "Changed paths unavailable. Inspect the revisions before reusing the assessment."
        return result
    paths = diff.stdout.split("\0")[:-1]
    result["changed_report_paths"] = paths
    if paths:
        result["review_guidance"] = "Inspect the listed report-side changes for effects on the recorded scope."
    else:
        result["review_guidance"] = "No net report-side file changes against the comparison base."
    if reviewed != base:
        result["integrated_changes_command"] = f"git diff --stat {reviewed} {base}"
        result["review_guidance"] += " Inspect intervening integration changes for effects on the same scope."
        delta = git("diff", "--name-only", "-z", reviewed, base, "--")
        if delta.returncode == 0:
            result["integrated_paths_changed_since_review"] = delta.stdout.split("\0")[:-1]
    return result


def reconcile(args):
    reported = commit(args.reported)
    main = commit(args.main)
    report = {"reported": reported or args.reported, "main_ref": args.main, "main": main,
              "reported_to_main": relation(reported, main), "assessments": {}, "uncertainties": []}
    gaps = report["uncertainties"]
    if not reported or not main:
        gaps.append("Reported or main commit unavailable locally.")
    number = args.pr
    head = None
    selected = set()
    checkout = commit("HEAD")
    if args.attempt:
        for path, record in load_dir("attempts", Path.cwd()):
            name = path.relative_to(Path.cwd()).as_posix()
            if args.attempt in (name, path.stem, record["id"], record.get("legacy_id"), record.get("label")):
                selected.add(name)
                try:
                    assessment = assessment_at(checkout, name)
                    if assessment:
                        number = owning_pr(name, assessment, main)
                except ValueError as exc:
                    gaps.append(str(exc))
                break
    else:
        # Discover explicit references in the same committed data we will cite.
        for revision in dict.fromkeys((checkout, main)):
            if not revision:
                continue
            refs = git("grep", "-l", "-z", "-E", f"PR(-| #){number}([^0-9]|$)",
                       revision, "--", "corpus/attempts/*.json")
            if refs.returncode not in (0, 1):
                gaps.append(f"PR citation lookup unavailable at {revision}.")
            for match in refs.stdout.split("\0")[:-1]:
                name = match.split(":", 1)[1]
                assessment = assessment_at(revision, name)
                if assessment and number in scoped_prs(assessment):
                    selected.add(name)
    if number:
        try:
            row, source = publication(number, main, args.snapshot)
            head = commit(row["headRefOid"])
            merged = (row.get("mergeCommit") or {}).get("oid")
            merge = commit(merged)
            report["pr"] = {"number": number, "source": source, "state": row["state"],
                            "head": row["headRefOid"], "merge": merged,
                            "reported_to_head": relation(reported, head),
                            "reported_to_merge": relation(reported, merge),
                            "head_to_merge": relation(head, merge), "merge_to_main": relation(merge, main)}
            if not head:
                gaps.append("Published head unavailable locally.")
            elif report["pr"]["reported_to_head"] == "divergent":
                gaps.append("Report and published head diverge. Content equivalence is unresolved.")
            if row["state"] == "MERGED" and report["pr"]["head_to_merge"] not in ("same", "ancestor"):
                gaps.append("Merge does not confirm head ancestry locally (possible squash, rewrite or missing history).")
            if row["state"] == "MERGED" and report["pr"]["merge_to_main"] not in ("same", "ancestor"):
                gaps.append("The selected local main revision does not confirm integration of this merge.")
            if not args.attempt:
                selected.update(pr_assessments(row))
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
            gaps.append(f"PR #{number} lookup unresolved: {exc}")
    else:
        gaps.append("No unique published PR identified for the selected assessment. Supply --pr for a PR lookup.")
    for name in sorted(selected):
        versions = []
        for role, revision in (("published_head", head), ("main", main), ("checkout_head", checkout)):
            if not revision:
                continue
            try:
                assessment = assessment_at(revision, name)
            except ValueError as exc:
                gaps.append(str(exc))
                continue
            if not assessment:
                continue
            same = next((v for v in versions if v["recorded"] == assessment), None)
            if same is None:
                same = comparison(assessment, reported, head, main)
                same["sources"] = {}
                versions.append(same)
                if assessment["review"] != "accepted_qualified":
                    same["review_guidance"] = (f"Recorded review is {assessment['review']}. "
                                               "This record supplies no acceptance. " + same["review_guidance"])
                if same["reported_to_reviewed"] in ("unknown", "divergent"):
                    gaps.append(f"Coverage by {revision}:{name} is unresolved.")
            same["sources"][role] = revision
        if versions:
            report["assessments"][name] = versions
    if not report["assessments"]:
        gaps.append("No scoped assessment located for this lookup.")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reported", help="worker commit")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--pr", type=int, help="published PR number")
    group.add_argument("--attempt", help="owning attempt path, stem, UUID, legacy ID or label in checkout")
    parser.add_argument("--main", default="origin/main", help="local main ref (default: origin/main)")
    parser.add_argument("--snapshot", type=Path, help=f"offline gh pr view JSON with fields {FIELDS}")
    args = parser.parse_args()
    if args.pr is not None and args.pr < 1:
        parser.error("--pr must be positive")
    try:
        if args.snapshot:
            args.snapshot = args.snapshot.resolve()
        root = git("rev-parse", "--show-toplevel")
        if root.returncode:
            raise ValueError(root.stderr.strip())
        os.chdir(root.stdout.strip())
        print(json.dumps(reconcile(args), indent=2, ensure_ascii=False))
    except (OSError, CorpusError, ValueError) as exc:
        sys.exit(f"worker report lookup failed: {exc}")


if __name__ == "__main__":
    main()
