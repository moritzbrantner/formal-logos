#!/usr/bin/env python3
"""Benchmark `truth brief`/`truth novelty` (#1643) against the documented lookup workflow (#1644).

The answer key is `scripts/testdata/retrieval-benchmark.json`: hand-pinned
notes, issues, records and objections per research question, located without
the system under test. Both workflows run on this checkout with the same
offline issue snapshot (minus the items that state the benchmark's answers):

* baseline: the documented pre-#1643 route (AGENTS.md "Premise dossiers and
  attempts", docs/notes/research-index.md): `truth index search` for the
  case's words (notes are projected since #952), then `truth related` and
  `truth dossier --issues-from` for each seed statement (the case's own seeds,
  else up to two statements the search surfaced), and `truth context` for a
  named argument or result;
* candidate: the single `truth brief` or `truth novelty` call of the case.

A reference counts as surfaced when its token appears in the workflow's
combined output (a lexical proxy, as in `context_benchmark.py`); this measures
retrieval, not understanding. Distinction patterns test whether the output
itself states a boundary (conditional consequence, unknown issue data, stale
snapshot, open rival). Nothing here changes a premise, frontier or status.

    python3 scripts/retrieval_benchmark.py --snapshot SNAPSHOT.json [--case ID]... [--json OUT]

SNAPSHOT is a `gh issue list`/`gh pr list --state all` capture (see the
fixture's `snapshot.command`). `--check-key` only validates that every pinned
reference resolves in this checkout and snapshot.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "scripts" / "testdata" / "retrieval-benchmark.json"
TRUTH = ROOT / "target" / "release" / "truth"  # --truth selects another build
STALE_CAPTURE = "2026-01-01T00:00:00Z"


def run(args: list[str]) -> tuple[str, float]:
    start = time.perf_counter()
    done = subprocess.run([str(TRUTH), *args], cwd=ROOT, capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    if done.returncode not in (0, 3):
        raise SystemExit(f"truth {' '.join(args)} exited {done.returncode}: {done.stderr.strip()}")
    return done.stdout + done.stderr, elapsed


def snapshots(source: Path, exclude: set[int], scratch: Path) -> dict[str, Path | None]:
    data = json.loads(source.read_text(encoding="utf-8"))
    items = data["items"] if isinstance(data, dict) else data
    captured = data.get("captured_at") if isinstance(data, dict) else None
    kept = [item for item in items if item.get("number") not in exclude]
    full = scratch / "snapshot.json"
    full.write_text(json.dumps({"captured_at": captured, "items": kept}), encoding="utf-8")
    stale = scratch / "snapshot-stale.json"
    stale.write_text(json.dumps({"captured_at": STALE_CAPTURE, "items": kept}), encoding="utf-8")
    # `dossier --issues-from` (the baseline) reads only the plain `gh` array form.
    plain = scratch / "snapshot-array.json"
    plain.write_text(json.dumps(kept), encoding="utf-8")
    return {"full": full, "stale": stale, "none": None, "array": plain}


def search_seeds(outputs: list[str], limit: int = 2) -> list[str]:
    """Statements a worker would open next: statement hits first, then statements linked from note hits."""
    direct, linked = [], []
    for output in outputs:
        try:
            hits = json.loads(output)
        except json.JSONDecodeError:
            continue
        for hit in hits:
            if hit.get("kind") == "statements":
                direct.append(hit["id"])
            for link in hit.get("links") or []:
                if link.startswith("statements:"):
                    linked.append(link.split(":", 1)[1])
    seeds: list[str] = []
    for sid in direct + linked:
        if sid not in seeds:
            seeds.append(sid)
    return seeds[:limit]


def baseline(case: dict, snapshot: Path | None, plain: Path) -> list[tuple[list[str], str, float]]:
    spec = case["baseline"]
    calls = []
    for words in spec.get("search", []):
        args = ["index", "search", words]
        calls.append((args, *run(args)))
    seeds = list(spec.get("seeds") or search_seeds([out for _, out, _ in calls]))
    issues = ["--issues-from", str(plain)] if snapshot else []
    for sid in seeds:
        for args in (["related", sid], ["dossier", sid, *issues]):
            calls.append((args, *run(args)))
    for target in spec.get("context", []):
        args = ["context", target]
        calls.append((args, *run(args)))
    return calls


def candidate(case: dict, snapshot: Path | None) -> list[tuple[list[str], str, float]]:
    args = list(case["candidate"]) + (["--issues-from", str(snapshot)] if snapshot else [])
    return [(args, *run(args))]


def found(ref: str, text: str) -> bool:
    if ref.startswith("#"):
        return re.search(re.escape(ref) + r"(?!\d)", text) is not None
    return ref in text


def classification(text: str) -> str | None:
    match = re.search(r"^Classification: (\S+)", text, re.M)
    return match.group(1) if match else None


def score(case: dict, calls: list, verdict: bool) -> dict:
    text = "\n".join(out for _, out, _ in calls)
    refs = case.get("refs", [])
    hits = {ref["ref"]: found(ref["ref"], text) for ref in refs}
    primary = [ref["ref"] for ref in refs if ref.get("primary")]
    distinctions = {}
    for item in case.get("distinctions", []):
        ok = True
        if "present" in item:
            ok = ok and re.search(item["present"], text) is not None
        if "absent" in item:
            ok = ok and re.search(item["absent"], text) is None
        distinctions[item["name"]] = ok
    row = {
        "case": case["id"],
        "category": case["category"],
        "held_out": bool(case.get("held_out")),
        "calls": len(calls),
        "bytes": len(text.encode("utf-8")),
        "seconds": round(sum(t for _, _, t in calls), 2),
        "refs": hits,
        "missed": [ref for ref, ok in hits.items() if not ok],
        "primary": primary,
        "primary_missed": [ref for ref in primary if not hits[ref]],
        "distinctions": distinctions,
        "commands": [" ".join(args) for args, _, _ in calls],
    }
    if verdict:
        got = classification(text)
        row["classification"] = got
        if "classification" in case:
            row["classification_ok"] = got in case["classification"]
    return row


def summarize(rows: list[dict]) -> dict:
    def ratio(num: int, den: int) -> str:
        return f"{num}/{den}"

    refs = [(case_ref, ok, row) for row in rows for case_ref, ok in row["refs"].items()]
    kinds: dict[str, list[int]] = {}
    for row in rows:
        for ref in row["_kinds"]:
            kinds.setdefault(ref[1], [0, 0])
            kinds[ref[1]][1] += 1
            kinds[ref[1]][0] += int(row["refs"][ref[0]])
    known = [row for row in rows if row["category"] != "negative-control"]
    # False novelty: the output shows none of the primary prior work (or says no-match-found),
    # so a worker reading it would plausibly report the question as unexplored.
    false_novelty = [row["case"] for row in known
                     if (row["primary"] and len(row["primary_missed"]) == len(row["primary"]))
                     or row.get("classification") == "no-match-found"]
    missed_key = [row["case"] for row in known if row["primary_missed"]]
    distinctions = [ok for row in rows for ok in row["distinctions"].values()]
    negatives = [row for row in rows if row["category"] == "negative-control" and "classification_ok" in row]
    return {
        "recall": ratio(sum(ok for _, ok, _ in refs), len(refs)),
        "recall_by_kind": {kind: ratio(*value) for kind, value in sorted(kinds.items())},
        "false_novelty_cases": false_novelty,
        "false_novelty_rate": ratio(len(false_novelty), len(known)),
        "primary_reference_missed_cases": missed_key,
        "missed_known_work_rate": ratio(sum(not ok for _, ok, row in refs if row["category"] != "negative-control"),
                                        sum(1 for _, _, row in refs if row["category"] != "negative-control")),
        "distinctions": ratio(sum(distinctions), len(distinctions)),
        "negative_control_verdicts": ratio(sum(row["classification_ok"] for row in negatives), len(negatives)) if negatives else "no verdict",
        "bytes": sum(row["bytes"] for row in rows),
        "calls": sum(row["calls"] for row in rows),
        "seconds": round(sum(row["seconds"] for row in rows), 1),
    }


def check_key(fixture: dict, snapshot: Path) -> list[str]:
    data = json.loads(snapshot.read_text(encoding="utf-8"))
    numbers = {item["number"] for item in (data["items"] if isinstance(data, dict) else data)}
    corpus = "\n".join(path.name for path in (ROOT / "corpus").rglob("*.json"))
    ids = set(re.findall(r"[0-9a-f]{8}-[0-9a-f]{4}", "\n".join(
        path.read_text(encoding="utf-8")[:400] for path in (ROOT / "corpus").rglob("*.json"))))
    errors = []
    for case in fixture["cases"]:
        for ref in case.get("refs", []):
            token = ref["ref"]
            if ref["kind"] == "note":
                ok = (ROOT / "docs" / "notes" / token).is_file()
            elif ref["kind"] == "issue":
                ok = int(token[1:]) in numbers
            else:
                ok = token in corpus or any(i.startswith(token) for i in ids)
            if not ok:
                errors.append(f"{case['id']}: pinned reference {token} ({ref['kind']}) does not resolve")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--json", type=Path)
    parser.add_argument("--check-key", action="store_true")
    parser.add_argument("--truth", type=Path, help="truth binary (default target/release/truth)")
    args = parser.parse_args(argv)
    if args.truth:
        global TRUTH
        TRUTH = args.truth.resolve()
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    errors = check_key(fixture, args.snapshot)
    if errors or args.check_key:
        print("\n".join(errors) or f"answer key resolves: {len(fixture['cases'])} cases")
        return 1 if errors else 0
    cases = [case for case in fixture["cases"] if not args.case or case["id"] in args.case]
    with tempfile.TemporaryDirectory() as tmp:
        snaps = snapshots(args.snapshot, set(fixture["snapshot"]["exclude_numbers"]), Path(tmp))
        run(["index", "build"])  # both workflows then reuse one warm index
        report = {"revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                  "baseline": [], "candidate": []}
        for case in cases:
            snapshot = snaps[case.get("snapshot", "full")]
            kinds = [(ref["ref"], ref["kind"]) for ref in case.get("refs", [])]
            for name, calls, verdict in (("baseline", lambda: baseline(case, snapshot, snaps["array"]), False),
                                         ("candidate", lambda: candidate(case, snapshot), True)):
                row = score(case, calls(), verdict)
                row["_kinds"] = kinds
                report[name].append(row)
    report["summary"] = {name: summarize(report[name]) for name in ("baseline", "candidate")}
    for name in ("baseline", "candidate"):
        for row in report[name]:
            del row["_kinds"]
    print(f"revision {report['revision']}")
    print(f"{'case':38} {'baseline recall/KB/s':>22} {'candidate recall/KB/s':>23}  candidate verdict")
    for base, cand in zip(report["baseline"], report["candidate"]):
        def cell(row):
            total = len(row["refs"])
            return f"{total - len(row['missed'])}/{total} {row['bytes'] / 1024:.0f} {row['seconds']:.1f}"
        print(f"{base['case']:38} {cell(base):>22} {cell(cand):>23}  {cand.get('classification') or ''}")
    for name in ("baseline", "candidate"):
        print(f"\n{name}: {json.dumps(report['summary'][name], ensure_ascii=False)}")
        for row in report[name]:
            failed = [k for k, ok in row["distinctions"].items() if not ok]
            if row["missed"] or failed or row.get("classification_ok") is False:
                print(f"  {row['case']}: missed {row['missed']} distinctions failed {failed}"
                      + (f" verdict {row['classification']}" if row.get("classification_ok") is False else ""))
    if args.json:
        args.json.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
