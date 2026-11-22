#!/usr/bin/env python3
"""Agent-guided discovery recipe helpers (#1832; docs/discover.md, "Agent-guided
blueprint recipe").

Two subcommands, both advisory. Neither writes a corpus record or proves anything.

diagnose  Read a `truth --json discover` report and the corpus. For each chosen
          target, list the verified arguments that already conclude it (known
          derivations), whether the search retrieved their premises as
          candidates, and which of their binders `truth discover` could not
          identify with a binder of the target or of an earlier premise. The
          identification rule mirrors `bind` in `scripts/Discover.lean`: same
          binder name declared in the same module, or the same whole-binder
          sense tag; a carrier of the same name in another module is the
          flagged by-name fallback. Binder types are not compared, so a listed
          identification is necessary, not sufficient. Needs a binder export:

              lake env lean --run scripts/DiscoverBinders.lean TruthCore DECLS > binders.jsonl

          The verdict per target joins the gaps its known derivations show:
            retrieval      some premise of the derivation was not retrieved;
            identification the derivation needs a binder identification that
                           no tag records (listed: a fresh binder whose name an
                           earlier binder of another module has, or a second
                           carrier; these are the exact sense or bridge
                           obligations);
          or is one of
            search         some known derivation was retrieved and fully
                           identifiable but not composed (a proof-search gap);
            no-known       no verified argument concludes the target, so the
                           failure is a search gap or a substantive gap, to be
                           told apart by a guided lemma attempt;
            found          the search closed the goal (see the report).

oracle    Run `scripts/run-discovery.sh` with a TEMPORARY overlay of whole-binder
          sense tags (a JSON list of {"sense", "declaration", "parameter"}) in
          a temporary detached `git worktree` of the repository, never in the
          repository itself. The worktree is created at HEAD under `--scratch`
          (default: the repository's parent directory), receives the
          repository's uncommitted and untracked files, shares the built
          `.lake` through a symlink (the Lean sources are unchanged, so Lake
          only replays) and uses the repository's `target/release/truth`. The
          overlay is written into the worktree's corpus only; the worktree is
          removed afterwards, on failure and on SIGTERM/SIGHUP too (a SIGKILL
          can leave it behind: `git worktree prune` and the scratch directory
          then remove it, and the repository's corpus is untouched either way).
          `sense` is an existing sense id or label, or a new label prefixed
          `TEMP_` (written into a temporary disambiguation record of the
          worktree). Reports go to `$TRUTH_DISCOVER_REPORT_DIR`, default the
          repository's `.cache/discover`; each run directory keeps
          `overlay.json` beside the report. Every finding of such a run is
          conditional on the overlay's identifications: they are the
          obligations a reviewed sense tag or a bridge premise must discharge
          before any finding can be recorded.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load_records(root: Path, kind: str) -> dict[str, dict]:
    records = {}
    for path in sorted((root / "corpus" / kind).glob("*.json")):
        record = json.loads(path.read_text())
        records[record["id"]] = record
    return records


def whole_tags(root: Path) -> dict[tuple[str, str], str]:
    """(declaration, binder) -> sense id, whole-binder tags only."""
    tags = {}
    for path in sorted((root / "corpus" / "disambiguations").glob("*.json")):
        record = json.loads(path.read_text())
        for sense in record.get("senses", []):
            for entry in sense.get("lean_parameters") or []:
                if entry.get("arguments"):
                    continue
                tags[(entry["declaration"], entry["parameter"])] = sense["id"]
    return tags


def load_binders(path: Path) -> dict[str, dict]:
    out = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            row = json.loads(line)
            out[row["declaration"]] = row
    return out


def simulate(declarations: list[str], binders: dict[str, dict],
             tags: dict[tuple[str, str], str]) -> list[dict]:
    """Bind the declarations in order (target first) as `Discover.lean` does,
    ignoring binder types. Per declaration after the first: `fresh`, the
    binders that became new outer binders; `blocked`, those of them that would
    need an identification no tag records (a fresh binder whose name an earlier
    outer binder of another module already has, or a fresh carrier while a
    carrier is already bound); and `by_name`, the flagged carrier fallback."""
    outer: list[tuple[str, str, str, str | None, bool]] = []  # name, decl, module, sense, carrier
    report = []
    for index, decl in enumerate(declarations):
        row = binders.get(decl)
        if row is None or "binders" not in row:
            report.append({"declaration": decl, "error": "no binder export",
                           "fresh": [], "blocked": [], "by_name": []})
            continue
        module = row["module"]
        fresh, blocked, by_name = [], [], []
        for name, carrier, instance in row["binders"]:
            if instance:
                continue
            sense = tags.get((decl, name))
            match = None
            for o_name, o_decl, o_module, o_sense, _ in outer:
                authored = (o_name == name and o_module == module) or (
                    sense is not None and o_sense == sense)
                if authored:
                    match = ("authored", o_decl)
                    break
                if carrier and o_name == name:
                    match = ("by_name", o_decl)
                    break
            if match is None:
                clash = any(o_name == name for o_name, *_ in outer) or (
                    carrier and any(o_carrier for *_, o_carrier in outer))
                outer.append((name, decl, module, sense, carrier))
                if index > 0:
                    fresh.append(name)
                    if clash:
                        blocked.append(name)
            elif match[0] == "by_name":
                by_name.append(f"{name} (= {match[1]}.{name})")
        if index > 0:
            report.append({"declaration": decl, "module": module, "fresh": fresh,
                           "blocked": blocked, "by_name": by_name})
    return report


def known_derivations(target: str, arguments: dict, results: dict) -> list[dict]:
    verified = {r.get("argument_id") for r in results.values()}
    return [a for a in arguments.values()
            if a.get("conclusion_statement_id") == target and a["id"] in verified]


def diagnose(args: argparse.Namespace) -> int:
    root = Path(args.root)
    report = json.loads(Path(args.report).read_text())
    statements = load_records(root, "statements")
    arguments = load_records(root, "arguments")
    results = load_records(root, "results")
    tags = whole_tags(root)
    binders = load_binders(Path(args.binders)) if args.binders else {}
    wanted = set(args.target or [])
    out = []
    for finding in report["findings"]:
        target = finding["target"]["statement_id"]
        if wanted and not any(target.startswith(w) for w in wanted):
            continue
        decl = statements[target].get("lean_declaration", "")
        target_names = {b[0] for b in binders.get(decl, {}).get("binders", [])}
        candidates = set(finding.get("candidates", []))
        rows = []
        for argument in known_derivations(target, arguments, results):
            premises = argument.get("premise_statement_ids", [])
            missing = [p for p in premises if p not in candidates]
            decls = [decl] + [statements[p].get("lean_declaration", "") for p in premises]
            binding = simulate(decls, binders, tags) if binders else []
            # A fresh binder whose name the target also binds is an
            # identification the search refused (e.g. B vs Being, Has vs InAct
            # need a mapping; CausesIn in another module needs a tag).
            obligations = [f"{entry['declaration']}.{name}"
                           for entry in binding for name in entry.get("blocked", [])]
            rows.append({
                "argument": argument["id"], "label": argument.get("label", ""),
                "premises": premises, "not_retrieved": missing,
                "binding": binding, "unidentified": obligations,
                "target_binders": sorted(target_names)})
        if finding["kind"] in ("discovery", "incompatibility") or (
                finding.get("lean") or {}).get("closed"):
            verdict = "found"
        elif not rows:
            verdict = "no-known"
        else:
            gaps = set()
            for r in rows:
                if r["not_retrieved"]:
                    gaps.add("retrieval")
                if r["unidentified"]:
                    gaps.add("identification")
            # A known derivation free of both gaps that was not composed is a
            # proof-search gap.
            if any(not r["not_retrieved"] and not r["unidentified"] for r in rows):
                verdict = "search"
            else:
                verdict = "+".join(sorted(gaps))
        out.append({"target": target, "declaration": decl, "kind": finding["kind"],
                    "verdict": verdict, "known": rows})
    if args.json:
        print(json.dumps(out, indent=2))
        return 0
    for item in out:
        print(f"{item['target'][:8]} {item['declaration'].split('.')[-1]}: "
              f"{item['kind']}, verdict {item['verdict']}")
        for row in item["known"]:
            print(f"  known {row['argument'][:8]} {row['label'][:80]}")
            if row["not_retrieved"]:
                print(f"    not retrieved: {', '.join(p[:8] for p in row['not_retrieved'])}")
            for entry in row["binding"]:
                if entry.get("blocked") or entry.get("by_name"):
                    print(f"    {entry['declaration']}: needs identification {entry.get('blocked')}"
                          f"{'; carrier by name ' + str(entry['by_name']) if entry.get('by_name') else ''}")
    return 0


def git(root: Path, *argv: str, check: bool = True) -> str:
    return subprocess.run(["git", "-C", str(root), *argv], check=check,
                          capture_output=True, text=True).stdout


def apply_overlay(directory: Path, overlay: list[dict]) -> None:
    """Write the overlay into the disambiguation records of `directory`."""
    by_key: dict[str, tuple[Path, dict]] = {}
    records: dict[Path, dict] = {}
    for path in sorted(directory.glob("*.json")):
        record = json.loads(path.read_text())
        records[path] = record
        for sense in record.get("senses", []):
            by_key[sense["id"]] = (path, sense)
            by_key[sense.get("label", "")] = (path, sense)
    changed: set[Path] = set()
    temp_senses: dict[str, dict] = {}
    for entry in overlay:
        key = entry["sense"]
        tag = {"declaration": entry["declaration"], "parameter": entry["parameter"]}
        if key.startswith("TEMP_"):
            sense = temp_senses.setdefault(key, {"id": f"temporary-{key.lower()}",
                                                 "label": key, "lean_parameters": []})
            sense["lean_parameters"].append(tag)
            continue
        if key not in by_key:
            raise SystemExit(f"unknown sense {key}")
        path, sense = by_key[key]
        params = sense.setdefault("lean_parameters", [])
        if tag not in params:
            params.append(tag)
            changed.add(path)
    for path in changed:
        path.write_text(json.dumps(records[path], indent=2, ensure_ascii=False) + "\n")
    # One temporary record per temporary sense: each is its own term, so two
    # temporary senses never count as two senses of one term.
    for label, sense in temp_senses.items():
        record = {"id": f"temporary-discover-oracle-{label.lower()}",
                  "label": f"Temporary discover oracle {label}",
                  "term": f"temporary {label.lower()}",
                  "term_label": f"temporary {label.lower()}",
                  "resolution": "Temporary oracle overlay of scripts/discover_blueprint.py "
                                "in a disposable worktree. Not a corpus record.",
                  "sense_definition_ids": [], "senses": [sense]}
        (directory / f"zz-temporary-discover-oracle-{label.lower()}.json").write_text(
            json.dumps(record, indent=2) + "\n")


def oracle(args: argparse.Namespace) -> int:
    root = Path(args.root).resolve()
    overlay = json.loads(Path(args.tags).read_text())
    scratch = Path(args.scratch).resolve() if args.scratch else root.parent
    work = Path(tempfile.mkdtemp(prefix="discover-oracle-", dir=scratch))
    tree = work / "tree"
    child = None

    def stop(signum, _frame):
        raise SystemExit(128 + signum)

    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, stop)
    try:
        git(root, "worktree", "add", "--detach", "--quiet", str(tree), "HEAD")
        # Carry the repository's uncommitted state into the worktree.
        listing = git(root, "ls-files", "-z", "--modified", "--others", "--exclude-standard")
        deleted = set(git(root, "ls-files", "-z", "--deleted").split("\0"))
        for name in filter(None, listing.split("\0")):
            target = tree / name
            if name in deleted:
                target.unlink(missing_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / name, target)
        if (root / ".lake").exists() and not (tree / ".lake").exists():
            (tree / ".lake").symlink_to(root / ".lake", target_is_directory=True)
        apply_overlay(tree / "corpus" / "disambiguations", overlay)
        env = dict(os.environ)
        env.setdefault("TRUTH_DISCOVER_BIN", str(root / "target" / "release" / "truth"))
        report_dir = Path(env.setdefault("TRUTH_DISCOVER_REPORT_DIR",
                                         str(root / ".cache" / "discover")))
        before = set(report_dir.glob("*")) if report_dir.exists() else set()
        child = subprocess.Popen(["bash", str(tree / "scripts" / "run-discovery.sh"), *args.rest],
                                 cwd=tree, env=env, start_new_session=True)
        code = child.wait()
        after = set(report_dir.glob("*")) if report_dir.exists() else set()
        for run_dir in after - before:
            (run_dir / "overlay.json").write_text(json.dumps(overlay, indent=2) + "\n")
        return code
    finally:
        if child is not None and child.poll() is None:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            child.wait()
        # Drop the shared-build symlink first, so that nothing below can
        # reach the repository's own `.lake`.
        lake = tree / ".lake"
        if lake.is_symlink():
            lake.unlink()
        git(root, "worktree", "remove", "--force", str(tree), check=False)
        shutil.rmtree(work, ignore_errors=True)
        git(root, "worktree", "prune", check=False)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", default=str(ROOT))
    sub = parser.add_subparsers(dest="command", required=True)
    d = sub.add_parser("diagnose")
    d.add_argument("report")
    d.add_argument("--binders", help="JSON lines from scripts/DiscoverBinders.lean")
    d.add_argument("--target", action="append", help="statement id prefix (repeatable)")
    d.add_argument("--json", action="store_true")
    o = sub.add_parser("oracle")
    o.add_argument("tags", help="JSON list of {sense, declaration, parameter}")
    o.add_argument("--scratch", help="parent directory of the temporary worktree "
                                     "(default: the repository's parent directory)")
    o.add_argument("rest", nargs=argparse.REMAINDER, help="-- then run-discovery.sh arguments")
    args = parser.parse_args()
    if args.command == "oracle":
        if args.rest and args.rest[0] == "--":
            args.rest = args.rest[1:]
        return oracle(args)
    return diagnose(args)


if __name__ == "__main__":
    sys.exit(main())
