#!/usr/bin/env python3
"""Agent-guided discovery recipe helpers (#1832; docs/discover.md, "Agent-guided
blueprint pilot").

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
          sense tags (a JSON list of {"sense", "declaration", "parameter"}),
          restoring the disambiguation records afterwards, even on failure.
          `sense` is an existing sense id or label, or a new label prefixed
          `TEMP_` (written into a temporary disambiguation record). Every
          finding of such a run is conditional on the overlay's
          identifications: they are the obligations a sense record or a bridge
          premise must discharge before any finding can be recorded. The run
          directory keeps `overlay.json` beside the report.
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
TEMP_PREFIX = "zz-temporary-discover-oracle-"


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


def oracle(args: argparse.Namespace) -> int:
    root = Path(args.root)
    overlay = json.loads(Path(args.tags).read_text())
    directory = root / "corpus" / "disambiguations"
    leftovers = sorted(directory.glob(TEMP_PREFIX + "*"))
    if leftovers:
        sys.exit(f"{leftovers[0]} exists: a previous oracle run was interrupted; remove it first")
    written: list[Path] = []
    # A terminated run must still restore the records: turn SIGTERM/SIGHUP
    # into an exception so that `finally` runs.
    def stop(signum, _frame):
        raise SystemExit(128 + signum)
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, stop)
    backup = Path(tempfile.mkdtemp(prefix="discover-oracle-"))
    originals: dict[Path, bytes] = {}
    try:
        by_label = {}
        records = {}
        for path in sorted(directory.glob("*.json")):
            record = json.loads(path.read_text())
            records[path] = record
            for sense in record.get("senses", []):
                by_label[sense["id"]] = (path, sense)
                by_label[sense.get("label", "")] = (path, sense)
        temp_senses: dict[str, dict] = {}
        for entry in overlay:
            sense_key = entry["sense"]
            tag = {"declaration": entry["declaration"], "parameter": entry["parameter"]}
            if sense_key.startswith("TEMP_"):
                sense = temp_senses.setdefault(sense_key, {
                    "id": f"temporary-{sense_key.lower()}", "label": sense_key,
                    "lean_parameters": []})
                sense["lean_parameters"].append(tag)
                continue
            if sense_key not in by_label:
                sys.exit(f"unknown sense {sense_key}")
            path, sense = by_label[sense_key]
            if path not in originals:
                originals[path] = path.read_bytes()
                shutil.copy(path, backup / path.name)
            params = sense.setdefault("lean_parameters", [])
            if tag not in params:
                params.append(tag)
        for path in originals:
            path.write_text(json.dumps(records[path], indent=2, ensure_ascii=False) + "\n")
        # One temporary record per temporary sense: each is its own term, so
        # two temporary senses never count as two senses of one term.
        for label, sense in temp_senses.items():
            path = directory / f"{TEMP_PREFIX}{label.lower()}.json"
            record = {"id": f"temporary-discover-oracle-{label.lower()}",
                      "label": f"Temporary discover oracle {label}",
                      "term": f"temporary {label.lower()}",
                      "term_label": f"temporary {label.lower()}",
                      "resolution": "Temporary oracle overlay of scripts/discover_blueprint.py; "
                                    "removed after the run. Not a corpus record.",
                      "sense_definition_ids": [], "senses": [sense]}
            path.write_text(json.dumps(record, indent=2) + "\n")
            written.append(path)
        env = dict(os.environ)
        report_dir = Path(env.get("TRUTH_DISCOVER_REPORT_DIR", root / ".cache" / "discover"))
        before = set(report_dir.glob("*")) if report_dir.exists() else set()
        child = subprocess.Popen(["bash", str(root / "scripts" / "run-discovery.sh"), *args.rest],
                                 cwd=root, env=env, start_new_session=True)
        try:
            code = child.wait()
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGTERM)
                child.wait()
        after = set(report_dir.glob("*")) if report_dir.exists() else set()
        for run_dir in after - before:
            (run_dir / "overlay.json").write_text(json.dumps(overlay, indent=2) + "\n")
        return code
    finally:
        for path, data in originals.items():
            path.write_bytes(data)
        for path in written:
            path.unlink(missing_ok=True)
        shutil.rmtree(backup, ignore_errors=True)


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
    o.add_argument("rest", nargs=argparse.REMAINDER, help="-- then run-discovery.sh arguments")
    args = parser.parse_args()
    if args.command == "oracle":
        if args.rest and args.rest[0] == "--":
            args.rest = args.rest[1:]
        return oracle(args)
    return diagnose(args)


if __name__ == "__main__":
    sys.exit(main())
