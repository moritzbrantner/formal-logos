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

repair    (#1833) Classify each goal of a report that did not yield an admissible
          discovery into the alternative diagnoses
            a  tactic, selection or budget;
            b  malformed goal or missing lemma;
            c  carrier or sense misidentification;
            d  inconsistent or vacuous bundle;
            e  a missing substantive premise;
            f  unknown;
          each `supported`, `possible`, `excluded` (for the exact bundle tested)
          or `not indicated`, with the signals behind it. A failed search
          proves none of them. Then list the evidence-based retry actions in
          priority order: reuse a verified lemma, try the premises of a
          verified argument that retrieval missed, split through an existing
          intermediate statement, retry without the by-name carrier fallback,
          test an exact one-point countermodel, raise the budget once, or
          report an OPEN bridge or a blocker. Every premise is an existing
          corpus statement; nothing is weakened, strengthened, tagged or
          identified by name. Guards refuse a support cycle, a repeated solver
          input and attempts beyond the cap.

retry     Execute one planned action (`--action ID`), or the next admissible
          ones (`--auto N`), on the exact bundle: `#discover` or the
          countermodel probe `scripts/DiscoverRepair.lean` over the same
          binding as `truth discover`, run once per solver input under the
          heavy-job lock. Each run is appended to a bounded attempt trace
          (exact goal, premise ids, revision, diagnoses, why the action was
          chosen, the change against the original goal, the outcome). A
          closed goal is assessed offline (P/¬P, incompatibility, by-name
          domain, transcription probe, known composition, `truth semantics`
          preflight, necessity) and stays a raw candidate: only `truth
          discover` certification and the spec path can record it.
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


def known_rows(finding: dict, statements: dict, arguments: dict, results: dict,
               binders: dict, tags: dict) -> list[dict]:
    """The verified arguments concluding the finding's target, with the
    premises the run did not retrieve and the binder identifications that no
    tag records."""
    target = finding["target"]["statement_id"]
    decl = statements[target].get("lean_declaration", "")
    target_names = {b[0] for b in binders.get(decl, {}).get("binders", [])}
    candidates = set(finding.get("candidates", []))
    rows = []
    for argument in known_derivations(target, arguments, results):
        premises = argument.get("premise_statement_ids", [])
        missing = [p for p in premises if p not in candidates]
        decls = [decl] + [statements.get(p, {}).get("lean_declaration", "") for p in premises]
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
    return rows


def known_verdict(finding: dict, rows: list[dict]) -> str:
    if finding["kind"] in ("discovery", "incompatibility") or (
            finding.get("lean") or {}).get("closed"):
        return "found"
    if not rows:
        return "no-known"
    gaps = set()
    for r in rows:
        if r["not_retrieved"]:
            gaps.add("retrieval")
        if r["unidentified"]:
            gaps.add("identification")
    # A known derivation free of both gaps that was not composed is a
    # proof-search gap.
    if any(not r["not_retrieved"] and not r["unidentified"] for r in rows):
        return "search"
    return "+".join(sorted(gaps))


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
        rows = known_rows(finding, statements, arguments, results, binders, tags)
        out.append({"target": target, "declaration": decl, "kind": finding["kind"],
                    "verdict": known_verdict(finding, rows), "known": rows})
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


# ---------------------------------------------------------------------------
# Adaptive repair (#1833): diagnoses, evidence-based retry actions, exact
# solver runs and a bounded attempt trace.

TOOL_ROOT = Path(__file__).resolve().parents[1]

DIAGNOSES = {
    "a": "tactic, selection or budget",
    "b": "malformed goal or missing lemma",
    "c": "carrier or sense misidentification",
    "d": "inconsistent or vacuous bundle",
    "e": "missing substantive premise",
    "f": "unknown",
}

# Declarations whose statements Duper's classical logic already supplies: a
# proof that uses Classical.choice in place of the explicit premise is known
# modulo logic, not new (attempt on PR #1848, retrieval miss iii).
LOGIC_DECLARATIONS = {"TruthCore.Logic.ExcludedMiddle"}

MAX_ATTEMPTS_PER_GOAL = 8
# An action whose earlier run had one of these outcomes is not repeated with
# another bundle of the same kind: its diagnosis is already settled.
SETTLING = {"known-bundle": ("closed-known", "closed-candidate"),
            "reuse-lemma": ("closed-known", "closed-candidate"),
            "countermodel": ("countermodel",)}
# An input whose run failed for infrastructure reasons (no output, Lean killed or
# timed out) is not keyed, so it can be rerun, but at most this often.
MAX_FAILURES_PER_INPUT = 2
BUDGET_FACTOR = 4
COUNTERMODEL_BOUNDS = (
    "One-point interpretation: every carrier is Unit and every predicate a "
    "constant (`slots` maps the slot pattern to binders). It shows only that this "
    "formal implication, over exactly these declarations under this plain binding, "
    "fails at one instantiation of its outer binders. Projection bindings (a target "
    "binder bound to a premise structure's field) are not tested. It does not refute "
    "any premise, a stronger or differently bound formulation, a sense "
    "identification or a bundle with further premises.")


class Corpus:
    """The statements, verified arguments and sense tags the repair reads."""

    def __init__(self, root: Path):
        self.root = root
        self.statements = load_records(root, "statements")
        self.arguments = load_records(root, "arguments")
        self.results = load_records(root, "results")
        verified = {r.get("argument_id") for r in self.results.values()}
        self.verified = [a for a in self.arguments.values() if a["id"] in verified]
        self.logic = {sid for sid, s in self.statements.items()
                      if s.get("lean_declaration") in LOGIC_DECLARATIONS}
        self.whole_tags = whole_tags(root)

    def declaration(self, sid: str) -> str:
        return self.statements.get(sid, {}).get("lean_declaration", "")

    def resolve(self, token: str) -> str:
        if token in self.statements:
            return token
        hits = [sid for sid in self.statements if sid.startswith(token)]
        if len(hits) != 1:
            raise SystemExit(f"statement {token!r}: {len(hits)} matches")
        return hits[0]

    def closure(self, premises, logic: bool) -> tuple[set, list[str]]:
        """Forward chaining over verified arguments: the statements that follow
        and the arguments that fired, in order."""
        have = set(premises) | (self.logic if logic else set())
        fired: list[str] = []
        changed = True
        while changed:
            changed = False
            for a in self.verified:
                c = a.get("conclusion_statement_id")
                if c in have or a["id"] in fired:
                    continue
                if set(a.get("premise_statement_ids", [])) <= have:
                    have.add(c)
                    fired.append(a["id"])
                    changed = True
        return have, fired

    def known(self, premises, target: str) -> dict | None:
        """Whether the target composes from verified arguments over the
        premises; `modulo_logic` when only with the logic statements added.
        `arguments` is the chain of fired arguments the target rests on."""
        for logic in (False, True):
            have, fired = self.closure(premises, logic=logic)
            if target in have:
                return {"arguments": self.chain(fired, target, set(premises)),
                        "modulo_logic": logic}
        return None

    def chain(self, fired: list[str], target: str, given: set) -> list[str]:
        by_id = {a["id"]: a for a in self.verified}
        concluding = {}
        for aid in fired:
            concluding.setdefault(by_id[aid]["conclusion_statement_id"], aid)
        out, todo, seen = [], [target], set()
        while todo:
            s = todo.pop()
            if s in seen or s in given or s not in concluding:
                continue
            seen.add(s)
            aid = concluding[s]
            out.append(aid)
            todo.extend(by_id[aid].get("premise_statement_ids", []))
        return list(reversed(out))

    def only_through(self, statement: str, target: str) -> bool:
        """True when `statement` has verified derivations and every one of them
        uses `target`, directly or through premises of the same kind: using it
        to derive the target would be a support cycle."""
        memo: dict[str, bool] = {}

        def through(s: str, stack: frozenset) -> bool:
            if s == target:
                return True
            if s in stack:
                return True
            if s in memo:
                return memo[s]
            routes = [a for a in self.verified if a.get("conclusion_statement_id") == s]
            if not routes:
                memo[s] = False
                return False
            result = all(any(through(p, stack | {s}) for p in a.get("premise_statement_ids", []))
                         for a in routes)
            memo[s] = result
            return result

        routes = [a for a in self.verified if a.get("conclusion_statement_id") == statement]
        return bool(routes) and through(statement, frozenset())

    def order_sensitive(self, declarations) -> list[str]:
        """Binders carrying both a whole-binder and a partial-application tag:
        whether `#discover` identifies them depends on which tag comes first."""
        kinds: dict[tuple[str, str], set] = {}
        for decl, binder, key in self.lean_tags(declarations):
            kinds.setdefault((decl, binder), set()).add("|" in key)
        return [f"{d}.{b}" for (d, b), k in kinds.items() if len(k) == 2]

    def lean_tags(self, declarations) -> list[list[str]]:
        """`[declaration, binder, key]` for the goal's declarations, keyed as
        `tag_key` in `truth/src/discover.rs` does (a partial application's key
        carries `|`, so it never identifies binders), and in the engine's order:
        disambiguation records by id, then senses and entries as listed. The
        order matters: `senseOf` in `scripts/Discover.lean` takes a binder's
        first tag, so a binder with a whole-binder and a partial-application
        tag is identified or not by which comes first."""
        wanted = set(declarations)
        rows = []
        if not hasattr(self, "_disambiguations"):
            self._disambiguations = sorted(
                (json.loads(path.read_text())
                 for path in (self.root / "corpus" / "disambiguations").glob("*.json")),
                key=lambda record: record.get("id", ""))
        for record in self._disambiguations:
            for sense in record.get("senses", []):
                for entry in sense.get("lean_parameters") or []:
                    if entry.get("declaration") not in wanted:
                        continue
                    args = entry.get("arguments") or []
                    key = sense["id"]
                    if any(a != "_" for a in args):
                        key = f"{key}|{' '.join(args)}"
                    row = [entry["declaration"], entry["parameter"], key]
                    if row not in rows:
                        rows.append(row)
        return rows


SOLVER_INPUTS = ("corpus", "TruthCore", "scripts/Discover.lean", "scripts/DiscoverRepair.lean",
                 "lake-manifest.json", "lean-toolchain")


def revision(root: Path) -> str:
    """The source revision of the solver inputs: the Git objects of the corpus,
    the library, the two Lean scripts and the Lean dependency pins (not of this
    tool), so that a change of the repair tool alone does not make an old solver
    input look new; uncommitted changes to them (the diff and untracked files,
    by content) enter the hash; and the commit it was read at. The prove-sweep
    probe enters each solver key separately (`solver_key`)."""
    import hashlib
    head = git(root, "rev-parse", "HEAD", check=False).strip() or "unknown"
    digest = hashlib.sha256()
    digest.update(git(root, "rev-parse", *[f"HEAD:{p}" for p in SOLVER_INPUTS],
                      check=False).encode())
    dirty = git(root, "status", "--porcelain", "--", *SOLVER_INPUTS, check=False).strip()
    if dirty:
        digest.update(git(root, "diff", "HEAD", "--binary", "--", *SOLVER_INPUTS,
                          check=False).encode())
        others = git(root, "ls-files", "-z", "--others", "--exclude-standard", "--",
                     *SOLVER_INPUTS, check=False)
        for name in sorted(filter(None, others.split("\0"))):
            digest.update(name.encode())
            path = root / name
            if path.is_file():
                digest.update(path.read_bytes())
    inputs = digest.hexdigest()[:12]
    return f"inputs {inputs}{'+dirty' if dirty else ''} at {head[:12]}"


def input_revision(rev: str) -> str:
    """The part of a revision string that identifies solver inputs."""
    return rev.split(" at ")[0]


def solver_key(goal: dict, corpus: Corpus) -> str:
    """Identity of one solver input: command, revision, declarations, budget,
    domain policy and the tags the goal's declarations carry."""
    import hashlib
    decls = [corpus.declaration(goal["target"])] + [corpus.declaration(p) for p in goal["premises"]]
    payload = {"command": goal["command"], "revision": input_revision(goal.get("revision", "")),
               "target": decls[0], "premises": sorted(decls[1:]),
               "heartbeats": goal["heartbeats"], "strict": goal.get("strict_domains", False),
               "tags": corpus.lean_tags(decls), "probe": prelude_digest()}
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()[:16]


class Trace:
    """The bounded attempt trace: one JSON file, one entry per solver input."""

    def __init__(self, path: Path | None):
        self.path = path
        self.entries: list[dict] = []
        if path and path.exists():
            self.entries = json.loads(path.read_text()).get("entries", [])

    def keys(self) -> dict[str, int]:
        return {e["key"]: i for i, e in enumerate(self.entries) if e.get("key")}

    def for_goal(self, label: str) -> list[dict]:
        return [e for e in self.entries if e.get("goal_label") == label]

    def add(self, entry: dict) -> None:
        """Bounded per goal by the plan-time guards (`plan`); a duplicate key
        here is a planner bug."""
        if entry.get("key") and entry["key"] in self.keys():
            raise ValueError(f"duplicate solver input {entry['key']}")
        self.entries.append(entry)

    def failures(self, key: str) -> int:
        return sum(1 for e in self.entries if e.get("failed_key") == key)

    def save(self) -> None:
        if self.path:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.write_text(json.dumps({"entries": self.entries}, indent=2) + "\n")


def goal_label(finding: dict) -> str:
    return f"{finding['target']['statement_id'][:8]}:{finding.get('label', '')}"


def original_goal(finding: dict, options: dict, rev: str) -> dict:
    return {"command": "discover", "target": finding["target"]["statement_id"],
            "premises": list(finding.get("candidates", [])),
            "heartbeats": options.get("heartbeats", 100000), "strict_domains": False,
            "revision": rev}


def seed_trace(trace: Trace, finding: dict, options: dict, rev: str, corpus: Corpus,
               report_path: str) -> None:
    """Register the engine's own goal, so an identical retry is refused."""
    goal = original_goal(finding, options, rev)
    key = solver_key(goal, corpus)
    if key in trace.keys():
        return
    trace.add({"key": key, "goal_label": goal_label(finding), "action": "engine",
               "goal": goal, "why": f"the engine's goal in {report_path}",
               "outcome": {"status": finding["kind"]}})


def signals(finding: dict, options: dict) -> dict:
    lean = finding.get("lean") or {}
    filters = [f.get("filter") for f in finding.get("filters", [])]
    error = lean.get("error") or ""
    return {
        "lean": lean, "filters": filters, "error": error,
        "timed_out": "timed out" in error,
        "closed": bool(lean.get("closed")) or bool(lean.get("alone")),
        "vacuous": lean.get("vacuous"), "literal": lean.get("literal_negation"),
        "by_name": lean.get("domain_identified_by_name") or [],
        "bridges": lean.get("bridges") or [],
        "truncated": len(finding.get("candidates", [])) >= options.get("candidates", 8),
    }


def bridge_same_name(bridge: dict) -> bool:
    """A bridge between two relations of one name declared in different
    declarations: often an identification question, not new philosophy."""
    a, b = bridge.get("from", ""), bridge.get("to", "")
    return a.rsplit(".", 1)[-1].split("_")[0] == b.rsplit(".", 1)[-1].split("_")[0] and \
        a.rsplit(".", 1)[0] != b.rsplit(".", 1)[0]


def reusable_lemmas(corpus: Corpus, bundle: list[str], target: str,
                    rows: list[dict]) -> list[dict]:
    """Verified arguments whose premises the bundle (with logic) already
    contains and whose conclusion is not in it: their conclusions are checked
    lemmas the search could not reach by itself (Duper does not compose
    through other theorems). Ranked: conclusions that a known derivation of the
    target uses first."""
    have = set(bundle) | corpus.logic
    wanted = {p for r in rows for p in r["premises"]}
    target_defs = set(corpus.statements.get(target, {}).get("definition_ids", []))
    out = []
    for a in corpus.verified:
        c = a.get("conclusion_statement_id")
        premises = set(a.get("premise_statement_ids", []))
        if c in have or c == target or not corpus.declaration(c):
            continue
        # A lemma must use the bundle (not only logic) and bear on the target:
        # a premise of a known derivation, or a shared definition.
        if not premises <= have or not (premises & set(bundle)):
            continue
        shared = target_defs & set(corpus.statements.get(c, {}).get("definition_ids", []))
        if c in wanted or shared:
            out.append({"lemma": c, "argument": a["id"], "known_premise": c in wanted})
    out.sort(key=lambda x: (not x["known_premise"], x["lemma"]))
    return out


def fresh_binders(binders: list[dict]) -> list[str]:
    """Outer binders renamed (`X_2`, `X_3` …): a premise binder of the same
    name as an earlier one that nothing identified with it (`freshUserName`
    in `scripts/Discover.lean`), with the tag it carries, if any. Only
    same-named binders are detected: a premise binder of another name that
    should denote the target's (`B` for `Being`) also stays separate, unseen
    here; the binder export (`--binders`) reports those."""
    out = []
    for b in binders:
        if b.get("name") and b["name"] != b.get("from", "").rsplit(".", 1)[-1]:
            tag = b.get("sense") or "untagged"
            kind = "partial-application tag" if "|" in tag else (
                "whole-binder tag" if tag != "untagged" else "untagged")
            out.append(f"{b.get('from')} ({kind})")
    return out


def classify(finding: dict, corpus: Corpus, options: dict, rows: list[dict],
             attempts: list[dict], binders_checked: bool = True) -> list[dict]:
    """The six alternative diagnoses with their status and evidence.
    `binders_checked` is false when no binder export was supplied: the known
    derivations' identification gaps are then unknown, not absent."""
    s = signals(finding, options)
    ev = {k: [] for k in DIAGNOSES}
    status = {k: "not indicated" for k in DIAGNOSES}

    def mark(code, level, text):
        order = ["not indicated", "possible", "supported"]
        if status[code] != "excluded" and order.index(level) > order.index(status[code]):
            status[code] = level
        ev[code].append(text)

    if s["error"]:
        if s["timed_out"]:
            mark("a", "supported", f"the Lean process hit its time limit: {s['error'][:160]}")
        else:
            mark("b", "supported", f"Lean could not state the goal: {s['error'][:160]}")
    if s["literal"]:
        mark("d", "supported", f"the inconsistent core {s['literal']} is a premise and its literal "
                               "negation (P/¬P): true by construction, not support")
    elif s["vacuous"]:
        mark("d", "supported", f"the premises prove False (core {s['lean'].get('vacuous_core')}): "
                               "an incompatibility, never support")
    if s["lean"].get("antecedent_refuted"):
        mark("d", "supported", "the premises refute the target's antecedents (vacuous target)")
    if "witness" in s["filters"]:
        mark("d", "possible", "no one-point joint model found; consistency unresolved")
    if s["by_name"] or "domain_by_name" in s["filters"]:
        mark("c", "supported", "carriers identified across modules by name only: "
                               + "; ".join(s["by_name"][:4]))
    if "senses" in s["filters"]:
        mark("c", "supported", "the bundle mixes senses of one term without a registered bridge")
    for r in rows:
        if r["unidentified"]:
            mark("c", "supported", f"known argument {r['argument'][:8]} needs identifications "
                                   f"no tag records: {', '.join(r['unidentified'][:6])}")
    decls = [corpus.declaration(finding["target"]["statement_id"])] + [
        corpus.declaration(p) for p in finding.get("candidates", [])]
    for binder in corpus.order_sensitive(decls):
        mark("c", "possible", f"{binder} has a whole-binder and a partial-application tag; "
                              "its identification depends on tag order")
    unresolved = not s["closed"] and not s["error"]
    if unresolved:
        mark("a", "possible", "Duper returned no proof; the engine does not record whether the "
                              "heartbeat budget expired or the search saturated")
        if s["truncated"]:
            mark("a", "possible", f"the candidate list is at its cap ({options.get('candidates', 8)}): "
                                  "selection may have cut a needed premise")
        for r in rows:
            if r["not_retrieved"]:
                mark("b", "supported", f"known argument {r['argument'][:8]}: premises not in the goal "
                                       f"{', '.join(p[:8] for p in r['not_retrieved'])}")
            elif not r["unidentified"] and binders_checked:
                mark("a", "supported", f"known argument {r['argument'][:8]} was retrieved and is "
                                       "identifiable but was not composed (search gap)")
            elif not r["unidentified"]:
                mark("a", "possible", f"known argument {r['argument'][:8]} was retrieved but not "
                                      "composed; identification not checked (no binder export)")
        lemmas = reusable_lemmas(corpus, finding.get("candidates", []),
                                 finding["target"]["statement_id"], rows)
        if lemmas:
            mark("b", "possible", f"{len(lemmas)} verified lemma(s) follow from the bundle but are "
                                  "not in it: " + ", ".join(l["lemma"][:8] for l in lemmas[:4]))
        for br in {b.get("text", ""): b for b in s["bridges"]}.values():
            if bridge_same_name(br):
                mark("c", "possible", f"missing bridge between same-named relations: {br.get('text', '')[:120]}")
            else:
                mark("e", "possible", f"candidate bridge (OPEN): {br.get('text', '')[:120]}")
    for at in attempts:
        out = at.get("outcome", {})
        tag = f"trace {(at.get('key') or at.get('report_key') or '')[:8]} ({at['action']})"
        if out.get("status") == "countermodel":
            untested = out.get("projections_untested") or []
            if untested:
                mark("a", "possible", f"{tag}: one-point countermodel under the plain binding only; "
                                      f"{len(untested)} projection binding(s) not tested, so a "
                                      "budget failure on those stays possible")
            else:
                status["a"] = "excluded"
                ev["a"].append(f"{tag}: one-point countermodel under this plain binding (no "
                               "projection binding applies): no budget proves this bundle so bound")
            # A countermodel shows that the bundle lacks *something* (a premise,
            # lemma, identification or bridge); it never shows that the gap is
            # a substantive premise, so (e) stays possible at most.
            mark("e", "possible", f"{tag}: the bundle as bound lacks a premise, lemma, "
                                  "identification or bridge; which one is not decided")
        if out.get("premises_model"):
            ev["d"].append(f"{tag}: one-point model of the premises ({out['premises_model']}): "
                           "not an inconsistent core; vacuity of the target is not tested")
        if out.get("status") == "closed-candidate" and at["action"] in ("reuse-lemma", "split"):
            mark("b", "supported", f"{tag}: closes once the lemma is in the goal")
        if out.get("status") == "closed-known" and at["action"] == "known-bundle":
            mark("b", "supported", f"{tag}: the known argument's premises close it (retrieval gap)")
        if out.get("status") == "unresolved" and at.get("goal", {}).get("command") == "discover":
            split = fresh_binders(at.get("binders", []))
            if split:
                mark("c", "supported", f"{tag}: same-named binders left separate (no shared "
                                       "whole-binder tag or same-module name with a definitionally "
                                       f"equal type joined them): {', '.join(split[:4])}")
            elif at["action"] == "known-bundle" and at.get("binders"):
                mark("a", "supported", f"{tag}: the premises of a verified argument, with no "
                                       "same-named binder left separate, did not close: a "
                                       "proof-search gap unless an identification by tag or type "
                                       "is missing (the verified proof may use reasoning Duper does "
                                       "not search, such as induction or a well-founded recursion)")
        if out.get("status") == "unresolved" and at["action"] == "strict-domains":
            mark("c", "supported", f"{tag}: without the by-name carrier fallback the goal does not close")
        if out.get("status") == "unresolved" and at["action"] == "budget":
            mark("a", "possible", f"{tag}: still unresolved at {at['goal']['heartbeats']} heartbeats; "
                                  "not a refutation")
    if not any(v == "supported" for v in status.values()):
        mark("f", "possible", "no signal supports any diagnosis yet")
    return [{"code": k, "diagnosis": DIAGNOSES[k], "status": status[k], "evidence": ev[k]}
            for k in DIAGNOSES]


def plan(finding: dict, corpus: Corpus, options: dict, rows: list[dict], trace: Trace,
         rev: str) -> list[dict]:
    """The retry actions, in priority order, with their guards checked."""
    s = signals(finding, options)
    target = finding["target"]["statement_id"]
    candidates = list(finding.get("candidates", []))
    minimal = [p["statement_id"] for p in finding.get("premises", [])]
    hb = options.get("heartbeats", 100000)
    label = goal_label(finding)
    done = trace.for_goal(label)
    keys = trace.keys()
    actions: list[dict] = []

    def goal(premises, command="discover", heartbeats=hb, strict=False):
        return {"command": command, "target": target, "premises": list(dict.fromkeys(premises)),
                "heartbeats": heartbeats, "strict_domains": strict, "revision": rev}

    def add(action, code, why, goals=(), added=(), report=None):
        refused = []
        for g in goals:
            for p in g["premises"]:
                if p not in corpus.statements or not corpus.declaration(p):
                    refused.append(f"{p[:8]} is not a corpus statement with a Lean declaration")
            if g["target"] in g["premises"]:
                refused.append("the target is among its own premises")
            k = solver_key(g, corpus)
            g["key"] = k
            if k in keys:
                refused.append(f"duplicate solver input (trace {k[:8]})")
            if trace.failures(k) >= MAX_FAILURES_PER_INPUT:
                refused.append(f"input {k[:8]} failed {trace.failures(k)} times for infrastructure "
                               "reasons; investigate before rerunning")
        for p in added:
            if corpus.only_through(p, target):
                refused.append(f"support cycle: every verified derivation of {p[:8]} uses the target")
        solver_runs = sum(1 for e in done if e.get("action") != "engine"
                          and (e.get("key") or e.get("failed_key")))
        if goals and solver_runs + len(goals) > MAX_ATTEMPTS_PER_GOAL:
            refused.append(f"attempt cap: {solver_runs} solver runs + {len(goals)} would exceed "
                           f"{MAX_ATTEMPTS_PER_GOAL} for this goal")
        if report and any(e.get("report_key") == report.get("key") for e in done):
            refused.append("already reported")
        settled = [e for e in done if e.get("action") == action
                   and e.get("outcome", {}).get("status") in SETTLING.get(action, ())]
        if goals and settled:
            refused.append(f"diagnosis already settled by trace {settled[0]['key'][:8]} "
                           f"({settled[0]['outcome']['status']})")
        # The id comes from the action's content, so that inserting an action
        # (a budget retry after a countermodel run) never shifts another's id.
        import hashlib
        content = json.dumps([action, [g["key"] for g in goals], (report or {}).get("key")])
        ident = hashlib.sha256(content.encode()).hexdigest()[:6]
        actions.append({"id": f"{target[:8]}-{action}-{ident}", "action": action,
                        "diagnosis": code, "why": why, "goals": list(goals),
                        "added": list(added), "report": report, "refused": refused})

    if s["error"] and not s["timed_out"]:
        add("blocker", "b", "the goal could not be stated; fix the declaration or its binding "
                            "first (no solver input would differ)",
            report={"key": f"error:{target}", "text": s["error"][:300]})
    if s["literal"]:
        add("reject", "d", "a literal P/¬P core: inconsistent by construction, never support; "
                           "no retry can turn it into a relationship",
            report={"key": f"literal:{target}", "text": f"core {s['literal']}"})
    elif s["vacuous"]:
        add("record-incompatibility", "d", "an inconsistent core is an incompatibility, not "
                                           "support; record it as such, do not retry for support",
            report={"key": f"vacuous:{target}", "text": f"core {s['lean'].get('vacuous_core')}"})
    if s["closed"] and (s["by_name"] or "domain_by_name" in s["filters"]):
        bundle = minimal or candidates
        add("strict-domains", "c", "the proof rests on a by-name carrier identification; retry the "
                                   "same bundle without that fallback to see whether it is load-bearing "
                                   "(the repair never merges carriers or writes tags)",
            goals=[goal(bundle, strict=True)])
    unresolved = not s["closed"] and not s["literal"] and not s["vacuous"] and \
        (not s["error"] or s["timed_out"])
    if unresolved:
        for lem in reusable_lemmas(corpus, candidates, target, rows)[:3]:
            add("reuse-lemma", "b", f"verified argument {lem['argument'][:8]} derives "
                                    f"{lem['lemma'][:8]} from premises already in the goal; Duper "
                                    "does not compose through theorems, so add the checked lemma",
                goals=[goal(candidates + [lem["lemma"]])], added=[lem["lemma"]])
        # The most composable known derivation first: no identification gap,
        # then the fewest premises retrieval missed.
        for r in sorted(rows, key=lambda r: (bool(r["unidentified"]), len(r["not_retrieved"]))):
            if r["not_retrieved"]:
                add("known-bundle", "b", f"retrieval missed premises of verified argument "
                                         f"{r['argument'][:8]}; the exact bundle tests whether the "
                                         "failure was retrieval (expected: filtered as known)",
                    goals=[goal(r["premises"])], added=r["not_retrieved"])
        add("countermodel", "a", "an exact one-point countermodel of premises and ¬target would "
                                 "exclude a budget or tactic failure for this bundle",
            goals=[goal(candidates, command="countermodel")])
        for r in rows:
            missing = [p for p in r["not_retrieved"] if p not in corpus.logic]
            if len(missing) == 1:
                m = missing[0]
                add("split", "b", f"one premise {m[:8]} of verified argument {r['argument'][:8]} is "
                                  "missing: search it from the goal's bundle, and the target from "
                                  "the bundle with it, as two goals",
                    goals=[dict(goal(candidates), target=m),
                           goal(candidates + [m])], added=[m])
        cm = [e for e in done if e.get("action") == "countermodel"]
        if any(e["outcome"].get("status") == "no-countermodel" for e in cm) and \
                all(e["outcome"].get("status") != "countermodel" for e in cm):
            add("budget", "a", f"no countermodel was found, so a budget failure stays possible; "
                               f"retry once at {BUDGET_FACTOR}x heartbeats",
                goals=[goal(candidates, heartbeats=hb * BUDGET_FACTOR)])
        for br in {b.get("text", ""): b for b in s["bridges"]}.values():
            add("open-bridge", "e" if not bridge_same_name(br) else "c",
                "the engine's missing bridge is a candidate proposition: OPEN for warrant "
                "research (or a sense-tag review when both relations share a name), never "
                "added to a goal",
                report={"key": f"bridge:{target}:{br.get('text', '')}", "status": "OPEN",
                        "text": br.get("text", ""), "from": br.get("from"), "to": br.get("to"),
                        "with_premises": br.get("used", [])})
    for r in rows:
        if r["unidentified"]:
            add("blocker", "c", f"known argument {r['argument'][:8]} needs binder identifications "
                                "that only a reviewed sense tag or an explicit bridge premise can "
                                "supply; the repair does not identify them",
                report={"key": f"ident:{r['argument']}", "text": ", ".join(r["unidentified"])})
    return actions


# --- Lean runs -------------------------------------------------------------

def prelude() -> str:
    """The transcription probe tactics of `truth prove-sweep` (`PRELUDE` in
    `truth/src/prove_sweep.rs`), which `scripts/Discover.lean` uses."""
    import re
    text = (TOOL_ROOT / "truth" / "src" / "prove_sweep.rs").read_text()
    found = re.search(r'pub const PRELUDE: &str = r#"(.*?)"#;', text, re.S)
    if not found:
        raise SystemExit("cannot read PRELUDE from truth/src/prove_sweep.rs")
    return found.group(1)


def prelude_digest() -> str:
    import hashlib
    return hashlib.sha256(prelude().encode()).hexdigest()[:12]


def lean_root(corpus: Corpus) -> Path:
    """Where Lean runs and the Discover scripts are read: the `--root`
    repository when it is a Lake project with those scripts (so the solver
    inputs match the revision and tags read from it), else this tool's own
    repository (synthetic test corpora)."""
    root = corpus.root.resolve()
    if (root / "lakefile.toml").is_file() and (root / "scripts" / "Discover.lean").is_file():
        return root
    return TOOL_ROOT


def module_of(root: Path, declaration: str, modules: dict | None = None) -> str:
    if modules and declaration in modules:
        return modules[declaration]
    parts = declaration.split(".")
    for n in range(len(parts) - 1, 0, -1):
        if (root / Path(*parts[:n])).with_suffix(".lean").is_file():
            return ".".join(parts[:n])
    raise SystemExit(f"no module found for {declaration}")


def lean_string(text: str) -> str:
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def command_line(label: str, goal: dict, corpus: Corpus) -> str:
    target = corpus.declaration(goal["target"])
    premises = [corpus.declaration(p) for p in goal["premises"]]
    config = json.dumps({"tags": corpus.lean_tags([target, *premises]), "bridges": False,
                         "strict_domains": goal.get("strict_domains", False)})
    if goal["command"] == "countermodel":
        return (f"#discover_countermodel {lean_string(label)} {goal['heartbeats']} "
                f"{lean_string(config)} {target} from {' '.join(premises)}")
    return (f"#discover {lean_string(label)} {goal['heartbeats']} \"\" {lean_string(config)} "
            f"{target} from {' '.join(premises)}")


def scratch_text(modules: list[str], commands: list[str], probe_stub: bool = False,
                 root: Path = TOOL_ROOT) -> str:
    discover = (root / "scripts" / "Discover.lean").read_text()
    repair = (root / "scripts" / "DiscoverRepair.lean").read_text()
    imports, bodies = set(), []
    for text in (discover, repair):
        lines = []
        for line in text.splitlines():
            if line.startswith("import "):
                imports.add(line[len("import "):].strip())
            else:
                lines.append(line)
        bodies.append("\n".join(lines))
    imports |= set(modules)
    probe = ('macro "prove_sweep_probe" : tactic => `(tactic| fail "stub")\n'
             if probe_stub else prelude())
    return ("".join(f"import {m}\n" for m in sorted(imports)) + "\n" + probe + "\n"
            + bodies[0] + "\n" + bodies[1] + "\nset_option maxHeartbeats 0\n\n"
            + "\n".join(commands) + "\n")


def run_lean(corpus: Corpus, labelled: list[tuple[str, dict]], *, lock: str | None,
             launcher: list[str] | None = None, modules: dict | None = None,
             extra_lean_path: str | None = None, probe_stub: bool = False,
             timeout: int | None = None) -> dict[str, dict]:
    """Runs the goals in one Lean process, in `lean_root(corpus)`; the raw
    outcomes by label. An outcome the process did not produce (no output, Lean
    timed out or was killed) is marked `infrastructure`: it is not a solver
    result, and its input is not keyed in the trace."""
    where = lean_root(corpus)
    decls = {corpus.declaration(g["target"]) for _, g in labelled}
    decls |= {corpus.declaration(p) for _, g in labelled for p in g["premises"]}
    mods = sorted({module_of(corpus.root, d, modules) for d in decls})
    commands = [command_line(label, g, corpus) for label, g in labelled]
    if launcher is None:
        launcher = [sys.executable, str(where / "scripts" / "worker_env.py"), "--", "lake"]
    if timeout is None:
        timeout = 300 + sum(60 + g["heartbeats"] // 1000 * 3 for _, g in labelled)
    with tempfile.TemporaryDirectory(prefix="discover-repair-") as tmp:
        path = Path(tmp) / "Repair.lean"
        log = Path(tmp) / "repair.log"
        path.write_text(scratch_text(mods, commands, probe_stub, root=where))
        if extra_lean_path:
            argv = [*launcher, "env", "sh", "-c", 'LEAN_PATH="$1:$LEAN_PATH" lean "$2"', "sh",
                    extra_lean_path, str(path)]
        else:
            argv = [*launcher, "env", "lean", str(path)]
        # The time limit bounds Lean, not the wait for the heavy-job lock.
        argv = ["timeout", "--kill-after=30", str(timeout), *argv]
        if lock:
            Path(lock).parent.mkdir(parents=True, exist_ok=True)
            argv = ["flock", lock, *argv]
        env = {**os.environ, "TRUTH_DISCOVER_LOG": str(log)}
        done = subprocess.run(argv, cwd=where, env=env, capture_output=True, text=True)
        output = done.stdout + done.stderr
        failure = {124: f"Lean timed out after {timeout}s",
                   137: "Lean was killed (exit 137: out of memory, or the kill after a timeout)",
                   }.get(done.returncode)
        logged = log.read_text() if log.exists() else ""
    outcomes: dict[str, dict] = {}
    for line in (logged + "\n" + output).splitlines():
        for marker in ("DISCOVER-REPAIR-JSON ", "DISCOVER-JSON "):
            at = line.find(marker)
            if at >= 0:
                try:
                    value = json.loads(line[at + len(marker):])
                except ValueError:
                    continue
                outcomes.setdefault(value.get("label", ""), value)
                break
    errors = [l for l in output.splitlines() if ": error" in l][:3]
    for label, _ in labelled:
        outcomes.setdefault(label, {"label": label, "infrastructure": True,
                                    "error": failure or "\n".join(errors) or "no output"})
    return outcomes


def semantics_preflight(corpus: Corpus, premises: list[str], target: str) -> dict:
    truth = corpus.root / "target" / "release" / "truth"
    if not truth.exists():
        return {"checked": False, "note": "truth CLI not built; senses not checked"}
    argv = [str(truth), "--root", str(corpus.root), "--json", "semantics"]
    for p in premises:
        argv += ["--premise", p]
    argv += ["--conclusion", target]
    done = subprocess.run(argv, capture_output=True, text=True)
    try:
        check = json.loads(done.stdout)["check"]
    except (ValueError, KeyError):
        return {"checked": False, "note": (done.stderr or done.stdout)[:200]}
    return {"checked": True, "passes": check.get("passes"), "message": check.get("message", "")}


def assess(raw: dict, goal: dict, corpus: Corpus, senses: bool = True) -> dict:
    """The outcome of one solver run, with the engine's filters applied
    offline where the raw outcome allows."""
    if raw.get("error"):
        if raw.get("infrastructure"):
            # Not a solver result: the process produced no outcome.
            return {"status": "failed", "infrastructure": True, "notes": [
                raw["error"][:300], "not a solver result; unresolved, not refuted"]}
        if "timed out" in raw["error"]:
            return {"status": "unresolved", "notes": [raw["error"][:300], "not refuted"]}
        return {"status": "error", "notes": [raw["error"][:300]]}
    if goal["command"] == "countermodel":
        binders = raw.get("binders", [])
        out = {"premises_model": raw.get("premises_model"),
               "by_name": raw.get("domain_identified_by_name", []),
               "projections_untested": raw.get("projections_untested", [])}
        if raw.get("countermodel"):
            out.update(status="countermodel", model={
                "statement": "∀ binders, premises → target fails at (plain binding)",
                "binders": binders, "interpretation": raw["countermodel"],
                "slots": raw.get("slots", []),
                "bounds": COUNTERMODEL_BOUNDS,
                "projections_untested": raw.get("projections_untested", []),
                "conditional_on_identifications": raw.get("domain_identified_by_name", [])})
        else:
            out.update(status="no-countermodel",
                       notes=["no one-point countermodel; the implication may hold or need a larger model"])
        return out
    if raw.get("alone"):
        return {"status": "vocabulary-theorem", "notes": ["the target follows from no premise"]}
    closed = raw.get("closed")
    if not closed:
        return {"status": "unresolved",
                "notes": ["no proof within the budget; unresolved, not refuted"]}
    premises = goal["premises"]
    minimal = [premises[i] for i in raw.get("minimal", []) if i < len(premises)]
    if raw.get("literal_negation"):
        return {"status": "rejected-literal-negation", "minimal": minimal,
                "notes": ["P/¬P core: not support, not an incompatibility"]}
    if raw.get("vacuous"):
        core = [premises[i] for i in raw.get("vacuous_core") or [] if i < len(premises)]
        return {"status": "incompatibility", "core": core,
                "notes": ["the premises prove False: an incompatibility, never support"]}
    out: dict = {"minimal": minimal, "prover": closed.get("prover"),
                 "axioms": closed.get("axioms", []), "notes": []}
    necessity = []
    omissions = {o.get("premise"): o.get("model") for o in raw.get("omissions") or []}
    for d in raw.get("deletions") or []:
        i = d.get("premise")
        sid = premises[i] if i is not None and i < len(premises) else str(i)
        if d.get("outcome") == "dropped":
            necessity.append({"premise": sid, "status": "dropped"})
        elif omissions.get(i):
            necessity.append({"premise": sid, "status": "needed (one-point omission model)",
                              "model": omissions[i]})
        else:
            necessity.append({"premise": sid, "status": "kept within budget; necessity unresolved"})
    out["necessity"] = necessity
    if raw.get("domain_identified_by_name"):
        out["status"] = "rejected-domain-by-name"
        out["by_name"] = raw["domain_identified_by_name"]
        return out
    # The engine's projection filters (docs/discover.md, step 4).
    projection = raw.get("projection") or None
    if raw.get("projection_unused"):
        out["status"] = "rejected-projection-unused"
        out["projection"] = projection
        return out
    if isinstance(projection, dict):
        out["projection"] = projection
        if projection.get("ambiguous"):
            out["status"] = "rejected-projection-ambiguous"
            return out
        out["notes"].append(f"closed only with {projection.get('binder')} bound to "
                            f"{projection.get('bound_to')}: a specialization of the target")
    if raw.get("probe"):
        out["status"] = "rejected-transcription"
        return out
    if raw.get("antecedent_refuted"):
        out["notes"].append("vacuous target: the premises refute the target's antecedents")
    if raw.get("witness") is None:
        out["notes"].append("no one-point joint model; consistency unresolved")
    out["senses"] = semantics_preflight(corpus, minimal, goal["target"]) if senses else {
        "checked": False}
    if out["senses"].get("checked") and not out["senses"].get("passes"):
        out["notes"].append("senses: " + out["senses"].get("message", "")[:200])
    known = corpus.known(minimal, goal["target"])
    if known:
        out["status"] = "closed-known"
        out["known"] = known
        return out
    out["status"] = "closed-candidate"
    out["notes"].append("raw candidate: certify with `truth discover` and record only through "
                        "the spec path and semantic review")
    return out


def change_against(goal: dict, original: dict, corpus: Corpus) -> dict:
    return {"target": corpus.declaration(goal["target"]) if goal["target"] != original["target"]
            else "unchanged",
            "added": [p for p in goal["premises"] if p not in original["premises"]],
            "removed": [p for p in original["premises"] if p not in goal["premises"]],
            "heartbeats": goal["heartbeats"], "strict_domains": goal.get("strict_domains", False),
            "command": goal["command"]}


def load_context(args):
    root = Path(args.root)
    corpus = Corpus(root)
    report_path = Path(args.report)
    report = json.loads(report_path.read_text())
    binders = load_binders(Path(args.binders)) if args.binders else {}
    wanted = set(args.target or [])
    findings = [f for f in report["findings"]
                if f["kind"] != "discovery" and
                (not wanted or any(f["target"]["statement_id"].startswith(w) for w in wanted))]
    trace_path = Path(args.trace) if args.trace else report_path.with_name("repair-trace.json")
    trace = Trace(trace_path)
    rev = args.revision or revision(root)
    return corpus, report, binders, findings, trace, rev


def plan_all(corpus, report, binders, findings, trace, rev, report_path):
    options = report.get("options", {})
    out = []
    for finding in findings:
        seed_trace(trace, finding, options, rev, corpus, report_path)
        rows = known_rows(finding, corpus.statements, corpus.arguments, corpus.results,
                          binders, corpus.whole_tags)
        attempts = trace.for_goal(goal_label(finding))
        out.append({"goal": goal_label(finding), "target": finding["target"]["statement_id"],
                    "declaration": finding["target"].get("lean_declaration", ""),
                    "kind": finding["kind"],
                    "filters": [f.get("filter") for f in finding.get("filters", [])],
                    "diagnoses": classify(finding, corpus, options, rows, attempts,
                                          binders_checked=bool(binders)),
                    "actions": plan(finding, corpus, options, rows, trace, rev),
                    "finding": finding})
    return out


def print_plan(items: list[dict]) -> None:
    for item in items:
        print(f"{item['goal']} {item['declaration'].split('.')[-1]}: {item['kind']}"
              f"{' ' + ','.join(item['filters']) if item['filters'] else ''}")
        for d in item["diagnoses"]:
            if d["status"] != "not indicated":
                print(f"  ({d['code']}) {d['diagnosis']}: {d['status']}")
                for e in d["evidence"][:3]:
                    print(f"      - {e}")
        for a in item["actions"]:
            state = "REFUSED: " + "; ".join(a["refused"]) if a["refused"] else "admissible"
            print(f"  [{a['id']}] {a['action']} ({a['diagnosis']}) {state}")
            print(f"      why: {a['why']}")


def repair(args: argparse.Namespace) -> int:
    corpus, report, binders, findings, trace, rev = load_context(args)
    # Planning only: the engine goals are seeded in memory, the trace file is
    # left as it was.
    items = plan_all(corpus, report, binders, findings, trace, rev, args.report)
    if args.json:
        for item in items:
            item.pop("finding")
        print(json.dumps(items, indent=2, ensure_ascii=False))
    else:
        print_plan(items)
    return 0


def execute(action: dict, item: dict, corpus: Corpus, trace: Trace, rev: str,
            runner, senses: bool = True) -> list[dict]:
    """Runs an admissible action and appends its trace entries."""
    if action["refused"]:
        raise SystemExit(f"action {action['id']} refused: {'; '.join(action['refused'])}")
    finding = item["finding"]
    label = item["goal"]
    original = next((e["goal"] for e in trace.for_goal(label) if e["action"] == "engine"), None)
    diagnoses = {d["code"]: d["status"] for d in item["diagnoses"]}
    entries = []
    if not action["goals"]:
        entry = {"key": None, "report_key": action["report"]["key"], "goal_label": label,
                 "revision": rev, "action": action["action"], "diagnosis": action["diagnosis"],
                 "diagnoses": diagnoses, "why": action["why"], "report": action["report"],
                 "outcome": {"status": action["report"].get("status", "reported")}}
        trace.add(entry)
        return [entry]
    labelled = [(f"{action['id']}.{i}", g) for i, g in enumerate(action["goals"])]
    raws = runner(corpus, labelled)
    for (lab, g), _ in zip(labelled, action["goals"]):
        raw = raws.get(lab, {"error": "no output"})
        outcome = assess(raw, g, corpus, senses=senses)
        failed = outcome.get("infrastructure")
        entry = {"key": None if failed else g["key"], "goal_label": label, "revision": rev,
                 "action": action["action"], "diagnosis": action["diagnosis"],
                 "diagnoses": diagnoses, "why": action["why"],
                 "goal": {k: v for k, v in g.items() if k != "key"},
                 "declarations": [corpus.declaration(g["target"])]
                 + [corpus.declaration(p) for p in g["premises"]],
                 "modified": change_against(g, original or g, corpus),
                 "outcome": outcome, "ms": raw.get("ms"),
                 "binders": raw.get("binders", [])}
        if failed:
            entry["failed_key"] = g["key"]
        trace.add(entry)
        entries.append(entry)
    return entries


def retry(args: argparse.Namespace) -> int:
    corpus, report, binders, findings, trace, rev = load_context(args)
    lock = None if args.no_lock else os.environ.get("TRUTH_DISCOVER_LOCK",
                                                    "/tmp/moenarch/truth-core-heavy.lock")

    def runner(c, labelled):
        return run_lean(c, labelled, lock=lock)

    budget = args.auto if args.auto else 1
    ran = []
    while budget > 0:
        items = plan_all(corpus, report, binders, findings, trace, rev, args.report)
        chosen = None
        for item in items:
            for a in item["actions"]:
                if args.action and a["id"] != args.action:
                    continue
                if args.action or (not a["refused"] and
                                   (a["goals"] or args.include_reports)):
                    chosen = (a, item)
                    break
            if chosen:
                break
        if not chosen:
            break
        entries = execute(chosen[0], chosen[1], corpus, trace, rev, runner)
        trace.save()
        ran.extend(entries)
        for e in entries:
            print(f"{e['goal_label']} {e['action']}: {e['outcome']['status']}")
        if args.action:
            break
        budget -= 1
    trace.save()
    if not ran:
        print("no admissible action")
    return 0


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
    for name in ("repair", "retry"):
        r = sub.add_parser(name)
        r.add_argument("report")
        r.add_argument("--binders", help="JSON lines from scripts/DiscoverBinders.lean")
        r.add_argument("--target", action="append", help="statement id prefix (repeatable)")
        r.add_argument("--trace", help="attempt trace (default: repair-trace.json beside the report)")
        r.add_argument("--revision", help="source revision to record (default: git HEAD)")
        if name == "repair":
            r.add_argument("--json", action="store_true")
        else:
            r.add_argument("--action", help="the planned action id to run")
            r.add_argument("--auto", type=int, default=0,
                           help="run up to N admissible actions, replanning after each")
            r.add_argument("--include-reports", action="store_true",
                           help="also record report-only actions (OPEN bridges, blockers)")
            r.add_argument("--no-lock", action="store_true",
                           help="do not take the heavy-job lock (tests only)")
    args = parser.parse_args()
    if args.command == "repair":
        return repair(args)
    if args.command == "retry":
        return retry(args)
    if args.command == "oracle":
        if args.rest and args.rest[0] == "--":
            args.rest = args.rest[1:]
        return oracle(args)
    return diagnose(args)


if __name__ == "__main__":
    sys.exit(main())
