#!/usr/bin/env python3
"""Target-free cross-family conjecture pilot (#1834, docs/discover.md).

`truth discover` (#1784) asks, for a *given* corpus statement, which premises
prove it. This adapter certifies a fixed, reviewable list of *conjectures*:
candidate conclusions and relationships (implications, incompatibilities,
strength orders) between two argument families that no target list named.
Candidate generation may be done by an agent; certification is deterministic
and kernel-backed. Nothing here writes a corpus record.

    python3 scripts/discover_conjecture.py binders CONFIG --out BINDERS.jsonl
    python3 scripts/discover_conjecture.py render CONFIG --binders BINDERS.jsonl --out FILE.lean
    python3 scripts/discover_conjecture.py classify CONFIG --binders BINDERS.jsonl \
        --lean-output OUT.txt --map FILE.lean.map.json [--json]
    python3 scripts/discover_conjecture.py run CONFIG --out-dir DIR [--json]

A configuration (TOML) lists the families (statement ids), and per candidate
its outer binders with their types, its premises (existing corpus statements,
each with an explicit mapping of *every* declaration parameter to an outer
binder), its conclusion (an existing statement, or a new Lean proposition over
the outer binders), optional countermodels and witness models (an assignment of
every outer binder), and an optional explicit OPEN bridge. Nothing is
identified by unification: an unmapped parameter is a configuration error.

Per candidate the rendered Lean file checks, each as its own declaration with
`#print axioms`:

* `main`: premises -> conclusion (`conjecture_unfold; duper [*]`);
* `vac`: premises -> False (an incompatibility, never support);
* `drop_i`: the goal without premise i (single-deletion minimization);
* `none`: the conclusion from no premise (a vocabulary theorem/tautology);
* `probe`: the folded transcription probe of `truth prove-sweep`;
* `litneg_i_j`: whether premise i unfolds definitionally to the negation of j;
* `cm_k`/`wit`: models checked by `decide` or `simp` (premises true,
  conclusion false; or premises and an optional antecedent instance true);
* `bridge`, `bridge_alone`, `bridge_vac`: an explicit OPEN bridge.

`classify` then applies the filters (known composition, transcription,
tautology, literal negation, vacuity, sense mismatch, identification by name
only, single family) and assigns each candidate one outcome: a verified
conditional implication, an incompatibility under the exact bundle, a
certified non-implication in a stated model, an OPEN bridge, rejected (with
the filter) or unresolved. A failed proof is unresolved unless a model is
certified. Identification is admissible only between parameters of the same
name in one Lean module, through one whole-binder sense tag shared by both
parameters, or as forced by such an identification of a relation whose type
mentions the carrier; two parameters of one declaration mapped to one binder
are an obligation. Single deletions are independent checks, so when more than
one succeeds the full bundle is kept and flagged; a premise counts as needed
only with a certified omission model. A verified implication is support only
with a certified joint witness, and every check is counted as proved only
within the three allowed axioms.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# The two tactics of `truth prove-sweep` (truth/src/prove_sweep.rs, PRELUDE),
# renamed: delta-unfold the project definitions in goal and hypotheses, and
# the single-premise-application transcription probe.
PRELUDE = r'''open Lean Meta Elab Tactic in
elab "conjecture_unfold" : tactic => do
  for _ in [0:8] do
    let env ← getEnv
    let g ← getMainGoal
    let names ← g.withContext do
      let mut found : NameSet := {}
      let mut types := #[← g.getType]
      for decl in ← getLCtx do
        unless decl.isImplementationDetail do types := types.push decl.type
      for ty in types do
        for n in (← instantiateMVars ty).getUsedConstants do
          if (`TruthCore).isPrefixOf n then
            if let some (.defnInfo _) := env.find? n then found := found.insert n
      return found
    if names.isEmpty then return
    let ids := names.toArray.map mkIdent
    try evalTactic (← `(tactic| delta $ids* at *)) catch _ => return

open Lean Meta Elab Tactic in
elab "conjecture_probe" : tactic => do
  evalTactic (← `(tactic| intros))
  let g ← getMainGoal
  g.withContext do
    if (← observing? g.assumption).isSome then
      setGoals []
      return
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless ← isProp decl.type do continue
      let saved ← saveState
      try
        let goals ← g.apply (mkFVar decl.fvarId)
        for sub in goals do
          unless ← sub.isAssigned do
            setGoals [sub]
            evalTactic (← `(tactic| first | assumption | rfl | exact True.intro | (constructor <;> assumption)))
        setGoals []
        return
      catch _ => restoreState saved
    throwError "conjecture_probe: no single premise application"
'''

SEARCH = "first | (intros; conjecture_unfold; duper [*]) | sorry"
MODEL = ("first | (beta_reduce; conjecture_unfold; beta_reduce; decide) | (beta_reduce; conjecture_unfold; simp; done)"
         " | (beta_reduce; conjecture_unfold; beta_reduce; simp [Fin.exists_fin_succ, Fin.forall_fin_succ]; done) | sorry")


class ConfigError(Exception):
    pass


# --- corpus -------------------------------------------------------------------------


class Corpus:
    """The corpus records the filters read: statements, arguments with results,
    strength relations and whole-binder sense tags."""

    def __init__(self, statements, arguments, results, relations, disambiguations):
        self.statements = {s["id"]: s for s in statements}
        self.alias = {}
        for s in statements:
            for key in (s["id"], s.get("legacy_id")):
                if key:
                    self.alias[key] = s["id"]
        verified = {r["argument_id"] for r in results}
        self.arguments = [a for a in arguments if a["id"] in verified]
        self.strengthens = {(r["subject_id"], r["object_id"]) for r in relations
                            if r.get("predicate") == "strengthens"}
        self.tags = {}  # (declaration, parameter) -> sense id (labels are not unique)
        self.sense_labels = {}
        for d in disambiguations:
            for sense in d.get("senses", []):
                key = sense.get("id") or f"{d.get('id')}:{sense['label']}"
                self.sense_labels[key] = sense["label"]
                for p in sense.get("lean_parameters", []) or []:
                    if p.get("arguments"):
                        continue  # a partial application never identifies a binder
                    # the first tag wins, as in the engine's reader
                    self.tags.setdefault((p["declaration"], p["parameter"]), key)

    @classmethod
    def load(cls, root: Path):
        def read(kind):
            return [json.loads(p.read_text()) for p in sorted((root / "corpus" / kind).glob("*.json"))]
        return cls(read("statements"), read("arguments"), read("results"),
                   read("relations"), read("disambiguations"))

    def resolve(self, token: str) -> str:
        if token in self.alias:
            return self.alias[token]
        matches = [i for i in self.statements if i.startswith(token)]
        if len(matches) == 1:
            return matches[0]
        raise ConfigError(f"unknown or ambiguous statement {token!r}")

    def declaration(self, sid: str) -> str:
        decl = self.statements[sid].get("lean_declaration")
        if not decl:
            raise ConfigError(f"statement {sid} has no lean_declaration")
        return decl

    def label(self, sid: str) -> str:
        return self.statements[sid].get("label", sid)

    def known(self, premises: list[str], conclusion: str) -> str | None:
        """Why `premises ⊢ conclusion` is already registered, or None."""
        if conclusion in premises:
            return "restatement: the conclusion is one of the premises"
        for p in premises:
            if (p, conclusion) in self.strengthens:
                return f"registered strength order {p[:8]} -> {conclusion[:8]}"
        have = set(premises)
        for a in self.arguments:
            if a["conclusion_statement_id"] == conclusion and set(a["premise_statement_ids"]) <= have:
                return f"registered argument {a['id'][:8]} from a subset of the premises"
        changed = True
        while changed:  # forward-chaining closure over verified arguments
            changed = False
            for a in self.arguments:
                c = a["conclusion_statement_id"]
                if c not in have and set(a["premise_statement_ids"]) <= have:
                    have.add(c)
                    changed = True
        if conclusion in have:
            return "follows by composing registered verified arguments (closure)"
        return None


# --- configuration -----------------------------------------------------------------


def load_config(path: Path) -> dict:
    with path.open("rb") as handle:
        config = tomllib.load(handle)
    if "candidate" not in config or "families" not in config:
        raise ConfigError("a configuration needs [families.*] and [[candidate]]")
    ids = [c["id"] for c in config["candidate"]]
    if len(ids) != len(set(ids)):
        raise ConfigError("candidate ids must be unique")
    return config


def declarations(config: dict, corpus: Corpus) -> list[str]:
    decls = set()
    for cand in config["candidate"]:
        for item in cand.get("premise", []):
            decls.add(corpus.declaration(corpus.resolve(item["statement"])))
        concl = cand["conclusion"]
        if "statement" in concl:
            decls.add(corpus.declaration(corpus.resolve(concl["statement"])))
    return sorted(decls)


def load_binders(path: Path) -> dict:
    """`DiscoverBinders.lean` output: declaration -> {module, binders}."""
    out = {}
    for line in path.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            if "error" in row:
                raise ConfigError(f"{row['declaration']}: {row['error']}")
            out[row["declaration"]] = row
    return out


def family_of(config: dict, corpus: Corpus) -> dict[str, str]:
    """statement -> family, for the families that count toward cross-family
    (a family with `cross_family = false`, such as a registered bridge, does
    not)."""
    owner = {}
    for name, fam in config["families"].items():
        if fam.get("cross_family", True) is False:
            continue
        for token in fam.get("statements", []):
            sid = corpus.resolve(token)
            if sid in owner and owner[sid] != name:
                raise ConfigError(f"statement {token} is in two families")
            owner[sid] = name
    return owner


class Occurrence:
    """One declaration applied in a candidate: its statement, declaration,
    module and parameter -> outer binder map."""

    def __init__(self, role, sid, decl, module, args):
        self.role, self.sid, self.decl, self.module, self.args = role, sid, decl, module, args


def occurrences(cand: dict, corpus: Corpus, binders: dict) -> list[Occurrence]:
    outer = {name for name, _ in cand["binders"]}
    found = []
    items = [("premise", p) for p in cand.get("premise", [])]
    if "statement" in cand["conclusion"]:
        items.append(("conclusion", cand["conclusion"]))
    for role, item in items:
        sid = corpus.resolve(item["statement"])
        decl = corpus.declaration(sid)
        if decl not in binders:
            raise ConfigError(f"{cand['id']}: no binder export for {decl}")
        params = [b[0] for b in binders[decl]["binders"] if not b[2]]
        args = item.get("args", {})
        missing = [p for p in params if p not in args]
        extra = [p for p in args if p not in params]
        if missing or extra:
            raise ConfigError(f"{cand['id']}: {decl} parameters unmapped {missing}, unknown {extra}")
        for p, b in args.items():
            if b not in outer:
                raise ConfigError(f"{cand['id']}: {decl}.{p} maps to undeclared binder {b!r}")
        found.append(Occurrence(role, sid, decl, binders[decl]["module"], args))
    return found


# --- rendering ---------------------------------------------------------------------


def applied(occ_decl: str, args: dict) -> str:
    named = " ".join(f"({p} := {b})" for p, b in args.items())
    return f"({occ_decl} {named})" if named else occ_decl


def model_claim(binders: list, body: str, assign: dict) -> str:
    """A claim about one model: the body abstracted over the typed outer
    binders and applied to the assigned values, so every value elaborates
    against its binder's type."""
    lam = " ".join(f"({n} : {t})" for n, t in binders)
    vals = " ".join(f"({assign[n]})" for n, _ in binders)
    return f"(fun {lam} => {body}) {vals}"


def render(config: dict, corpus: Corpus, binders: dict) -> tuple[str, dict]:
    """The certification file and a map from declaration name to its candidate,
    check and line range."""
    run = config.get("run", {})
    imports = run.get("imports", ["TruthCore", "Duper"])
    heartbeats = int(run.get("heartbeats", 200000))
    namespace = run.get("namespace", "TruthCore.ConjecturePilot")
    lines = [f"import {m}" for m in imports]
    lines += ["", "set_option linter.all false", ""] + PRELUDE.splitlines() + [f"namespace {namespace}", ""]
    for o in run.get("opens", []):
        lines.append(f"open {o}")
    spans = {}

    def add(name, cand_id, check, statement, tactic, extra=None):
        start = len(lines) + 1
        lines.append(f"set_option maxHeartbeats {heartbeats} in")
        lines.append(f"theorem {name} : {statement} := by")
        lines.append(f"  {tactic}")
        lines.append(f"#print axioms {name}")
        lines.append("")
        spans[f"{namespace}.{name}"] = {"candidate": cand_id, "check": check, "lines": [start, len(lines)], **(extra or {})}

    for cand in config["candidate"]:
        occs = occurrences(cand, corpus, binders)
        cid = re.sub(r"\W", "_", cand["id"])
        names = [n for n, _ in cand["binders"]]
        quant = " ".join(f"({n} : {t})" for n, t in cand["binders"])
        concl = cand["conclusion"]

        hyps = [applied(o.decl, o.args) for o in occs if o.role == "premise"]
        if "statement" in concl:
            c = next(o for o in occs if o.role == "conclusion")
            goal = applied(c.decl, c.args)
        else:
            goal = f"({concl['lean']})"

        def stmt(hs, target):
            body = " → ".join(hs + [target])
            return f"∀ {quant}, {body}" if names else body

        add(f"{cid}_main", cand["id"], "main", stmt(hyps, goal), SEARCH)
        add(f"{cid}_vac", cand["id"], "vac", stmt(hyps, "False"), SEARCH)
        add(f"{cid}_none", cand["id"], "none", stmt([], goal), SEARCH)
        add(f"{cid}_probe", cand["id"], "probe", stmt(hyps, goal), "first | conjecture_probe | sorry")
        for i in range(len(hyps)):
            rest = hyps[:i] + hyps[i + 1:]
            add(f"{cid}_drop{i}", cand["id"], "drop", stmt(rest, goal), SEARCH, {"premise": i})
            add(f"{cid}_vacdrop{i}", cand["id"], "vacdrop", stmt(rest, "False"), SEARCH, {"premise": i})
        for i in range(len(hyps)):
            for j in range(len(hyps)):
                if i != j:
                    add(f"{cid}_litneg{i}_{j}", cand["id"], "litneg",
                        stmt([], f"({hyps[i]} = ¬ {hyps[j]})"), "first | (intros; rfl) | sorry",
                        {"pair": [i, j]})
        for k, model in enumerate(cand.get("countermodel", [])):
            assign = model["assign"]
            if set(assign) != set(names):
                raise ConfigError(f"{cand['id']}: countermodel {k} must assign every outer binder")
            prem_ids = [o.sid for o in occs if o.role == "premise"]
            omit = {prem_ids.index(corpus.resolve(t)) for t in model.get("omit", [])}
            kept = [h for i, h in enumerate(hyps) if i not in omit]
            body = model_claim(cand["binders"], " ∧ ".join(kept + [f"¬ {goal}"]), assign)
            add(f"{cid}_cm{k}", cand["id"], "countermodel", body, MODEL, {"model": k, "omit": sorted(omit)})
        if "witness" in cand:
            assign = cand["witness"]["assign"]
            if set(assign) != set(names):
                raise ConfigError(f"{cand['id']}: the witness must assign every outer binder")
            parts = hyps + ([f"({cand['witness']['instance']})"] if cand["witness"].get("instance") else [])
            body = model_claim(cand["binders"], " ∧ ".join(parts or ["True"]), assign)
            add(f"{cid}_wit", cand["id"], "witness", body, MODEL)
        if "bridge" in cand:
            bridge = f"({cand['bridge']['lean']})"
            add(f"{cid}_bridge", cand["id"], "bridge", stmt(hyps + [bridge], goal), SEARCH)
            add(f"{cid}_bridge_alone", cand["id"], "bridge_alone", stmt([bridge], goal), SEARCH)
            add(f"{cid}_bridge_vac", cand["id"], "bridge_vac", stmt(hyps + [bridge], "False"), SEARCH)
    lines += [f"end {namespace}", ""]
    return "\n".join(lines), spans


# --- Lean output -------------------------------------------------------------------

AXIOMS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")
ERROR = re.compile(r"^[^:\n]*:(\d+):(\d+): error")


def parse_lean(output: str, spans: dict) -> dict:
    """name -> {proved, axioms, error}. A check is proved when its declaration
    printed axioms without `sorryAx` and no error falls inside its lines."""
    axioms = {}
    for m in AXIOMS.finditer(output):
        axioms[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in NO_AXIOMS.finditer(output):
        axioms[m.group(1)] = []
    errors = [int(m.group(1)) for m in map(ERROR.match, output.splitlines()) if m]
    status = {}
    for name, span in spans.items():
        lo, hi = span["lines"]
        err = any(lo <= line <= hi for line in errors)
        ax = axioms.get(name)
        closed = ax is not None and "sorryAx" not in ax and not err
        outside = sorted(set(ax or []) - ALLOWED_AXIOMS - {"sorryAx"})
        # every check, not only the goal, counts as proved only within the allowed axioms
        status[name] = {"proved": closed and not outside, "closed": closed, "outside_axioms": outside,
                        "axioms": ax, "error": err or ax is None, "elaboration_error": err}
    return status


# --- identification ----------------------------------------------------------------


def identification(cand: dict, occs: list[Occurrence], corpus: Corpus) -> dict:
    """Admissibility of every outer binder that fills two parameters.

    The engine's rule (docs/discover.md, Goal): two parameter occurrences of
    one outer binder are linked when they have the same parameter name and
    their declarations are in the same Lean module, or when both parameters
    carry the same whole-binder sense tag. A carrier occurrence is also linked
    when such a link joins two occurrences of a relation whose declared type
    mentions the carrier (typing then forces the carriers equal). Two
    parameters of one occurrence mapped to one binder identify two different
    parameters of one declaration: that is never linked by the module rule.
    A binder whose occurrences are not all connected is an identification
    obligation; differently tagged occurrences are a sense mismatch."""
    types = dict((n, t) for n, t in cand["binders"])
    carriers = {n for n, t in cand["binders"] if t.strip() in ("Type", "Prop") or t.strip().startswith(("Sort", "Type "))}
    by_binder = {}
    for k, o in enumerate(occs):
        for p, b in o.args.items():
            by_binder.setdefault(b, []).append((k, p))
    edges = {b: set() for b in by_binder}
    mismatches, admissions = [], []

    def tag(k, p):
        return corpus.tags.get((occs[k].decl, p))

    def label(t):
        return corpus.sense_labels.get(t, t)

    def direct(b, uses):
        for x in range(len(uses)):
            for y in range(x + 1, len(uses)):
                (k1, p1), (k2, p2) = uses[x], uses[y]
                t1, t2 = tag(k1, p1), tag(k2, p2)
                if k1 != k2 and p1 == p2 and occs[k1].module == occs[k2].module:
                    edges[b].add((x, y))
                    admissions.append((b, "same name and module", occs[k1].decl, occs[k2].decl))
                elif t1 and t1 == t2:
                    edges[b].add((x, y))
                    admissions.append((b, f"shared sense {label(t1)}", occs[k1].decl, occs[k2].decl))
                if t1 and t2 and t1 != t2:
                    mismatches.append({"binder": b, "senses": [label(t1), label(t2)],
                                       "declarations": [f"{occs[k1].decl}.{p1}", f"{occs[k2].decl}.{p2}"]})

    for b, uses in by_binder.items():
        if b not in carriers:
            direct(b, uses)
    for b, uses in by_binder.items():
        if b not in carriers:
            continue
        direct(b, uses)
        # carriers forced by an admissible identification of a relation over them
        first = {}
        for x, (k, _) in enumerate(uses):
            first.setdefault(k, x)
        for r, ruses in by_binder.items():
            if r in carriers or not re.search(rf"(?<![\w.']){re.escape(b)}(?![\w'])", types.get(r, "")):
                continue
            for (x, y) in edges[r]:
                k1, k2 = ruses[x][0], ruses[y][0]
                if k1 in first and k2 in first and k1 != k2:
                    edges[b].add((first[k1], first[k2]))
    obligations = []
    for b, uses in by_binder.items():
        if len(uses) < 2:
            continue
        parent = list(range(len(uses)))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i
        for x, y in edges[b]:
            parent[find(x)] = find(y)
        groups = {}
        for x, (k, p) in enumerate(uses):
            groups.setdefault(find(x), []).append(f"{occs[k].decl}.{p}")
        if len(groups) > 1:
            within = sorted({occs[k].decl for k, _ in uses if sum(1 for kk, _ in uses if kk == k) > 1})
            ob = {"binder": b, "unlinked_groups": sorted(sorted(g) for g in groups.values())}
            if within:
                ob["same_declaration"] = within
            obligations.append(ob)
    return {"obligations": obligations, "mismatches": mismatches,
            "admitted": [{"binder": b, "by": why, "declarations": [d1, d2]} for b, why, d1, d2 in admissions]}


# --- classification ----------------------------------------------------------------


def classify(config: dict, corpus: Corpus, binders: dict, status: dict, spans: dict) -> list[dict]:
    owner = family_of(config, corpus)
    namespace = config.get("run", {}).get("namespace", "TruthCore.ConjecturePilot")
    reports = []
    for cand in config["candidate"]:
        cid = re.sub(r"\W", "_", cand["id"])

        def check(name):
            return status.get(f"{namespace}.{cid}_{name}", {"proved": False, "closed": False, "outside_axioms": [],
                                                              "axioms": None, "error": True, "elaboration_error": False})
        occs = occurrences(cand, corpus, binders)
        prem = [o for o in occs if o.role == "premise"]
        concl_sid = corpus.resolve(cand["conclusion"]["statement"]) if "statement" in cand["conclusion"] else None
        report = {
            "id": cand["id"], "template": cand.get("template", ""), "kind": cand.get("kind", "implication"),
            "meaning": cand.get("meaning", ""), "scope": cand.get("scope", ""), "matters": cand.get("matters", ""),
            "premises": [o.sid for o in prem], "conclusion": concl_sid or "new: " + cand["conclusion"]["lean"],
            "families": sorted({owner.get(o.sid, "?") for o in occs}), "filters": [], "flags": [],
        }
        main, vac, none, probe = check("main"), check("vac"), check("none"), check("probe")
        certified = [s for n, s in spans.items() if s["candidate"] == cand["id"]
                     and s["check"] == "countermodel" and status.get(n, {}).get("proved")]
        omissions = [{"omit": [prem[i].sid for i in s["omit"]], "model": s["model"]} for s in certified if s["omit"]]
        if omissions:
            report["omission_models"] = omissions
        # an error inside a model, witness or bridge text is a configuration error, not a failed proof
        config_errors = sorted({s["check"] + (str(s["model"]) if "model" in s else "") for n, s in spans.items()
                                if s["candidate"] == cand["id"] and s["check"] in ("countermodel", "witness", "bridge", "bridge_alone", "bridge_vac")
                                and status.get(n, {}).get("elaboration_error")})
        if config_errors:
            report["config_errors"] = config_errors
        outside = sorted({a for n, s in spans.items() if s["candidate"] == cand["id"]
                          for a in status.get(n, {}).get("outside_axioms", [])})
        if outside:
            report["flags"].append(f"axioms outside the allowed three in some check ({', '.join(outside)}): those checks count as unproved")
        # "error" only when the goal produced no declaration; an error inside a
        # produced goal (say a heartbeat timeout escaping `first`) leaves it
        # unproved, and models and bridges are still classified.
        if main["axioms"] is None:
            report["outcome"], report["reason"] = "error", "the goal did not elaborate"
            reports.append(report)
            continue
        ident = identification(cand, occs, corpus)
        report["identification"] = ident
        # Single deletions are independent checks: two redundant premises may each
        # be droppable alone but not together. Only one succeeding deletion is
        # taken; with several, the full bundle is kept and flagged.
        droppable = [i for i in range(len(prem)) if check(f"drop{i}")["proved"]]
        if len(droppable) > 1:
            needed = list(range(len(prem)))
            report["flags"].append("several single deletions succeed; their joint deletion is untested, so the full bundle is kept (not minimized)")
        else:
            needed = [i for i in range(len(prem)) if i not in droppable]
        omitted_certified = {o for s in certified if len(s["omit"]) == 1 for o in s["omit"]}
        report["premise_status"] = {
            prem[i].sid: ("needed (omission model certified)" if i in omitted_certified
                          else "dropped (deletion re-proved)" if i not in needed
                          else "kept: several single deletions succeeded; joint deletion untested" if i in droppable
                          else "not dropped (unresolved: deletion failed within the budget)")
            for i in range(len(prem))}
        report["axioms"] = main["axioms"]
        if vac["proved"]:
            core = [i for i in range(len(prem)) if not check(f"vacdrop{i}")["proved"]]
            report["inconsistent_core"] = [prem[i].sid for i in core]
            literal = [(i, j) for i in core for j in core if i != j and check(f"litneg{i}_{j}")["proved"]]
            if literal:
                report["outcome"] = "rejected"
                report["filters"].append("literal_negation")
                report["reason"] = "a premise unfolds definitionally to the negation of another: inconsistent by construction, neither support nor a discovered incompatibility"
            elif ident["mismatches"] or ident["obligations"]:
                report["outcome"] = "open_bridge"
                report["filters"].append("senses" if ident["mismatches"] else "name_only_identification")
                report["reason"] = "the premises refute each other only under the listed identifications"
            else:
                report["outcome"] = "incompatibility"
                report["reason"] = "the premise bundle proves False: at least one member fails; it supports nothing"
                if len({owner[x] for x in report["inconsistent_core"] if x in owner}) < 2:
                    report["flags"].append("single family: the inconsistent core lies in one family")
            report["support"] = False
            reports.append(report)
            continue
        if main["closed"]:
            if main["outside_axioms"]:
                report["outcome"], report["reason"] = "rejected", "axioms outside propext, Classical.choice, Quot.sound"
                report["filters"].append("axioms")
            elif none["proved"]:
                report["outcome"], report["reason"] = "rejected", "the conclusion follows from no premise (vocabulary theorem/tautology)"
                report["filters"].append("tautology")
            elif probe["proved"]:
                report["outcome"], report["reason"] = "rejected", "one premise application closes the folded goal (invariant 16)"
                report["filters"].append("transcription")
            elif concl_sid and (why := corpus.known([prem[i].sid for i in needed], concl_sid)):
                report["outcome"], report["reason"] = "rejected", f"known: {why}"
                report["filters"].append("known")
            elif ident["mismatches"]:
                report["outcome"], report["reason"] = "rejected", "a binder joins two different senses of one term"
                report["filters"].append("senses")
            elif ident["obligations"]:
                report["outcome"] = "open_bridge"
                report["reason"] = "valid only under identifications that no module convention or sense tag licenses; not a theorem about the statements"
                report["filters"].append("name_only_identification")
            elif len({owner[x] for x in [prem[i].sid for i in needed] + [concl_sid] if x in owner}) < 2:
                report["outcome"], report["reason"] = "rejected", "the minimal premises and conclusion lie in one family"
                report["filters"].append("single_family")
            else:
                report["outcome"] = "verified_conditional_implication"
                report["reason"] = "kernel-checked from the minimal premises; establishes nothing about their truth"
            report["minimal_premises"] = [prem[i].sid for i in needed]
            report["dropped_premises"] = [prem[i].sid for i in range(len(prem)) if i not in needed]
            witnessed = "witness" in cand and check("wit")["proved"]
            if witnessed:
                report["flags"].append("witness: premises jointly satisfied in the stated model"
                                       + (", with an instance of the antecedent" if cand["witness"].get("instance") else
                                          "; antecedent instance not checked"))
            elif "witness" in cand:
                report["flags"].append("witness: stated model not certified; consistency unresolved; not support")
            else:
                report["flags"].append("witness: none supplied; consistency unresolved; not support")
            report["support"] = report["outcome"] == "verified_conditional_implication" and witnessed
            reports.append(report)
            continue
        full = [s for s in certified if not s["omit"]]
        report["support"] = False
        bridged = "bridge" in cand and check("bridge")["proved"] and not check("bridge_alone")["proved"] \
            and not check("bridge_vac")["proved"]
        if bridged:
            under = " under the listed identifications" if ident["obligations"] or ident["mismatches"] else ""
            report["bridge"] = dict(cand["bridge"], verified=(
                f"one sufficient OPEN bridge{under} (not shown to be weakest): the premises with it prove the "
                "conclusion; it alone does not; no contradiction was found"))
        if full:
            report["outcome"] = "certified_non_implication"
            report["reason"] = f"model {full[0]['model']} makes every premise true and the conclusion false"
        elif bridged:
            report["outcome"] = "open_bridge"
            report["reason"] = "the premises with the explicit bridge prove the conclusion; the bridge alone does not; it stays OPEN"
        else:
            report["outcome"] = "unresolved"
            report["reason"] = "no proof within the budget and no certified countermodel: not a refutation"
        reports.append(report)
    return reports


# --- commands ----------------------------------------------------------------------


def lake(args: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["lake", "env", "lean", *args], cwd=cwd, capture_output=True, text=True)


def export_binders(config: dict, corpus: Corpus, out: Path, root: Path) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as handle:
        handle.write("\n".join(declarations(config, corpus)) + "\n")
    proc = lake(["--run", "scripts/DiscoverBinders.lean", "TruthCore", handle.name], root)
    if proc.returncode:
        raise SystemExit(proc.stderr or proc.stdout)
    out.write_text(proc.stdout)


def summarize(reports: list[dict], corpus: Corpus) -> str:
    rows = []
    for r in reports:
        concl = r["conclusion"] if r["conclusion"].startswith("new:") else f"{corpus.label(r['conclusion'])[:60]} [{r['conclusion'][:8]}]"
        rows.append(f"{r['id']}: {r['outcome']}{' (' + ', '.join(r['filters']) + ')' if r['filters'] else ''}\n"
                    f"  conclusion: {concl[:110]}\n  reason: {r['reason']}")
        for ob in r.get("identification", {}).get("obligations", []):
            rows.append(f"  obligation {ob['binder']}: {' / '.join('+'.join(g) for g in ob['unlinked_groups'])}")
        for mm in r.get("identification", {}).get("mismatches", []):
            rows.append(f"  sense mismatch {mm['binder']}: {mm['senses']}")
        if r.get("bridge"):
            rows.append(f"  OPEN bridge: {r['bridge']['lean']}")
        if r.get("minimal_premises") is not None and r.get("dropped_premises"):
            rows.append(f"  dropped (not needed): {', '.join(x[:8] for x in r['dropped_premises'])}")
        for om in r.get("omission_models", []):
            rows.append(f"  omission model {om['model']}: omitting {', '.join(x[:8] for x in om['omit'])} keeps the conclusion false")
    counts = {}
    for r in reports:
        counts[r["outcome"]] = counts.get(r["outcome"], 0) + 1
    return "\n".join(rows) + "\n\n" + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) + "\n"


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("binders", "render", "classify", "run"):
        p = sub.add_parser(name)
        p.add_argument("config", type=Path)
        p.add_argument("--root", type=Path, default=ROOT)
        if name in ("render", "classify"):
            p.add_argument("--binders", type=Path, required=True)
        if name in ("binders", "render"):
            p.add_argument("--out", type=Path, required=True)
        if name == "classify":
            p.add_argument("--lean-output", type=Path, required=True)
            p.add_argument("--map", type=Path, required=True)
        if name == "run":
            p.add_argument("--out-dir", type=Path, required=True)
        if name in ("classify", "run"):
            p.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        config = load_config(args.config)
        corpus = Corpus.load(args.root)
        if args.command == "binders":
            export_binders(config, corpus, args.out, args.root)
            return 0
        if args.command == "render":
            text, spans = render(config, corpus, load_binders(args.binders))
            args.out.write_text(text)
            Path(str(args.out) + ".map.json").write_text(json.dumps(spans, indent=1))
            return 0
        if args.command == "classify":
            spans = json.loads(args.map.read_text())
            status = parse_lean(args.lean_output.read_text(), spans)
            reports = classify(config, corpus, load_binders(args.binders), status, spans)
        else:
            out = args.out_dir
            out.mkdir(parents=True, exist_ok=True)
            # Duper is a pinned package that `lake build` of the library does not build.
            built = subprocess.run(["lake", "build", "Duper", "TruthCore"], cwd=args.root, capture_output=True, text=True)
            if built.returncode:
                raise SystemExit(built.stderr or built.stdout)
            export_binders(config, corpus, out / "binders.jsonl", args.root)
            binders = load_binders(out / "binders.jsonl")
            text, spans = render(config, corpus, binders)
            lean_file = out / "Conjectures.lean"
            lean_file.write_text(text)
            (out / "Conjectures.lean.map.json").write_text(json.dumps(spans, indent=1))
            proc = lake([str(lean_file.resolve())], args.root)
            (out / "lean-output.txt").write_text(proc.stdout + proc.stderr)
            status = parse_lean(proc.stdout + proc.stderr, spans)
            reports = classify(config, corpus, binders, status, spans)
            (out / "report.json").write_text(json.dumps(reports, indent=1, ensure_ascii=False))
    except ConfigError as exc:
        print(f"discover_conjecture: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(reports, indent=1, ensure_ascii=False) if args.json else summarize(reports, corpus), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
