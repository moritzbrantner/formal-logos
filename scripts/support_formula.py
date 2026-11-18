#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = ["dd==0.6.0", "networkx==3.4.2"]
# ///
"""Count exact minimal premise combinations in the registered argument graph.

Run with `uv run scripts/support_formula.py`; the Rust `truth support-graph`
command owns corpus extraction. `--graph FILE` replays that exported graph.
The default terminal basis reproduces the November 2026 calculation. A false
input means a premise is not supplied, not that its negation is accepted.
"""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import gc
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import time
import unittest

import dd
from dd import autoref
import networkx as nx

try:  # CUDD is faster; PyPI wheels of dd ship without it, so fall back to pure Python.
    from dd import cudd
except ImportError:
    cudd = None

import truth_cli

ROOT = Path(__file__).resolve().parents[1]


def progress(event, **data):
    print(json.dumps({"event": event, **data}, sort_keys=True), file=sys.stderr, flush=True)


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def graph_digest(graph):
    inputs = {key: graph[key] for key in ("target_statement_ids", "statements", "rules")}
    return hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def validate_graph(graph):
    if graph.get("schema_version") != 1:
        raise ValueError("Expected support-graph schema_version 1")
    if graph.get("kind") != "registered-support-graph" or graph.get("complete") is not True:
        raise ValueError("Expected a complete registered-support-graph export")
    statements = {s["id"]: s for s in graph["statements"]}
    if len(statements) != len(graph["statements"]):
        raise ValueError("Duplicate statement IDs in support graph")
    targets = graph["target_statement_ids"]
    if not targets or len(set(targets)) != len(targets) or not set(targets) <= statements.keys():
        raise ValueError("Targets must be distinct known statement IDs")
    rule_ids = set()
    conclusions = set()
    for rule in graph["rules"]:
        rid = rule["argument_id"]
        if rid in rule_ids:
            raise ValueError(f"Duplicate argument ID: {rid}")
        rule_ids.add(rid)
        premises = rule["premise_statement_ids"]
        conclusion = rule["conclusion_statement_id"]
        if conclusion not in statements or not set(premises) <= statements.keys():
            raise ValueError(f"Unknown statement in argument {rid}")
        if len(premises) != len(set(premises)):
            raise ValueError(f"Duplicate premise in argument {rid}")
        conclusions.add(conclusion)
    terminals = set(statements) - conclusions
    if set(graph["terminal_statement_ids"]) != terminals:
        raise ValueError("Terminal input list does not match result-backed rules")
    return statements, terminals


def load_graph(args):
    if args.graph:
        if args.statements:
            raise ValueError("Targets are fixed by --graph; omit positional statements")
        graph = json.loads(args.graph.read_text(encoding="utf-8"))
    else:
        command = ["--json", "support-graph", *args.statements]
        prefix = ([str(args.truth.resolve())] if args.truth else
                  truth_cli.command(args.repo.resolve(), existing_build=False))
        completed = subprocess.run(
            [*prefix, "--root", str(args.repo.resolve()), *command],
            cwd=args.repo, capture_output=True, text=True, timeout=args.export_timeout, check=False)
        if completed.returncode:
            raise RuntimeError(f"truth support-graph failed ({completed.returncode}): {completed.stderr.strip()}")
        graph = json.loads(completed.stdout)
    validate_graph(graph)
    return graph


_AUTOREF_MANAGERS = []


def new_bdd(memory_mib=None):
    """A BDD manager with complemented edges: CUDD if built, else `dd.autoref`.

    Both backends return regular-node children from `succ`, signed node
    references and canonical reduced diagrams, so every exact count, size and
    minimal family is identical; only node counts under dynamic reordering and
    speed may differ.
    """
    if cudd is None:
        bdd = autoref.BDD()
        # dd.bdd asserts on collection while Functions in reference cycles
        # still point into it; retain managers for the process lifetime.
        _AUTOREF_MANAGERS.append(bdd)
        return bdd
    if memory_mib is None:
        return cudd.BDD()
    bdd = cudd.BDD(memory_estimate=memory_mib * 1024**2)
    bdd.configure(max_memory=memory_mib * 1024**2)
    return bdd


def effective_children(bdd, node):
    """Both backends expose regular-node children; complemented edges invert both."""
    level, low, high = bdd.succ(node)
    return (level, ~low, ~high) if node.negated else (level, low, high)


def require_fixed_order(bdd):
    if bdd.configure()["reordering"]:
        raise RuntimeError("Exact traversal requires a fixed BDD variable order")


def exact_count(bdd, root):
    """Integer model count, including skipped variables; never CUDD floats."""
    require_fixed_order(bdd)
    n = len(bdd.vars)
    cache = {}

    def walk(node):
        if node == bdd.false:
            return n, 0
        if node == bdd.true:
            return n, 1
        key = int(node)
        if key not in cache:
            level, low, high = effective_children(bdd, node)
            ll, lc = walk(low)
            hl, hc = walk(high)
            cache[key] = level, (lc << (ll - level - 1)) + (hc << (hl - level - 1))
        return cache[key]

    level, count = walk(root)
    return count << level


def exact_histogram(bdd, root, node_limit):
    """Exact size histogram when affordable; this limit never caps the count."""
    require_fixed_order(bdd)
    if root.dag_size > node_limit:
        return None
    n = len(bdd.vars)
    cache = {}

    def multiply_skips(poly, skip, shift=0):
        result = defaultdict(int)
        for k, value in poly.items():
            for i in range(skip + 1):
                result[k + i + shift] += value * math.comb(skip, i)
        return dict(result)

    def walk(node):
        if node == bdd.false:
            return n, {}
        if node == bdd.true:
            return n, {0: 1}
        key = int(node)
        if key not in cache:
            level, low, high = effective_children(bdd, node)
            ll, lp = walk(low)
            hl, hp = walk(high)
            result = multiply_skips(lp, ll - level - 1)
            for k, value in multiply_skips(hp, hl - level - 1, 1).items():
                result[k] = result.get(k, 0) + value
            cache[key] = level, result
        return cache[key]

    level, histogram = walk(root)
    return dict(sorted(multiply_skips(histogram, level).items()))


def minmax_size(bdd, root):
    require_fixed_order(bdd)
    n = len(bdd.vars)
    cache = {}

    def walk(node):
        if node == bdd.false:
            return n, math.inf, -math.inf
        if node == bdd.true:
            return n, 0, 0
        key = int(node)
        if key not in cache:
            level, low, high = effective_children(bdd, node)
            ll, lmin, lmax = walk(low)
            hl, hmin, hmax = walk(high)
            cache[key] = level, min(lmin, 1 + hmin), max(lmax + ll - level - 1, 1 + hmax + hl - level - 1)
        return cache[key]

    level, minimum, maximum = walk(root)
    return (None, None) if minimum == math.inf else (minimum, maximum + level)


def minimal_models(bdd, formula, variables):
    """A monotone support is minimal iff removing any included input loses F."""
    support = bdd.support(formula)
    minimal = formula
    for variable in variables:
        if variable in support:
            minimal &= ~bdd.var(variable) | ~bdd.let({variable: False}, formula)
        else:
            minimal &= ~bdd.var(variable)
    return minimal


def minimal_by_shannon(bdd, formula):
    """Independent recurrence: Min(ite(x,H,L)) = ite(x,Min(H)&~L,Min(L))."""
    require_fixed_order(bdd)
    n = len(bdd.vars)
    cache = {}

    def level_of(node):
        return n if node in (bdd.true, bdd.false) else bdd.succ(node)[0]

    def pad_zero(node, start, end):
        for level in range(end - 1, start - 1, -1):
            node = bdd.ite(bdd.var(bdd.var_at_level(level)), bdd.false, node)
        return node

    def walk(node):
        if node in (bdd.true, bdd.false):
            return node
        key = int(node)
        if key not in cache:
            level, low, high = effective_children(bdd, node)
            low_min = pad_zero(walk(low), level + 1, level_of(low))
            high_min = pad_zero(walk(high), level + 1, level_of(high)) & ~low
            cache[key] = bdd.ite(bdd.var(bdd.var_at_level(level)), high_min, low_min)
        return cache[key]

    return pad_zero(walk(formula), 0, level_of(formula))


def forward_closure(seeds, rules):
    reached = set(seeds)
    dependents = defaultdict(list)
    outstanding = []
    queue = deque(seeds)
    for i, rule in enumerate(rules):
        premises = rule["premise_statement_ids"]
        conclusion = rule["conclusion_statement_id"]
        outstanding.append(len(premises))
        for premise in premises:
            dependents[premise].append(i)
        if not premises and conclusion not in reached:
            reached.add(conclusion)
            queue.append(conclusion)
    while queue:
        for i in dependents[queue.popleft()]:
            outstanding[i] -= 1
            conclusion = rules[i]["conclusion_statement_id"]
            if outstanding[i] == 0 and conclusion not in reached:
                reached.add(conclusion)
                queue.append(conclusion)
    return reached


def solve_graph(graph, basis="terminal", memory_mib=2048):
    statements, terminals = validate_graph(graph)
    if basis not in ("terminal", "direct-or-derived"):
        raise ValueError(f"Unknown input basis: {basis}")
    sys.setrecursionlimit(max(sys.getrecursionlimit(), len(statements) * 4 + 1000))
    dependencies = nx.DiGraph()
    dependencies.add_nodes_from(sorted(statements))
    for rule in graph["rules"]:
        for premise in rule["premise_statement_ids"]:
            dependencies.add_edge(premise, rule["conclusion_statement_id"])
    sccs = sorted(tuple(sorted(c)) for c in nx.strongly_connected_components(dependencies))
    condensation = nx.condensation(dependencies, sccs)
    order = list(nx.lexicographical_topological_sort(condensation, key=lambda c: sccs[c]))
    variable_statements = []
    visited = set()
    for start in [*graph["target_statement_ids"], *sorted(statements)]:
        pending = [start]
        while pending:
            statement = pending.pop()
            if statement in visited:
                continue
            visited.add(statement)
            variable_statements.append(statement)
            children = sorted(dependencies.predecessors(statement), key=lambda s: (
                dependencies.out_degree(s), statements[s].get("legacy_id") or s, s))
            pending.extend(reversed(children))
    variables = {s: f"p{i:04d}" for i, s in enumerate(variable_statements)}
    bdd = new_bdd(memory_mib)
    bdd.configure(reordering=True)
    bdd.declare(*variables.values())
    formulas = {s: bdd.var(v) if basis == "direct-or-derived" or s in terminals else bdd.false
                for s, v in variables.items()}
    by_component = defaultdict(list)
    for rule in graph["rules"]:
        by_component[condensation.graph["mapping"][rule["conclusion_statement_id"]]].append(rule)
    passes = 0
    for i, component in enumerate(order):
        while True:
            changed = False
            passes += 1
            for rule in by_component[component]:
                product = bdd.true
                for premise in sorted(rule["premise_statement_ids"], key=lambda s: formulas[s].dag_size):
                    product &= formulas[premise]
                conclusion = rule["conclusion_statement_id"]
                value = formulas[conclusion] | product
                if value != formulas[conclusion]:
                    formulas[conclusion] = value
                    changed = True
            if not changed:
                break
        if (i + 1) % 100 == 0:
            progress("closure", components=i + 1, total=len(order), nodes=len(bdd))
    # Never assume the requested conclusion itself, including a terminal target.
    roots = {s: bdd.let({variables[s]: False}, formulas[s]) for s in graph["target_statement_ids"]}
    bdd.configure(reordering=False)
    return bdd, roots, variables, {"components": len(order), "passes": passes}


def check_closure(bdd, roots, variables, graph, basis):
    """Deterministic differential checks against queue-based forward chaining."""
    ids = sorted(variables)
    allowed = set(graph["terminal_statement_ids"]) if basis == "terminal" else set(ids)
    rng = random.Random(960267)
    selections = [set(), set(ids), *({s} for s in ids)]
    for probability in (0.01, 0.03, 0.1, 0.25, 0.5, 0.75, 0.95):
        for _ in range(24):
            selections.append({s for s in ids if rng.random() < probability})
    for selection in selections:
        for target, formula in roots.items():
            effective = (selection & allowed) - {target}
            assignment = {variable: sid in effective for sid, variable in variables.items()}
            actual = bdd.let(assignment, formula) == bdd.true
            expected = target in forward_closure(effective, graph["rules"])
            if actual != expected:
                raise RuntimeError(f"Symbolic/forward closure disagreement for {target}")
    return {"deterministic_input_sets": len(selections), "comparisons": len(selections) * len(roots)}


def representative_supports(bdd, minimal, variables, target, rules, count=3):
    by_variable = {v: s for s, v in variables.items()}
    remaining = minimal
    examples = []
    for _ in range(count):
        cache = {}

        def smallest(node):
            if node == bdd.false:
                return math.inf, frozenset()
            if node == bdd.true:
                return 0, frozenset()
            key = int(node)
            if key not in cache:
                level, low, high = effective_children(bdd, node)
                lc, ls = smallest(low)
                hc, hs = smallest(high)
                cache[key] = (lc, ls) if lc <= hc + 1 else (hc + 1, hs | {bdd.var_at_level(level)})
            return cache[key]

        size, chosen = smallest(remaining)
        if size == math.inf:
            break
        support = {by_variable[v] for v in chosen}
        if target not in forward_closure(support, rules) or any(
                target in forward_closure(support - {s}, rules) for s in support):
            raise RuntimeError(f"Representative support replay/minimality failed for {target}")
        examples.append({"statement_ids": sorted(support), "premise_count": len(support),
                         "forward_replay": True, "every_single_deletion_fails": True})
        conjunction = bdd.true
        for variable in chosen:
            conjunction &= bdd.var(variable)
        remaining &= ~conjunction
    return examples


def export_bdds(bdd, roots, variables, path):
    """Exact signed-edge ROBDD; the dictionary is embedded to recover all sets."""
    require_fixed_order(bdd)
    ids, nodes, retained = {}, [], []

    def edge(node):
        if node == bdd.true:
            return 1
        if node == bdd.false:
            return -1
        sign = -1 if node.negated else 1
        regular = ~node if node.negated else node
        key = int(regular)
        if key not in ids:
            ident = len(nodes) + 2
            ids[key] = ident
            nodes.append(None)
            retained.append(regular)
            level, low, high = bdd.succ(regular)
            nodes[ident - 2] = [level, edge(low), edge(high)]
        return sign * ids[key]

    entries = {name: edge(root) for name, root in roots.items()}
    data = {"format": "signed-edge-robdd-v1", "terminal": {"1": True, "-1": False},
            "node_ids": "array index + 2", "node_format": ["variable level", "false branch edge", "true branch edge"],
            "edge_semantics": "negative edge complements its absolute target node",
            "variable_order": sorted(variables.values(), key=bdd.level_of_var),
            "statement_by_variable": {v: s for s, v in variables.items()}, "roots": entries, "nodes": nodes}
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
    temporary.replace(path)
    return {"path": str(path), "node_count": len(nodes), "bytes": path.stat().st_size,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def compare_baseline(report, baseline):
    if report["basis"] != baseline.get("basis"):
        return {"status": "incomparable", "reason": "Different input bases"}
    targets = {}
    for target, current in report["targets"].items():
        old = baseline.get("targets", {}).get(target)
        if not old or old.get("minimal_support_count") is None:
            targets[target] = {"status": "no_baseline_target"}
            continue
        changes = {"status": "compared", "minimal_support_count_delta": str(
            int(current["minimal_support_count"]) - int(old["minimal_support_count"]))}
        for key in ("minimum_premise_count", "maximum_minimal_premise_count"):
            if current.get(key) is not None and old.get(key) is not None:
                changes[key + "_delta"] = current[key] - old[key]
        before, after = set(old.get("mandatory_statement_ids", [])), set(current["mandatory_statement_ids"])
        changes["mandatory_inputs_added"] = sorted(after - before)
        changes["mandatory_inputs_removed"] = sorted(before - after)
        targets[target] = changes
    return {"status": "compared", "source_head": baseline.get("source_head"), "targets": targets,
            "scope": "Descriptive changes in premise combinations, not an evidence-weight or philosophical-strength score."}


def calculate(graph, *, basis="terminal", memory_mib=2048, histogram_node_limit=60000, bdd_output=None):
    start = time.perf_counter()
    statements, terminals = validate_graph(graph)
    bdd, roots, variables, fixed_point = solve_graph(graph, basis, memory_mib)
    validation = check_closure(bdd, roots, variables, graph, basis)
    report = {"schema_version": 1, "status": "complete", "basis": basis,
              "source_head": graph.get("source_head"), "worktree_dirty": graph.get("worktree_dirty"),
              "input_identity": graph.get("input_identity"), "graph_sha256": graph.get("graph_sha256"),
              "analysis_graph_sha256": graph_digest(graph),
              "scope": "Exact minimal input sets deriving the target in the registered statement-ID graph; not new Lean composition, premise truth, or independent evidence counts.",
              "semantics": {"input_false": "premise not supplied; not its negation",
                            "cycles": "least fixed point", "target_direct_input": "excluded separately for each target",
                            "status_as_fact": False, "transcriptions": "included",
                            "terminal_basis": "statements with no incoming result-backed rule",
                            "direct_or_derived_formula": "The exported graph retains a direct-input OR derivations option for every non-target statement."},
              "graph": {"statement_count": len(statements), "rule_count": len(graph["rules"]),
                        "result_count": graph.get("result_count"), "terminal_statement_count": len(terminals)},
              "direct": graph.get("direct", {}),
              "fixed_point": fixed_point, "validation": validation, "targets": {},
              "dependencies": {"dd": dd.__version__, "dd_backend": "autoref" if cudd is None else "cudd",
                               "networkx": nx.__version__}}
    for target in graph["target_statement_ids"]:
        formula = roots[target]
        support = bdd.support(formula)
        mandatory = sorted(s for s, variable in variables.items()
                           if variable in support and bdd.let({variable: False}, formula) == bdd.false)
        bdd.configure(reordering=True)
        minimal = minimal_models(bdd, formula, sorted(variables.values(), key=bdd.level_of_var))
        bdd.configure(reordering=False)
        if minimal_by_shannon(bdd, formula) != minimal:
            raise RuntimeError(f"Independent minimal-family algorithms disagree for {target}")
        count = exact_count(bdd, minimal)
        minimum, maximum = minmax_size(bdd, minimal)
        histogram = exact_histogram(bdd, minimal, histogram_node_limit)
        if histogram is not None and sum(histogram.values()) != count:
            raise RuntimeError(f"Count and size histogram disagree for {target}")
        roots[target + "_minimal"] = minimal
        report["targets"][target] = {
            "label": statements[target].get("label", target), "status": "exact",
            "minimal_support_count": str(count), "minimum_premise_count": minimum,
            "maximum_minimal_premise_count": maximum, "mandatory_statement_ids": mandatory,
            "formula_support_variables": len(bdd.support(formula)), "formula_nodes": formula.dag_size,
            "minimal_bdd_nodes": minimal.dag_size,
            "histogram_status": "complete" if histogram is not None else "unavailable_node_limit",
            "size_histogram": {str(k): str(v) for k, v in histogram.items()} if histogram is not None else None,
            "independent_shannon_minimization_agrees": True,
            "representative_supports": representative_supports(bdd, minimal, variables, target, graph["rules"])}
        progress("target_complete", target=target, minimal_support_count=str(count), minimum=minimum, maximum=maximum)
    if bdd_output:
        report["exact_bdd"] = export_bdds(bdd, roots, variables, bdd_output)
    report["seconds"] = round(time.perf_counter() - start, 3)
    gc.collect()
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("statements", nargs="*", help="Target IDs/aliases; default God existence and necessary classical root")
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--truth", type=Path, help="Prebuilt Rust CLI; otherwise use scripts/truth_cli.py")
    parser.add_argument("--graph", type=Path, help="Replay an exported support-graph JSON")
    parser.add_argument("--output", type=Path, default=ROOT / "target/support-formula/report.json")
    parser.add_argument("--graph-output", type=Path, help="Save the exact graph, including direct-or-derived options")
    parser.add_argument("--bdd-output", type=Path, help="Save every conjunction as an exact decision diagram")
    parser.add_argument("--baseline", type=Path, help="Compare a prior report with the same input basis")
    parser.add_argument("--basis", choices=("terminal", "direct-or-derived"), default="terminal")
    parser.add_argument("--memory-mib", type=int, default=2048)
    parser.add_argument("--histogram-node-limit", type=int, default=60000,
                        help="Skip only the size histogram above this BDD size; counts remain exact")
    parser.add_argument("--export-timeout", type=float, default=600)
    parser.add_argument("--self-test", action="store_true", help="Run the small exhaustive oracle tests without corpus calculation")
    args = parser.parse_args(argv)
    if args.self_test:
        suite = unittest.defaultTestLoader.discover(str(Path(__file__).parent), pattern="test_support_formula.py")
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    if args.memory_mib <= 0 or args.histogram_node_limit < 0 or args.export_timeout <= 0:
        parser.error("Memory and timeout must be positive; histogram node limit cannot be negative")
    if args.graph_output is None and args.graph is None:
        args.graph_output = args.output.with_name(args.output.stem + "-graph.json")
    outputs = [p.resolve() for p in (args.output, args.graph_output, args.bdd_output) if p]
    inputs = {p.resolve() for p in (args.graph, args.baseline) if p}
    if len(outputs) != len(set(outputs)) or inputs.intersection(outputs):
        parser.error("Input and output paths must be distinct")
    try:
        write_json(args.output, {"schema_version": 1, "status": "incomplete", "basis": args.basis})
        graph = load_graph(args)
        if args.graph_output:
            write_json(args.graph_output, graph)
        write_json(args.output, {"schema_version": 1, "status": "incomplete", "basis": args.basis,
                                 "source_head": graph.get("source_head"), "graph_sha256": graph.get("graph_sha256"),
                                 "analysis_graph_sha256": graph_digest(graph)})
        report = calculate(graph, basis=args.basis, memory_mib=args.memory_mib,
                           histogram_node_limit=args.histogram_node_limit, bdd_output=args.bdd_output)
        report["graph_artifact"] = str(args.graph_output or args.graph)
        if args.baseline:
            report["baseline_comparison"] = compare_baseline(report, json.loads(args.baseline.read_text(encoding="utf-8")))
        write_json(args.output, report)
    except (OSError, ValueError, RuntimeError, MemoryError, subprocess.TimeoutExpired) as error:
        print(f"support formula: {error}", file=sys.stderr)
        return 1
    print(f"Exact {report['basis']} support combinations ({report['source_head'] or 'exported graph'}):")
    for target in report["targets"].values():
        print(f"  {target['label']}: {int(target['minimal_support_count']):,}; "
              f"size {target['minimum_premise_count']}–{target['maximum_minimal_premise_count']}; "
              f"{len(target['mandatory_statement_ids'])} shared inputs")
    print(f"Report: {args.output} ({report['seconds']:.3f}s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
