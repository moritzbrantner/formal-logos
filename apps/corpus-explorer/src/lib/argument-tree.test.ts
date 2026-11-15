import { describe, expect, test } from "bun:test";

import {
  alternativesByConclusion,
  argumentKind,
  formalStatusLabel,
  layoutTree,
  parseArgumentTree,
  statusKind,
  treeHref,
  treeRanks,
  type ArgumentTree,
  type TreeArgument,
  type TreeStatement,
} from "./argument-tree";
import { DEFAULT_ROOT_STATEMENT_ID } from "./proposition-graph";
import { truthJson } from "./truth-cli";

function statement(id: string, role: TreeStatement["role"], down: number | null, up: number | null, extra: Partial<TreeStatement> = {}): TreeStatement {
  return {
    id, label: `${id} label`, legacy_id: null, lean_declaration: null, role, down_depth: down, up_depth: up,
    status: "open", depth: "bare", closed: null, established: false, reaches_tree_root: true, is_case_root: false,
    definition_ids: [], disambiguation_ids: [], senses: [], ...extra,
  };
}

function argument(id: string, side: "down" | "up", conclusion: string, premises: string[], extra: Partial<TreeArgument> = {}): TreeArgument {
  return {
    id, label: id, sides: [side], up_from: side === "up" ? [premises[0]] : [], conclusion_statement_id: conclusion,
    premise_statement_ids: premises, steps: [], results: [], verified: false, route: null, ...extra,
  };
}

function edge(kind: string, from: string, to: string, argumentId: string | null, cycle = false) {
  return { kind, from, to, argument_id: argumentId, relation_id: null, result_id: null, extra_premises: [], verified: true, derivation: null, cycle };
}

// X has two alternative arguments (A1 from P, Q; A2 from R), is used by U1
// (with co-premise C) toward Y, and P strengthens to S.
const fixture: ArgumentTree = {
  schema_version: 1, root: "X", case_root: "Y", options: { down: 3, up: 3, budget: 400 }, edge_kinds: ["supports", "uses", "strengthens"],
  statements: [
    statement("X", "root", 0, 0, { closed: "proved", depth: "stated" }),
    statement("P", "support", 1, null, { established: true, closed: "proved" }),
    statement("Q", "support", 1, null),
    statement("R", "support", 1, null, { depth: "supported" }),
    statement("Y", "dependent", null, 1, { is_case_root: true }),
    statement("C", "co_premise", null, null),
    statement("S", "strength_neighbor", null, null),
  ],
  arguments: [
    argument("A1", "down", "X", ["P", "Q"], { results: [{ id: "R1", theorem: "t", status: "solution-present", transcription: null }], verified: true }),
    argument("A2", "down", "X", ["R"], { results: [{ id: "R2", theorem: "t", status: "solution-present", transcription: "assembly" }], verified: true }),
    argument("U1", "up", "Y", ["X", "C"]),
  ],
  edges: [
    edge("supports", "A1", "X", "A1"), edge("uses", "A1", "P", "A1"), edge("uses", "A1", "Q", "A1"),
    edge("supports", "A2", "X", "A2"), edge("uses", "A2", "R", "A2"),
    edge("uses", "U1", "X", "U1"), edge("uses", "U1", "C", "U1"), edge("supports", "U1", "Y", "U1"),
    edge("strengthens", "P", "S", null),
  ],
  definitions: [], disambiguations: [],
  truncated: [{ statement_id: "Q", side: "down", reason: "depth", omitted_arguments: 2 }],
  node_count: 10,
};

describe("re-rooted argument tree view", () => {
  test("accepts the CLI shape and rejects a tree without its root node", () => {
    expect(parseArgumentTree(fixture).root).toBe("X");
    expect(() => parseArgumentTree({ ...fixture, statements: fixture.statements.slice(1) })).toThrow("no root node");
    expect(() => parseArgumentTree({ ...fixture, schema_version: 3 })).toThrow();
    const derived = { kind: "contrapositive", from: "X", to: "Y", argument_id: null, relation_id: null, result_id: null, extra_premises: [], verified: false, derivation: null, cycle: false };
    const v2 = parseArgumentTree({ ...fixture, schema_version: 2, edges: [...fixture.edges, derived] });
    expect(v2.edges.some((edge) => edge.kind === "contrapositive")).toBe(false);
    expect(v2.derived_edges).toHaveLength(1);
  });

  test("puts support below and dependents above, co-premises and strength neighbours beside their partners", () => {
    const ranks = treeRanks(fixture);
    expect(ranks.statements.get("X")).toBe(0);
    expect(ranks.arguments.get("A1")).toBe(1);
    expect(ranks.statements.get("P")).toBe(2);
    expect(ranks.arguments.get("U1")).toBe(-1);
    expect(ranks.statements.get("Y")).toBe(-2);
    expect(ranks.statements.get("C")).toBe(0);
    expect(ranks.statements.get("S")).toBe(2);
  });

  test("lays nodes out without overlap, root row between dependents and support", () => {
    const layout = layoutTree(fixture);
    expect(layout.nodes).toHaveLength(fixture.statements.length + fixture.arguments.length);
    const y = (id: string) => layout.byId.get(id)!.y;
    expect(y("Y")).toBeLessThan(y("U1"));
    expect(y("U1")).toBeLessThan(y("X"));
    expect(y("X")).toBeLessThan(y("A1"));
    expect(y("A1")).toBeLessThan(y("P"));
    for (const a of layout.nodes) for (const b of layout.nodes) {
      if (a === b) continue;
      const apart = a.x + a.width <= b.x || b.x + b.width <= a.x || a.y + a.height <= b.y || b.y + b.height <= a.y;
      expect(apart).toBe(true);
    }
  });

  test("classifies statuses, OR alternatives and transcriptions from CLI fields only", () => {
    const byId = new Map(fixture.statements.map((entry) => [entry.id, entry]));
    expect(statusKind(byId.get("P")!)).toBe("established");
    expect(statusKind(byId.get("X")!)).toBe("closed");
    expect(statusKind(byId.get("R")!)).toBe("open");
    expect(statusKind(byId.get("Q")!)).toBe("bare");
    expect(alternativesByConclusion(fixture).get("X")).toEqual(["A1", "A2"]);
    expect(argumentKind(fixture.arguments[0])).toBe("verified");
    expect(argumentKind(fixture.arguments[1])).toBe("transcription");
    expect(argumentKind(fixture.arguments[2])).toBe("unverified");
    expect(treeHref("a b")).toBe("/tree?id=a%20b");
  });

  test("shows the formal status before and after the lexicon data exists (#1673)", () => {
    expect(formalStatusLabel({ lean_declaration: null, formal_status: null })).toBe("no Lean");
    expect(formalStatusLabel({ lean_declaration: "T.D", formal_status: null })).toBe("formal status not yet computed");
    expect(formalStatusLabel({ lean_declaration: "T.D", formal_status: { status: "defined" } })).toBe("Lean definition");
    expect(formalStatusLabel({ lean_declaration: "T.D", formal_status: { status: "primitive", formal_gap: { kind: "primitive" } } })).toBe("primitive + prose");
    expect(formalStatusLabel({ lean_declaration: "T.D", formal_status: "primitive" })).toBe("primitive (no prose yet)");
  });

  test("renders the real case-root tree from the CLI", () => {
    const tree = parseArgumentTree(truthJson(["tree", DEFAULT_ROOT_STATEMENT_ID, "--budget", "80"]));
    const layout = layoutTree(tree);
    expect(layout.nodes.length).toBe(tree.statements.length + tree.arguments.length);
    expect(tree.truncated.length).toBeGreaterThan(0);
    expect(tree.definitions.length).toBeGreaterThan(0);
  }, 30000);
});
