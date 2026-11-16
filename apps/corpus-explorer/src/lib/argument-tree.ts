/**
 * The re-rooted argument tree (#1674): types for `truth --json tree X`
 * (truth/README.md, `tree`), a shape check, and a deterministic layered
 * layout. The explorer only renders this CLI JSON; statuses, closure,
 * truncation and cycles come from the CLI and are never recomputed here.
 */

export type TreeSenseUse = {
  disambiguation_id: string;
  sense_id: string | null;
  sense_label: string | null;
  lean_declaration: string | null;
};

export type TreeStatement = {
  id: string;
  label: string | null;
  legacy_id: string | null;
  lean_declaration: string | null;
  role: "root" | "support" | "dependent" | "co_premise" | "strength_neighbor";
  down_depth: number | null;
  up_depth: number | null;
  status: unknown;
  depth: unknown;
  closed: string | null;
  established: boolean;
  reaches_tree_root: boolean;
  is_case_root: boolean;
  definition_ids: string[];
  disambiguation_ids: string[];
  senses: TreeSenseUse[];
};

export type TreeArgument = {
  id: string;
  label: string | null;
  sides: Array<"down" | "up">;
  up_from: string[];
  conclusion_statement_id: string;
  premise_statement_ids: string[];
  steps: Array<{ id: string; label: string | null; rule: string | null; input_statement_ids: string[]; output_statement_id: string | null }>;
  results: Array<{ id: string; theorem: string | null; status: string | null; transcription: string | null }>;
  verified: boolean;
  route: { cost: number; cheapest: boolean; open_premise_statement_ids: string[] } | null;
};

export type TreeEdge = {
  kind: string;
  from: string;
  to: string;
  argument_id: string | null;
  relation_id: string | null;
  result_id: string | null;
  extra_premises: string[];
  verified: boolean;
  derivation: string | null;
  cycle: boolean;
};

export type TreeDefinition = {
  id: string;
  label: string | null;
  term: string | null;
  basis: string | null;
  lean_declaration: string | null;
  senses: TreeSenseUse[];
  /** Lean-computed formal status (#1652 L3, #1673); `null` until that data exists. */
  formal_status: unknown;
  used_by: string[];
};

export type TreeDisambiguation = {
  id: string;
  label: string | null;
  term_label: string | null;
  senses: Array<{ id?: string; label?: string; definition_id?: string; lean_declaration?: string }>;
  used_by: string[];
};

export type TreeTruncation = {
  statement_id: string;
  side: "down" | "up";
  reason: "depth" | "budget";
  omitted_arguments: number;
};

export type ArgumentTree = {
  schema_version: number;
  root: string;
  case_root: string;
  options: { down: number; up: number; budget: number };
  edge_kinds: string[];
  statements: TreeStatement[];
  arguments: TreeArgument[];
  edges: TreeEdge[];
  definitions: TreeDefinition[];
  disambiguations: TreeDisambiguation[];
  truncated: TreeTruncation[];
  node_count: number;
  /** Derived inversion edges (schema 2), kept out of the drawn graph. */
  derived_edges?: TreeEdge[];
};

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

/** Tree JSON versions this view reads (`truth tree`): 2 adds derived inversion edges. */
export const SCHEMA_VERSIONS = [1, 2];
/** Edges between records; the others (`contrapositive`, `inverse_conditional`) are derived. */
export const RECORD_EDGE_KINDS = ["supports", "uses", "strengthens"];

/** Check the transport shape of one tree file; references are the CLI's job. */
export function parseArgumentTree(value: unknown): ArgumentTree {
  if (!isObject(value) || !SCHEMA_VERSIONS.includes(value.schema_version as number) || typeof value.root !== "string") {
    throw new Error(`Tree report must be a schema_version ${SCHEMA_VERSIONS.join(" or ")} object with a root`);
  }
  for (const field of ["statements", "arguments", "edges", "definitions", "disambiguations", "truncated"]) {
    if (!Array.isArray(value[field])) throw new Error(`Tree report lacks ${field}`);
  }
  const tree = value as unknown as ArgumentTree;
  // Schema 2 adds derived inversion edges (#1674 phase 2). They connect no new
  // nodes and the graph draws record edges only; derived edges are counted.
  tree.derived_edges = tree.edges.filter((edge) => !RECORD_EDGE_KINDS.includes(edge.kind));
  tree.edges = tree.edges.filter((edge) => RECORD_EDGE_KINDS.includes(edge.kind));
  if (!tree.statements.some((statement) => statement.id === tree.root && statement.role === "root")) {
    throw new Error(`Tree report has no root node ${tree.root}`);
  }
  return tree;
}

/** The URL of a statement's re-rooted tree. */
export function treeHref(statementId: string) {
  return `/tree?id=${encodeURIComponent(statementId)}`;
}

export type StatusKind = "established" | "closed" | "open" | "bare";

/** Display class of a statement, from the CLI's frontier fields only. */
export function statusKind(statement: TreeStatement): StatusKind {
  if (statement.established) return "established";
  if (statement.closed) return "closed";
  return statement.depth === "bare" ? "bare" : "open";
}

export function statusLabel(statement: TreeStatement): string {
  const kind = statusKind(statement);
  if (kind === "established") return statement.closed ? `established · ${statement.closed.replaceAll("_", " ")}` : "established";
  if (kind === "closed") return `closed · ${statement.closed!.replaceAll("_", " ")}`;
  return kind === "bare" ? "open · bare" : `open · ${typeof statement.depth === "string" ? statement.depth : "unknown depth"}`;
}

export type ArgumentKind = "verified" | "transcription" | "unverified";

/** Verified non-transcription, transcription-only, or without a result. */
export function argumentKind(argument: TreeArgument): ArgumentKind {
  if (!argument.results.length) return "unverified";
  return argument.results.every((result) => result.transcription) ? "transcription" : "verified";
}

/**
 * The definition's formal status for display (#1673). The field is `null`
 * until the lexicon's formal-status data exists; then a `defined` status reads
 * as a Lean definition and the other statuses as primitives with or without
 * their prose boundary.
 */
export function formalStatusLabel(definition: Pick<TreeDefinition, "lean_declaration" | "formal_status">): string {
  if (!definition.lean_declaration) return "no Lean";
  const value = definition.formal_status;
  if (value === null || value === undefined) return "formal status not yet computed";
  const record = isObject(value) ? value : {};
  const status = typeof value === "string" ? value : String(record.status ?? record.kind ?? "");
  if (status === "defined") return "Lean definition";
  if (status === "primitive" || status === "constraint" || status === "unresolved") {
    const prose = record.formal_gap ?? record.prose ?? record.has_prose;
    return prose ? `${status} + prose` : `${status} (no prose yet)`;
  }
  return status || "formal status recorded";
}

export type LayoutNode = {
  kind: "statement" | "argument";
  id: string;
  rank: number;
  x: number;
  y: number;
  width: number;
  height: number;
};

export type TreeLayout = {
  nodes: LayoutNode[];
  byId: Map<string, LayoutNode>;
  width: number;
  height: number;
};

export const LAYOUT = {
  column: 236,
  statementWidth: 216,
  statementHeight: 104,
  argumentWidth: 200,
  argumentHeight: 92,
  gap: 34,
  maxColumns: 6,
  padding: 16,
};

/**
 * Ranks: the root at 0, support below (statements at 2d, the arguments
 * concluding them at 2d + 1), dependents above (statements at -2u, the
 * arguments using them at -2u - 1). Co-premises share the row of the premise
 * the upward walk came from; strength neighbours share their partner's row.
 */
export function treeRanks(tree: ArgumentTree): { statements: Map<string, number>; arguments: Map<string, number> } {
  const statements = new Map<string, number>();
  for (const statement of tree.statements) {
    if (statement.role === "root") statements.set(statement.id, 0);
    else if (statement.role === "support" && statement.down_depth !== null) statements.set(statement.id, 2 * statement.down_depth);
    else if (statement.role === "dependent" && statement.up_depth !== null) statements.set(statement.id, -2 * statement.up_depth);
  }
  const argumentRanks = new Map<string, number>();
  const rankOf = (id: string) => statements.get(id);
  for (const argument of tree.arguments) {
    if (argument.sides.includes("down") && rankOf(argument.conclusion_statement_id) !== undefined) {
      argumentRanks.set(argument.id, rankOf(argument.conclusion_statement_id)! + 1);
    } else {
      const from = argument.up_from.map(rankOf).filter((rank): rank is number => rank !== undefined);
      if (from.length) argumentRanks.set(argument.id, Math.min(...from) - 1);
    }
  }
  for (const argument of tree.arguments) {
    const rank = argumentRanks.get(argument.id);
    if (rank === undefined || !argument.sides.includes("up")) continue;
    for (const premise of argument.premise_statement_ids) {
      if (!statements.has(premise)) statements.set(premise, rank + 1);
    }
  }
  for (const edge of tree.edges) {
    if (edge.kind !== "strengthens") continue;
    for (const [node, partner] of [[edge.from, edge.to], [edge.to, edge.from]]) {
      if (!statements.has(node) && statements.has(partner)) statements.set(node, statements.get(partner)!);
    }
  }
  for (const statement of tree.statements) {
    if (!statements.has(statement.id)) {
      statements.set(statement.id, statement.down_depth !== null ? 2 * statement.down_depth : statement.up_depth !== null ? -2 * statement.up_depth : 0);
    }
  }
  for (const argument of tree.arguments) {
    if (!argumentRanks.has(argument.id)) argumentRanks.set(argument.id, (statements.get(argument.conclusion_statement_id) ?? 0) + 1);
  }
  return { statements, arguments: argumentRanks };
}

/**
 * A deterministic layered layout. Rows are ordered outward from the root by the
 * mean column of their already placed neighbours, and wrap after
 * `LAYOUT.maxColumns` nodes so a wide argument stays readable.
 */
export function layoutTree(tree: ArgumentTree): TreeLayout {
  const ranks = treeRanks(tree);
  const rows = new Map<number, Array<{ kind: "statement" | "argument"; id: string }>>();
  const push = (rank: number, kind: "statement" | "argument", id: string) => {
    const row = rows.get(rank) ?? [];
    row.push({ kind, id });
    rows.set(rank, row);
  };
  for (const statement of tree.statements) push(ranks.statements.get(statement.id)!, "statement", statement.id);
  for (const argument of tree.arguments) push(ranks.arguments.get(argument.id)!, "argument", argument.id);

  const neighbours = new Map<string, string[]>();
  const link = (a: string, b: string) => {
    neighbours.set(a, [...(neighbours.get(a) ?? []), b]);
    neighbours.set(b, [...(neighbours.get(b) ?? []), a]);
  };
  for (const edge of tree.edges) link(edge.from, edge.to);

  const order = [...rows.keys()].sort((a, b) => Math.abs(a) - Math.abs(b) || a - b);
  const column = new Map<string, number>();
  for (const rank of order) {
    const row = rows.get(rank)!;
    const inward = rank === 0 ? 0 : rank > 0 ? rank - 1 : rank + 1;
    const keyed = row.map((entry, index) => {
      const placed = (neighbours.get(entry.id) ?? [])
        .filter((other) => column.has(other) && (rows.get(inward)?.some((item) => item.id === other) ?? false))
        .map((other) => column.get(other)!);
      const key = placed.length ? placed.reduce((sum, value) => sum + value, 0) / placed.length : Number.POSITIVE_INFINITY;
      return { entry, key, index };
    });
    keyed.sort((a, b) => a.key - b.key || a.index - b.index);
    const width = Math.min(row.length, LAYOUT.maxColumns);
    keyed.forEach(({ entry }, index) => column.set(entry.id, (index % LAYOUT.maxColumns) - (width - 1) / 2));
    rows.set(rank, keyed.map(({ entry }) => entry));
  }

  const columns = Math.max(1, ...[...rows.values()].map((row) => Math.min(row.length, LAYOUT.maxColumns)));
  const width = columns * LAYOUT.column + 2 * LAYOUT.padding;
  const nodes: LayoutNode[] = [];
  let y = LAYOUT.padding;
  for (const rank of [...rows.keys()].sort((a, b) => a - b)) {
    const row = rows.get(rank)!;
    for (let start = 0; start < row.length; start += LAYOUT.maxColumns) {
      const chunk = row.slice(start, start + LAYOUT.maxColumns);
      const statementRow = chunk.some((entry) => entry.kind === "statement");
      const height = statementRow ? LAYOUT.statementHeight : LAYOUT.argumentHeight;
      const offset = (width - chunk.length * LAYOUT.column) / 2;
      chunk.forEach((entry, index) => {
        const nodeWidth = entry.kind === "statement" ? LAYOUT.statementWidth : LAYOUT.argumentWidth;
        nodes.push({
          kind: entry.kind,
          id: entry.id,
          rank,
          x: offset + index * LAYOUT.column + (LAYOUT.column - nodeWidth) / 2,
          y: y + (height - (entry.kind === "statement" ? LAYOUT.statementHeight : LAYOUT.argumentHeight)) / 2,
          width: nodeWidth,
          height: entry.kind === "statement" ? LAYOUT.statementHeight : LAYOUT.argumentHeight,
        });
      });
      y += height + LAYOUT.gap;
    }
  }
  return { nodes, byId: new Map(nodes.map((node) => [node.id, node])), width, height: y - LAYOUT.gap + LAYOUT.padding };
}

/** The OR alternatives concluding each statement on the support side. */
export function alternativesByConclusion(tree: ArgumentTree): Map<string, string[]> {
  const map = new Map<string, string[]>();
  for (const argument of tree.arguments) {
    if (!argument.sides.includes("down")) continue;
    map.set(argument.conclusion_statement_id, [...(map.get(argument.conclusion_statement_id) ?? []), argument.id]);
  }
  return map;
}
