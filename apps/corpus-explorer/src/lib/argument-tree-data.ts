import fs from "node:fs";
import os from "node:os";
import path from "node:path";

import { parseArgumentTree, type ArgumentTree } from "./argument-tree";
import { getCorpus } from "./corpus";
import { DEFAULT_ROOT_STATEMENT_ID } from "./proposition-graph";
import { getFrontierReport } from "./site-state";
import { truthJson } from "./truth-cli";

/**
 * Bounded options of the prebuilt trees. A tree of every statement at the CLI
 * defaults (budget 400) is 654 MB of JSON and at budget 60 still 202 MB, so
 * the static site prebuilds only the case root and its route nodes and asks
 * for `truth tree X` locally otherwise (docs/github-pages.md, "Re-rooted
 * argument trees").
 */
export const STATIC_TREE_OPTIONS = { down: 3, up: 3, budget: 80 } as const;

/**
 * The statements whose trees the static site carries: the case root, the
 * premises of every argument concluding it and each route's open leaves.
 */
export function staticTreeIds(): string[] {
  const report = getFrontierReport(DEFAULT_ROOT_STATEMENT_ID);
  const corpus = getCorpus();
  const ids = new Set([DEFAULT_ROOT_STATEMENT_ID]);
  for (const route of report.routes.routes) {
    const argument = corpus.arguments.find((entry) => entry.id === route.argument_id);
    for (const premise of argument?.premise_statement_ids ?? []) ids.add(premise);
    for (const premise of route.open_premise_statement_ids) ids.add(premise);
  }
  return [...ids].sort();
}

let cached: Map<string, ArgumentTree> | undefined;

/** One `truth tree --out-dir` batch per build process, read back and shape-checked. */
export function getStaticTrees(): Map<string, ArgumentTree> {
  if (!cached) {
    const ids = staticTreeIds();
    const directory = fs.mkdtempSync(path.join(os.tmpdir(), "truth-tree-"));
    try {
      truthJson([
        "tree", "--out-dir", directory,
        "--down", String(STATIC_TREE_OPTIONS.down),
        "--up", String(STATIC_TREE_OPTIONS.up),
        "--budget", String(STATIC_TREE_OPTIONS.budget),
        ...ids,
      ]);
      cached = new Map(ids.map((id) => [id, parseArgumentTree(JSON.parse(fs.readFileSync(path.join(directory, `${id}.json`), "utf8")))]));
    } finally {
      fs.rmSync(directory, { recursive: true, force: true });
    }
  }
  return cached;
}
