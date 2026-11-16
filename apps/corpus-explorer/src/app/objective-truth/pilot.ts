import { readdirSync, readFileSync } from "node:fs";
import path from "node:path";

import { legacyUuid } from "@/lib/corpus-ids";
import { repositoryRoot, truthJson } from "@/lib/truth-cli";

const statementIds = (...legacyIds: string[]) => legacyIds.map((id) => legacyUuid("statement", id));

/** A reading guide over canonical IDs, never another proposition or status store. */
export const PILOT_GROUPS = [
  {
    title: "The two logical propositions",
    scope: "These exact Lean propositions have premise-free proofs. They do not by themselves say that truth is independent of minds or endorsement.",
    statementIds: statementIds("STMT-SOME-LEAN-PROPOSITION-HOLDS", "STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS"),
  },
  {
    title: "Interpretation bridges still to defend",
    scope: "A logical proof does not supply an interpretation of ordinary truth or of expressed negation. The verified conditional tests retain these open premises.",
    statementIds: statementIds("STMT-PILOT-LOGICAL-SENTENCE-STABLE", "STMT-PILOT-NEGATION-RESPECTED"),
  },
  {
    title: "Distinct readings of relativity",
    scope: "Global variation, local variation, an unindexed all-opinions-true thesis, and an epistemic limitation are different readings. Their identities remain separate.",
    statementIds: statementIds("STMT-PILOT-GLOBAL-PROFILE-VARIATION", "STMT-PILOT-LOCAL-PROFILE-VARIATION", "STMT-ALL-OPINIONS-TRUE-UNINDEXED", "STMT-PILOT-OPPOSED-OPINIONS", "STMT-PILOT-CONFLICTING-OPINIONS", "STMT-ARIST-DEMOCRITUS-NO-TRUTH-OR-UNKNOWN"),
  },
  {
    title: "What the tests establish",
    scope: "These are conditional consequences or models of the stated encoding. They do not establish a full worldview, source fidelity, or an unconditional self-refutation of relativism.",
    statementIds: statementIds("STMT-PILOT-NOT-GLOBAL-PROFILE-VARIATION", "STMT-PILOT-NOT-ALL-OPINIONS-TRUE", "STMT-PILOT-LOCAL-VARIATION-COMPATIBLE", "STMT-PILOT-GLOBAL-VARIATION-MODEL", "STMT-PILOT-EPISTEMIC-DIFFERENCES-MODEL"),
  },
] satisfies Array<{ title: string; scope: string; statementIds: string[] }>;

export function pilotGraphHref(statementId: string) {
  const params = new URLSearchParams({
    view: "focus", node: statementId, sel: statementId,
    scope: "goal", target: statementId, cluster: "namespace",
  });
  return `/graph?${params}`;
}

export type PilotScenario = { id: string; established: string[]; verifiedResults: number };
let cachedScenarios: PilotScenario[] | undefined;

type PilotFixture = { statement_ids: string[]; argument_ids: string[]; cases: { id: string; result_ids: string[] }[] };

/** Records of `kind` (a corpus directory) whose id is listed, in file order. */
function selected(kind: string, ids: string[]): unknown[] {
  const directory = path.join(repositoryRoot, "corpus", kind);
  return readdirSync(directory).filter((file) => file.endsWith(".json")).sort()
    .map((file): unknown => JSON.parse(readFileSync(path.join(directory, file), "utf8")))
    .filter((record) => typeof record === "object" && record !== null && "id" in record &&
      typeof record.id === "string" && ids.includes(record.id));
}

/** Reuse the CLI's authoritative frontier (`truth frontier --fixture`, #954 B12) with explicit verifier-record subsets.
 * Removing a record simulates unavailable grounding; it does not undo a theorem. */
export function getPilotScenarios(): PilotScenario[] {
  if (!cachedScenarios) {
    const fixture = JSON.parse(readFileSync(path.join(repositoryRoot, "scripts/testdata/objective-truth-pilot.json"), "utf8")) as PilotFixture;
    const statements = selected("statements", fixture.statement_ids);
    const argumentRecords = selected("arguments", fixture.argument_ids);
    const raw: unknown = fixture.cases.map((pilotCase) => {
      const results = selected("results", pilotCase.result_ids);
      const report = truthJson(
        ["frontier", "--fixture", "-", "--frontier-root", fixture.statement_ids[0]],
        JSON.stringify({ statements, arguments: argumentRecords, results }),
      ) as { established_statements: unknown };
      return { id: pilotCase.id, established: report.established_statements, verifiedResults: results.length };
    });
    if (!Array.isArray(raw)) {
      throw new Error("Invalid pilot scenario report");
    }
    cachedScenarios = raw.map((item: unknown) => {
      if (typeof item !== "object" || item === null || !("id" in item) || typeof item.id !== "string" ||
          !("established" in item) || !Array.isArray(item.established) ||
          !item.established.every((id: unknown) => typeof id === "string") ||
          !("verifiedResults" in item) || typeof item.verifiedResults !== "number") {
        throw new Error("Invalid pilot scenario record");
      }
      return { id: item.id, established: item.established, verifiedResults: item.verifiedResults };
    });
  }
  return cachedScenarios;
}
