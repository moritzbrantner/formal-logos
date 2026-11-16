import {
  buildPropositionGraph,
  type PropositionGraphInput,
} from "./proposition-graph";
import type { FrontierReport } from "./site-state";
import { truthJson } from "./truth-cli";

/** A fixture corpus plus the results that the Lean heuristics would flag as transcriptions. */
export type GraphFixtureInput = PropositionGraphInput & { transcriptionResultIds: string[] };

/**
 * Tests exercise the CLI's actual closure semantics, never a second JS
 * solver: `truth frontier --fixture -` computes the frontier report of the
 * fixture records with the given transcription flags (#954 B12).
 */
export function fixtureReport(input: GraphFixtureInput): FrontierReport {
  const fixture = {
    statements: input.statements,
    arguments: input.arguments,
    results: input.results,
    relations: input.relations,
    claims: input.claims,
    inferences: input.inferences,
    transcription_flags: input.results
      .filter((result) => input.transcriptionResultIds.includes(result.id))
      .map((result) => ({
        result_id: result.id,
        argument_id: result.argument_id,
        proof_steps: 1,
        single_application_of: "fixture",
        goal_consequent_premises: [],
      })),
  };
  const report = truthJson(
    ["frontier", "--fixture", "-", "--frontier-root", "ROOT"],
    JSON.stringify(fixture),
  ) as FrontierReport & { input_identity?: string };
  delete report.input_identity;
  return report;
}

export function fixtureGraph(input: GraphFixtureInput) {
  return buildPropositionGraph(input, fixtureReport(input));
}
