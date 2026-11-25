import { record } from "@/lib/current-judgments";
import { truthJson } from "@/lib/truth-cli";

type Input = {
  id: string;
  label: string | null;
  paraphrase: string;
  role: "premise" | "commitment";
};

type Result = {
  id: string;
  theorem: string;
  challenge_path: string | null;
  solution_path: string | null;
  advertised_statement: { statement: string; line: number } | null;
};

export type Comparison = {
  withheld: string[];
  reachable: boolean;
  selected_applicable: boolean;
  missing_selected_inputs: string[];
  recovered_inputs: string[];
  supporting_arguments: string[];
  derivation: string[];
};

type ArgumentSynthesis = Comparison & {
  mode: "argument";
  scope: string;
  argument: {
    argument_id: string;
    conclusion_statement_id: string;
    label: string;
    meaning: string;
  };
  inputs: Input[];
  results: Result[];
  comparisons: Comparison[];
};

function strings(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((entry) => typeof entry === "string");
}

function input(value: unknown): value is Input {
  return record(value) && typeof value.id === "string" && (typeof value.label === "string" || value.label === null)
    && typeof value.paraphrase === "string" && (value.role === "premise" || value.role === "commitment");
}

function result(value: unknown): value is Result {
  if (!record(value) || typeof value.id !== "string" || typeof value.theorem !== "string") {
    return false;
  }
  const advertised = value.advertised_statement;
  return (value.challenge_path === null || typeof value.challenge_path === "string")
    && (value.solution_path === null || typeof value.solution_path === "string")
    && (advertised === null || (record(advertised) && typeof advertised.statement === "string" && typeof advertised.line === "number"));
}

function comparison(value: unknown): value is Comparison {
  return record(value) && typeof value.reachable === "boolean" && typeof value.selected_applicable === "boolean"
    && strings(value.withheld) && strings(value.supporting_arguments) && strings(value.derivation)
    && strings(value.missing_selected_inputs) && strings(value.recovered_inputs);
}

function argumentSynthesis(value: unknown): value is ArgumentSynthesis {
  return record(value) && value.mode === "argument" && typeof value.scope === "string" && record(value.argument)
    && typeof value.argument.argument_id === "string" && typeof value.argument.conclusion_statement_id === "string"
    && typeof value.argument.label === "string" && typeof value.argument.meaning === "string"
    && Array.isArray(value.inputs) && value.inputs.every(input)
    && Array.isArray(value.results) && value.results.every(result)
    && Array.isArray(value.comparisons) && value.comparisons.every(comparison)
    && comparison(value);
}

export function getArgumentSynthesis(argumentId: string, conclusionId: string) {
  const report = truthJson(["synthesis", argumentId, "--compare-premises"]);
  if (!argumentSynthesis(report) || report.argument.argument_id !== argumentId
    || report.argument.conclusion_statement_id !== conclusionId || report.withheld.length !== 0) {
    throw new Error(`Invalid argument synthesis for ${argumentId}`);
  }

  const expected = new Set(report.inputs.map(({ id }) => id));
  for (const { withheld } of report.comparisons) {
    if (withheld.length !== 1 || !expected.delete(withheld[0])) {
      throw new Error(`Unexpected premise comparison for ${argumentId}`);
    }
  }
  if (expected.size) {
    throw new Error(`Missing premise comparisons for ${argumentId}`);
  }
  const { scope, argument, inputs, results, comparisons, withheld, reachable, selected_applicable,
    missing_selected_inputs, recovered_inputs, supporting_arguments, derivation } = report;
  const baseline: Comparison = { withheld, reachable, selected_applicable,
    missing_selected_inputs, recovered_inputs, supporting_arguments, derivation };
  return { scope, argument, inputs, results, comparisons, baseline };
}
