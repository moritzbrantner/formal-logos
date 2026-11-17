import { describe, expect, test } from "bun:test";

import { projectArgumentComposition, type ArgumentProjectionCorpus } from "./argument-projection";
import { getCorpus, type Corpus, type CorpusArgument, type CorpusInference, type CorpusResult } from "./corpus";
import { resultProjectionCorpus } from "./result-projection";

function argument(id: string, premises: string[], conclusion: string, inferences: string[] = []): CorpusArgument {
  return {
    id, premise_statement_ids: premises, conclusion_statement_id: conclusion, inference_ids: inferences,
    meaning: `${id} follows from its premises.`, label: `Label for ${id}`, definition_ids: ["DEFINITION"],
  };
}

function inference(id: string, inputs: string[], output: string): CorpusInference {
  return {
    id, input_statement_ids: inputs, output_statement_id: output, rule: "fixture", meaning: `${id} step.`,
    label: `Label for ${id}`, assumption_statement_ids: [], discharged_statement_ids: [],
  };
}

function result(id: string, argument: CorpusArgument): CorpusResult {
  return {
    id, argument, argument_id: argument.id, meaning: argument.meaning,
    challenge_module: "Fixture.Challenge", solution_module: "Fixture.Solution", theorem: "fixture",
    comparator_config: "fixture.json", status: "solution-present",
  };
}

function corpusWith(arguments_: CorpusArgument[]): Corpus {
  return {
    sources: [], passages: [], statements: [], claims: [], inferences: [], arguments: arguments_,
    relations: [], results: [], candidates: [], definitions: [], disambiguations: [],
  };
}

function fixture() {
  const root = argument("root", ["B", "A", "B"], "R", ["root-step"]);
  root.commitment_statement_ids = ["K"];
  const first = argument("first", ["C"], "A", ["first-step"]);
  const second = argument("second", ["C", "R"], "B", ["second-step"]);
  const unverified = argument("unverified", ["C"], "A");
  const cycle = argument("cycle", ["A"], "C");
  const unrelated = argument("unrelated", [], "Z");
  const corpus = corpusWith([
    first, second, unverified, root, cycle, argument("commitment-only", [], "K"), unrelated,
  ]);
  corpus.statements = ["Z", "A", "R", "T", "C", "B", "Q", "K"].map((id) => ({ id, paraphrase: `${id} statement.` }));
  corpus.inferences = [
    inference("second-step", ["C", "R"], "B"),
    inference("unused", ["Z"], "K"),
    inference("root-step", ["A", "B"], "R"),
    inference("first-step", ["C", "Q"], "T"),
  ];
  corpus.results = [result("r-second", second), result("r-root", root), result("r-first", first), result("r-second-again", second), result("r-unrelated", unrelated)];
  return { corpus, root };
}

// Independent reference: the original page's simple full scans, including its
// ordering and duplicate-ID behavior. It deliberately does not use query indexes.
function referenceProjection(corpus: Corpus, argument: CorpusArgument): ArgumentProjectionCorpus {
  const reachable = new Map([[argument.id, argument]]);
  for (const current of reachable.values()) {
    for (const candidate of corpus.arguments) {
      if (!reachable.has(candidate.id) && current.premise_statement_ids.includes(candidate.conclusion_statement_id)) {
        reachable.set(candidate.id, candidate);
      }
    }
  }
  const arguments_ = [...reachable.values()];
  const inferenceIds = new Set(arguments_.flatMap((entry) => entry.inference_ids));
  const inferences = corpus.inferences.filter((entry) => inferenceIds.has(entry.id));
  const statementIds = new Set([
    ...arguments_.flatMap((entry) => [...entry.premise_statement_ids, entry.conclusion_statement_id]),
    ...inferences.flatMap((entry) => [...entry.input_statement_ids, entry.output_statement_id]),
  ]);
  return {
    statements: corpus.statements.filter((entry) => statementIds.has(entry.id)).map(({ id, paraphrase }) => ({ id, paraphrase })),
    arguments: arguments_, inferences,
    verified_argument_ids: corpus.results.map((entry) => entry.argument_id).filter((id) => reachable.has(id)),
  };
}

function clientFields(projection: ArgumentProjectionCorpus): ArgumentProjectionCorpus {
  return {
    ...projection,
    arguments: projection.arguments.map((entry) => ({
      id: entry.id, premise_statement_ids: entry.premise_statement_ids,
      conclusion_statement_id: entry.conclusion_statement_id, inference_ids: entry.inference_ids, meaning: entry.meaning,
    })),
    inferences: projection.inferences.map((entry) => ({
      id: entry.id, input_statement_ids: entry.input_statement_ids,
      output_statement_id: entry.output_statement_id, rule: entry.rule, meaning: entry.meaning,
    })),
  };
}

describe("result projection preparation", () => {
  test("preserves corpus order, cycles, shared support and the separate verification list", () => {
    const { corpus, root } = fixture();
    const actual = resultProjectionCorpus(corpus, root);
    expect(actual).toEqual(clientFields(referenceProjection(corpus, root)));
    expect(actual.arguments.map((entry) => entry.id)).toEqual(["root", "first", "second", "unverified", "cycle"]);
    expect(actual.inferences.map((entry) => entry.id)).toEqual(["second-step", "root-step", "first-step"]);
    expect(actual.statements.map((entry) => entry.id)).toEqual(["A", "R", "T", "C", "B", "Q"]);
    expect(actual.verified_argument_ids).toEqual(["second", "root", "first", "second"]);
  });

  test("sends only client fields while preserving collapsed and expanded graph behavior", () => {
    const { corpus, root } = fixture();
    const before = referenceProjection(corpus, root);
    const after = resultProjectionCorpus(corpus, root);
    expect(JSON.stringify(after).length).toBeLessThan(JSON.stringify(before).length);
    expect(after.arguments.every((entry) => Object.keys(entry).length === 5)).toBe(true);
    expect(after.inferences.every((entry) => Object.keys(entry).length === 5)).toBe(true);
    for (const expanded of [new Set<string>(), new Set([root.id]), new Set(before.arguments.map((entry) => entry.id))]) {
      expect(projectArgumentComposition(after, root.id, expanded)).toEqual(projectArgumentComposition(before, root.id, expanded));
    }
  });

  test("keeps absent links absent and never expands commitments", () => {
    const root = argument("root", ["missing"], "conclusion", ["missing-step"]);
    root.commitment_statement_ids = ["commitment"];
    const corpus = corpusWith([argument("commitment-support", [], "commitment")]);
    expect(resultProjectionCorpus(corpus, root)).toEqual(clientFields(referenceProjection(corpus, root)));
    expect(resultProjectionCorpus(corpus, root).arguments.map((entry) => entry.id)).toEqual([root.id]);
  });

  test("preserves the first matching record for duplicate IDs and repeated record references", () => {
    const root = argument("root", ["B", "A"], "R");
    const first = argument("same-id", [], "A");
    const other = argument("other", [], "B");
    const duplicate = argument("same-id", ["unreachable"], "B");
    const corpus = corpusWith([first, other, first, duplicate]);
    expect(resultProjectionCorpus(corpus, root)).toEqual(clientFields(referenceProjection(corpus, root)));
    expect(resultProjectionCorpus(corpus, root).arguments.map((entry) => entry.conclusion_statement_id)).toEqual(["R", "A", "B"]);
  });

  test("keeps separate snapshots and their argument order independent", () => {
    const { corpus, root } = fixture();
    const reordered = { ...corpus, arguments: [...corpus.arguments].reverse() };
    expect(resultProjectionCorpus(corpus, root)).toEqual(clientFields(referenceProjection(corpus, root)));
    expect(resultProjectionCorpus(reordered, root)).toEqual(clientFields(referenceProjection(reordered, root)));
    expect(resultProjectionCorpus(corpus, root).arguments).not.toEqual(resultProjectionCorpus(reordered, root).arguments);
  });

  test("does not inspect unrelated conclusions again after indexing the snapshot", () => {
    let unrelatedReads = 0;
    const chain = Array.from({ length: 20 }, (_, index) => argument(`chain-${index}`, [`S-${index + 1}`], `S-${index}`));
    const unrelated = Array.from({ length: 1_000 }, (_, index) => ({
      ...argument(`unrelated-${index}`, [], ""),
      get conclusion_statement_id() {
        unrelatedReads++;
        return `unrelated-statement-${index}`;
      },
    }));
    const corpus = corpusWith([...chain, ...unrelated]);
    const root = chain[0]!;
    resultProjectionCorpus(corpus, root);
    unrelatedReads = 0;
    expect(resultProjectionCorpus(corpus, root).arguments.map((entry) => entry.id)).toEqual(chain.map((entry) => entry.id));
    expect(unrelatedReads).toBe(0);
    referenceProjection(corpus, root);
    expect(unrelatedReads).toBe(chain.length * unrelated.length);
  });

  test("matches the reference for a spread of real result projections", () => {
    const corpus = getCorpus();
    const interval = Math.max(1, Math.floor(corpus.results.length / 16));
    for (const result of corpus.results.filter((_, index) => index % interval === 0)) {
      expect(resultProjectionCorpus(corpus, result.argument)).toEqual(clientFields(referenceProjection(corpus, result.argument)));
    }
  });
});
