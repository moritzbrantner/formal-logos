import { describe, expect, test } from "bun:test";

import {
  argumentsConcludingStatement,
  argumentsUsingStatement,
  claimsForSource,
  claimsForStatement,
  disambiguationsForDefinition,
  findArgument,
  findCandidate,
  findClaim,
  findDefinition,
  findInference,
  findPassage,
  findResult,
  findSource,
  findStatement,
  getCorpus,
  passagesForSource,
  resultsForArgument,
  termsFor,
  usesOfTerm,
  type Corpus,
  type CorpusArgument,
  type CorpusClaim,
  type CorpusPassage,
  type CorpusResult,
  type CorpusStatement,
  type TermLinks,
} from "./corpus";

function emptyCorpus(): Corpus {
  return {
    sources: [], passages: [], statements: [], claims: [], inferences: [],
    arguments: [], relations: [], results: [], candidates: [], definitions: [], disambiguations: [],
  };
}

function argument(id: string, premises: string[], conclusion: string): CorpusArgument {
  return { id, premise_statement_ids: premises, conclusion_statement_id: conclusion, inference_ids: [], meaning: id };
}

function fixture(): Corpus {
  const statements: CorpusStatement[] = [
    { id: "s2", paraphrase: "Second", definition_ids: ["d2", "d1", "d2"], disambiguation_ids: ["sense2"] },
    { id: "s1", paraphrase: "First", definition_ids: ["d1"], disambiguation_ids: ["sense1", "sense1"] },
    { id: "s3", paraphrase: "Third" },
  ];
  const passage: CorpusPassage = {
    id: "p1", kind: "bibliographic_span", source_id: "source", locator: "1", claim_locator_prefixes: ["1"],
    author: "Author", title: "Work", year: 2026, language: "en", why_bibliographic: "Fixture",
  };
  const claims: CorpusClaim[] = [statements[1], statements[0], statements[1]].map((statement, i) => ({
    id: `c${i}`, statement_id: statement.id, source_id: "source", locator: "1", interpretation: "Fixture",
    status: "formalized", statement, passage, paraphrase: statement.paraphrase,
    definition_ids: ["d2", "d2"], disambiguation_ids: ["sense1", "sense1"],
  }));
  const arguments_: CorpusArgument[] = [
    { ...argument("a2", ["s1", "s1"], "s2"), commitment_statement_ids: ["s1", "s3"], definition_ids: ["d2", "d2"] },
    { ...argument("a1", ["s3"], "s2"), commitment_statement_ids: ["s1"], disambiguation_ids: ["sense2", "sense2"] },
    argument("a3", [], "s3"),
  ];
  const results: CorpusResult[] = [arguments_[1], arguments_[0], arguments_[1]].map((entry, i) => ({
    id: `r${i}`, argument_id: entry.id, argument: entry, meaning: entry.meaning,
    challenge_module: "Fixture.Challenge", solution_module: "Fixture.Solution", theorem: "fixture",
    comparator_config: "fixture.json", status: "solution-present",
  }));
  return {
    ...emptyCorpus(), statements, claims, arguments: arguments_, results,
    passages: [passage, { ...passage, id: "p2" }],
    sources: [{ id: "source", kind: "primary_text", author: "Author", work: "Work", citation_system: "pages", work_urn: "fixture", catalog_url: "", notes: "" }],
    definitions: ["d1", "d2"].map((id) => ({ id, term: id, definition: id, basis: "stipulative" })),
    disambiguations: [
      { id: "sense2", term: "Second", sense_definition_ids: ["d2", "d1", "d2"], resolution: "Fixture" },
      { id: "sense1", term: "First", sense_definition_ids: ["d1"], resolution: "Fixture" },
    ],
    inferences: [{ id: "i1", input_statement_ids: ["s1"], output_statement_id: "s2", rule: "fixture", meaning: "Fixture", assumption_statement_ids: [], discharged_statement_ids: [] }],
    candidates: [{ id: "candidate", source_id: "source", locator: "1", priority: 1, goal: "Fixture", reason: "Fixture", status: "candidate" }],
  };
}

function expectQueriesToMatchScans(corpus: Corpus, sampleSize = Infinity) {
  const queryIds = (records: readonly { id: string }[]) => {
    const step = Math.max(1, Math.ceil(records.length / sampleSize));
    return [...records.filter((_, i) => i % step === 0 || i === records.length - 1).map((entry) => entry.id), "missing"];
  };
  const finders = [
    [corpus.sources, findSource], [corpus.passages, findPassage],
    [corpus.statements, findStatement], [corpus.claims, findClaim],
    [corpus.inferences, findInference], [corpus.arguments, findArgument],
    [corpus.results, findResult], [corpus.candidates, findCandidate],
    [corpus.definitions, findDefinition],
  ] as const;
  for (const [records, find] of finders) {
    for (const id of queryIds(records)) {
      expect(find(corpus, id)).toBe(records.find((entry) => entry.id === id));
    }
  }
  for (const id of queryIds(corpus.statements)) {
    expect(claimsForStatement(corpus, id)).toEqual(corpus.claims.filter((entry) => entry.statement_id === id));
    expect(argumentsUsingStatement(corpus, id)).toEqual(corpus.arguments.filter((entry) =>
      entry.premise_statement_ids.includes(id) || (entry.commitment_statement_ids ?? []).includes(id)));
    expect(argumentsConcludingStatement(corpus, id)).toEqual(corpus.arguments.filter((entry) => entry.conclusion_statement_id === id));
  }
  for (const id of queryIds(corpus.arguments)) {
    expect(resultsForArgument(corpus, id)).toEqual(corpus.results.filter((entry) => entry.argument_id === id));
  }
  for (const id of queryIds(corpus.sources)) {
    expect(passagesForSource(corpus, id)).toEqual(corpus.passages.filter((entry) => entry.source_id === id));
    expect(claimsForSource(corpus, id)).toEqual(corpus.claims.filter((entry) => entry.source_id === id));
  }
  for (const id of queryIds(corpus.definitions)) {
    expect(disambiguationsForDefinition(corpus, id)).toEqual(corpus.disambiguations.filter((entry) => entry.sense_definition_ids.includes(id)));
  }
  for (const field of ["definition_ids", "disambiguation_ids"] as const) {
    const records = field === "definition_ids" ? corpus.definitions : corpus.disambiguations;
    for (const id of queryIds(records)) {
      const links = (entry: TermLinks) => entry[field]?.includes(id) ?? false;
      expect(usesOfTerm(corpus, field, id)).toEqual({
        statements: corpus.statements.filter(links), claims: corpus.claims.filter(links), arguments: corpus.arguments.filter(links),
      });
    }
  }
}

describe("corpus snapshot query indexes", () => {
  test("match independent scans, including collection order and repeated links", () => {
    expectQueriesToMatchScans(fixture());
  });

  test("preserve first-match lookup and every matching row for duplicate ids", () => {
    const corpus = fixture();
    corpus.statements.push({ ...corpus.statements[0], paraphrase: "Later duplicate" });
    corpus.arguments.push({ ...corpus.arguments[0], meaning: "Later duplicate" });
    corpus.claims.push({ ...corpus.claims[0], interpretation: "Later duplicate" });
    expectQueriesToMatchScans(corpus);
  });

  test("preserve linked term order separately from disambiguation collection order", () => {
    const corpus = fixture();
    expect(termsFor(corpus, [{ definition_ids: ["d2", "d1", "missing", "d2"], disambiguation_ids: ["sense1"] }])).toEqual({
      definitions: [corpus.definitions[1], corpus.definitions[0]],
      disambiguations: corpus.disambiguations,
    });
  });

  test("returned arrays cannot mutate cached query buckets", () => {
    const corpus = fixture();
    const reads = [
      () => disambiguationsForDefinition(corpus, "d1"),
      () => passagesForSource(corpus, "source"),
      () => claimsForSource(corpus, "source"),
      () => claimsForStatement(corpus, "s1"),
      () => argumentsUsingStatement(corpus, "s1"),
      () => argumentsConcludingStatement(corpus, "s2"),
      () => resultsForArgument(corpus, "a1"),
      () => usesOfTerm(corpus, "definition_ids", "d2").statements,
      () => usesOfTerm(corpus, "definition_ids", "d2").claims,
      () => usesOfTerm(corpus, "definition_ids", "d2").arguments,
    ];
    for (const read of reads) {
      const expected = read();
      read().reverse();
      read().splice(0);
      expect(read()).toEqual(expected);
      expect(read()).not.toBe(expected);
    }
  });

  test("separate snapshots with the same ids do not share records or memberships", () => {
    const first = fixture();
    const second = fixture();
    second.statements[0].paraphrase = "Updated snapshot";
    second.arguments[0].premise_statement_ids = ["s2"];
    second.arguments[0].commitment_statement_ids = [];
    expect(findStatement(first, "s2")).toBe(first.statements[0]);
    expect(findStatement(second, "s2")).toBe(second.statements[0]);
    expect(argumentsUsingStatement(first, "s1")).toEqual(first.arguments.slice(0, 2));
    expect(argumentsUsingStatement(second, "s1")).toEqual([second.arguments[1]]);
  });

  test("repeated lookups do not revisit unrelated records after indexing", () => {
    const corpus = emptyCorpus();
    let recordReads = 0;
    corpus.arguments = Array.from({ length: 1_000 }, (_, i) => ({
      ...argument(`a${i}`, [], ""),
      get id() { recordReads += 1; return `a${i}`; },
      get premise_statement_ids() { recordReads += 1; return [`s${i}`]; },
      get conclusion_statement_id() { recordReads += 1; return `s${i + 1}`; },
    }));
    findArgument(corpus, "a0");
    expect(recordReads).toBeGreaterThan(0);
    recordReads = 0;
    for (let i = 0; i < 100; i += 1) {
      expect(findArgument(corpus, `a${i}`)).toBe(corpus.arguments[i]);
      expect(argumentsUsingStatement(corpus, `s${i}`)).toEqual([corpus.arguments[i]]);
      expect(argumentsConcludingStatement(corpus, `s${i + 1}`)).toEqual([corpus.arguments[i]]);
    }
    expect(recordReads).toBe(0);
  });

  test("match the simple query oracle for representative current corpus records", () => {
    expectQueriesToMatchScans(getCorpus(), 20);
  });
});
