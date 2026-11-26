import { expect, test } from "bun:test";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { CaseOverview, CasePremiseDetail } from "../app/case/god-exists/content";
import { currentCase, casePremiseHref, GOD_EXISTS, GOD_SENSE, ATTRIBUTE_IDS, type RecordedAssessment } from "./current-case";
import { getCorpus, type Corpus, type CorpusArgument } from "./corpus";
import { truthJson } from "./truth-cli";
import { getDossier } from "./premise-dossier";
import type { FrontierReport } from "./site-state";
import type { ScopedAssessment } from "./current-judgments";
import DossierPage from "../app/dossiers/[statementId]/page";
import { getCurrentCase, parseAssessmentBatch } from "./current-case-data";

const argument = (id: string, premises: string[], conclusion: string): CorpusArgument => ({
  id, premise_statement_ids: premises, conclusion_statement_id: conclusion, inference_ids: [], meaning: id,
});
const arguments_ = [argument("route-a", ["shared", "other"], GOD_EXISTS), argument("route-b", ["shared"], GOD_EXISTS),
  argument("transcription", ["extra"], GOD_EXISTS), argument("unverified", ["unverified-premise"], GOD_EXISTS),
  argument("support-shared", ["foundation", "other"], "shared"),
  argument("historical", [GOD_EXISTS, "historical-evidence"], "catholicism"), argument("attribute", [GOD_EXISTS], ATTRIBUTE_IDS[0])];
const statements = [GOD_EXISTS, "shared", "foundation", "other", "extra", "unverified-premise", "historical-evidence", "catholicism", ...ATTRIBUTE_IDS]
  .map((id) => ({ id, paraphrase: id }));
const results = ["route-a", "route-b", "transcription", "attribute", "support-shared"].map((id) => ({
  id: `result-${id}`, argument_id: id, challenge_module: "Fixture", solution_module: "Fixture", theorem: id,
  comparator_config: "fixture", status: "solution-present" as const,
  argument: arguments_.find((argument) => argument.id === id)!, meaning: id,
}));
const corpus: Corpus = { statements, arguments: arguments_, results, claims: [], inferences: [], relations: [],
  definitions: [{ id: GOD_SENSE, term: "GOD_4", definition: "Selected sense", basis: "stipulative" }],
  disambiguations: [], sources: [], passages: [], candidates: [] };
const report = truthJson(["frontier", "--fixture", "-", "--frontier-root", GOD_EXISTS], JSON.stringify({
  statements, arguments: arguments_, results, claims: [], inferences: [], relations: [],
  transcription_flags: [{ result_id: "result-transcription", argument_id: "transcription", proof_steps: 1,
    single_application_of: "fixture", goal_consequent_premises: [] }],
})) as FrontierReport;
const emptyBatch = { statements: {}, current_assessments: [], revision_impacts: [] };
const project = (overrides: Partial<Parameters<typeof currentCase>[0]> = {}) => currentCase({
  corpus, report, dossiers: {}, assessments: emptyBatch, revision: "fixture-revision", ...overrides,
});
const assessment = (excerpt: string, section: string): RecordedAssessment => ({
  kind: "assessment", section, path: "docs/notes/fixture.md", heading: "Provisional judgment", line: 4,
  date: null, dated_by: "latest date written in the note", excerpt, matched_record_ids: ["shared"],
});

test("God-only case excludes downstream history and keeps attributes separate", () => {
  const view = project();
  expect(view.routes.map((route) => route.id)).toEqual(["route-a", "route-b", "transcription", "unverified"]);
  expect(view.premises.map((premise) => premise.statement.id)).not.toContain("historical-evidence");
  expect(view.bundles.map((bundle) => bundle.id)).not.toContain("historical");
  expect(view.bundles.map((bundle) => bundle.id)).not.toContain("attribute");
  expect(view.attributes.map((attribute) => attribute.id)).toEqual([...ATTRIBUTE_IDS]);
  expect(view.established).toBe(false);
  expect(project({ corpus: { ...corpus, arguments: arguments_.filter((argument) => argument.id !== "attribute") } }).established).toBe(view.established);
  expect(() => project({ report: { ...report, root: "catholicism" } })).toThrow("God-existence");
});

test("complete shared bundles, direct assumptions and exact paths survive", () => {
  const view = project();
  expect(view.routes.find((route) => route.id === "route-a")?.premise_statement_ids).toEqual(["shared", "other"]);
  expect(view.routes.find((route) => route.id === "route-b")?.premise_statement_ids).toEqual(["shared"]);
  for (const bundle of view.bundles) {
    for (const premiseId of bundle.premise_statement_ids) {
      expect(view.premises.some((premise) => premise.statement.id === premiseId)).toBe(true);
    }
  }
  const shared = view.premises.find((premise) => premise.statement.id === "shared");
  expect(shared?.usedBy).toEqual(["route-a", "route-b"]);
  expect(shared?.directAssumption).toBe(true);
  expect(shared?.path).toEqual(["shared", "route-a", GOD_EXISTS]);
  expect(shared?.alternatives.length).toBeGreaterThan(0);
  expect(shared?.alternatives.some((bundle) => bundle.premise_statement_ids.includes("foundation") && bundle.premise_statement_ids.includes("other"))).toBe(true);
  for (const option of report.support_options.items) {
    expect(view.premises.find((premise) => premise.statement.id === option.statement_id)?.alternatives).toEqual(option.verified_alternative_bundles);
  }
});

test("verified, transcription and unverified bundles stay distinct", () => {
  expect(project().routes.map((route) => [route.id, route.status])).toEqual([
    ["route-a", "verified"], ["route-b", "verified"], ["transcription", "transcription"], ["unverified", "unverified"],
  ]);
});

test("cost never ranks strength or removes routes", () => {
  const before = project();
  const after = project({ report: { ...report, routes: { ...report.routes, routes: report.routes.routes.map((route, index) => ({
    ...route, cost: 999 - index, cheapest: !route.cheapest,
  })) } } });
  expect(after).toEqual(before);
  expect("strength" in before.routes[0]).toBe(false);
});

test("conflicting assessments remain separate; absent assessments stay unknown", () => {
  const entries = [assessment("Positive warrant", "note#positive"), assessment("Premise disputed", "note#disputed")];
  const view = project({ assessments: { ...emptyBatch, statements: { shared: entries, "historical-evidence": [assessment("Downstream", "note#history")] } } });
  expect(view.premises.find((premise) => premise.statement.id === "shared")?.assessments).toEqual(entries);
  expect(view.premises.find((premise) => premise.statement.id === "other")?.assessments).toEqual([]);
  expect(view.assessments).toHaveLength(2);
  expect(view.assessments.map((entry) => entry.assessment.excerpt).sort()).toEqual(["Positive warrant", "Premise disputed"]);
  expect(parseAssessmentBatch({ ...emptyBatch, statements: { shared: entries, other: [] } })).toEqual({ ...emptyBatch, statements: { shared: entries, other: [] } });
  expect(() => parseAssessmentBatch({ statements: { shared: [{ excerpt: "Missing provenance" }] } })).toThrow();
});

test("explicit scopes drive the overview, premise judgments, shared routes and revision dispositions", () => {
  const current: ScopedAssessment = {
    attempt_id: "finding", statement_ids: ["shared", "other"], scope: "Two premise comparison",
    assessment: "The common-source advantage depends on the producer. Partitioned sources survive.",
    next_test: "Trace each actual contribution.", note: "docs/notes/fixture.md#common-source", date: "2026-11-03",
    review: "accepted_qualified", publication: "published", reviewed_revision: "c".repeat(40),
    evidence: "Reviewer accepted the scoped result.", supersedes: "Narrows the previous inference.",
  };
  const batch = parseAssessmentBatch({ statements: { shared: [assessment("Incidental excerpt only", "note#context")] },
    current_assessments: [current, { ...current, attempt_id: "other-reading", assessment: "A different interpretation.", scope: "Alternative reading" }],
    revision_impacts: [{ attempt_id: "revision-attempt", change: { kind: "judgment", revision: "narrower-scope",
      previous: "Earlier record", reason: "The local case leaves the global bridge open.", statement_ids: ["foundation"] },
      consumers: [{ consumer: "statements:shared", tier: "premise_use", disposition: "retained", reason: "The narrower claim suffices." }] }],
  });
  const view = project({ assessments: batch });
  const overview = renderToStaticMarkup(createElement(CaseOverview, { view }));
  expect(overview).toContain("No current assessment explicitly covers this proposition.");
  expect(overview).toContain(current.assessment);
  expect(overview).toContain(current.next_test);
  expect(overview).toContain('value="other-reading"');
  expect(overview.split('value="finding"')).toHaveLength(2);
  expect(overview).not.toContain("Incidental excerpt only");
  expect(view.readings[0].routeGroups?.map(({ propositionIds, routes }) => [propositionIds, routes.map((link) => link.id)]))
    .toEqual([[["shared", "other"], ["route-a", "route-b"]]]);
  const shared = view.premises.find((p) => p.statement.id === "shared")!;
  expect(shared.readings).toHaveLength(2);
  expect(view.premises.find((p) => p.statement.id === "foundation")?.readings).toEqual([]);
  const html = renderToStaticMarkup(createElement(CasePremiseDetail, { view, premise: shared }));
  for (const text of [current.assessment, current.scope, current.next_test, current.evidence, current.note,
    "/attempts/finding", current.reviewed_revision, "The narrower claim suffices.", "The local case leaves the global bridge open."]) {
    expect(html).toContain(text);
    expect(html.indexOf(text)).toBeLessThan(html.indexOf("Incidental excerpt only"));
  }
  expect(view.premises.find((p) => p.statement.id === "foundation")?.revisions).toHaveLength(1);
  expect(view.premises.find((p) => p.statement.id === "other")?.revisions).toEqual([]);
  const proposed = project({ assessments: { ...emptyBatch, current_assessments: [{ ...current, review: "unreviewed" }] } });
  const proposalHtml = renderToStaticMarkup(createElement(CaseOverview, { view: proposed }));
  expect(proposalHtml).toContain("proposed revision");
  expect(proposalHtml).not.toContain("reviewed revision");
  expect(() => parseAssessmentBatch({ ...batch, current_assessments: [{ ...current, scope: undefined }] })).toThrow();
  expect(() => parseAssessmentBatch({ ...batch, revision_impacts: [{ change: {} }] })).toThrow();
});

test("shared findings render once without dropping their premise associations", () => {
  const attempt = { id: "shared-finding", statement_ids: ["shared", "other"], date: "2026-11-17", kind: "derivation" as const,
    outcome: "blocked" as const, summary: "The next test is a distinct bridge", blocker: "Missing bridge", evidence: ["docs/notes/fixture.md"] };
  // Only attempts are consumed from dossiers: use a real-shaped report at the public boundary.
  const dossier = (id: string) => ({ statement: { id, paraphrase: id }, root: "catholicism", closure: null, established: false,
    frontier: null, claim_ids: [], supporting_claim_ids: [], definition_ids: [], disambiguation_ids: [], argument_ids: [],
    result_ids: [], transcription_result_ids: [], instantiation_result_ids: [], alternative_relation_ids: [], objection_relation_ids: [],
    countermodel_attempt_ids: [], attempts: [attempt], model_evaluations: [], route_contributions: [] });
  const view = project({ dossiers: { shared: dossier("shared"), other: dossier("other"), "historical-evidence": {
    ...dossier("historical-evidence"), attempts: [{ ...attempt, id: "downstream-finding" }],
  } } });
  expect(view.attempts).toEqual([attempt]);
  expect(view.premises.find((premise) => premise.statement.id === "shared")?.attempts).toEqual([attempt]);
  expect(view.premises.find((premise) => premise.statement.id === "other")?.attempts).toEqual([attempt]);
});


test("compact overview links every proposition and preserves complete immediate root bundles", () => {
  const view = project({ assessments: { ...emptyBatch, statements: { shared: [assessment("Distinct recorded judgment", "note#judgment")] } } });
  const html = renderToStaticMarkup(createElement(CaseOverview, { view }));
  expect(html).not.toContain("<details");
  expect(html).not.toContain("Distinct recorded judgment");
  for (const premise of view.premises) {
    expect(html).toContain(`href="${casePremiseHref(premise.statement.id)}"`);
  }
  for (const bundle of view.routes) {
    expect(html).toContain(`id="argument-${bundle.id}"`);
    for (const id of bundle.premise_statement_ids) {
      expect(html).toContain(`href="${casePremiseHref(id)}"`);
    }
  }
});

test("proposition pages expose all expanded bundles and provenance with canonical evidence links", () => {
  const entries = [assessment("Positive warrant", "note#positive"), assessment("Premise disputed", "note#disputed")];
  const view = project({ assessments: { ...emptyBatch, statements: { shared: entries } } });
  for (const premise of view.premises) {
    const html = renderToStaticMarkup(createElement(CasePremiseDetail, { view, premise }));
    expect(html).not.toContain("<details");
    expect(html).toContain(`href="/dossiers/${premise.statement.id}"`);
    expect(html).toContain(`href="/dossiers/${premise.statement.id}#dossier-rivals"`);
    for (const bundle of premise.bundles) {
      expect(html).toContain(`id="argument-${bundle.id}"`);
      for (const id of bundle.premise_statement_ids) {
        expect(html).toContain(`href="${casePremiseHref(id)}"`);
      }
    }
    for (const bundle of premise.alternatives) {
      for (const id of bundle.premise_statement_ids) {
        expect(html).toContain(`href="${casePremiseHref(id)}"`);
      }
      for (const id of bundle.result_ids) {
        expect(html).toContain(`href="/results/${id}"`);
      }
    }
    for (const entry of premise.assessments) {
      expect(html).toContain(entry.excerpt);
      expect(html).toContain(`${entry.path}#L${entry.line}`);
    }
  }
});


test("real case preserves destinations for every support and evidence record", () => {
  const view = getCurrentCase();
  const commonGiver = "0881e859-c4c3-53ff-9bec-b61294e12d51";
  const reading = view.premises.find((p) => p.statement.id === commonGiver)?.readings.find((item) => item.current.attempt_id === "efe9809e-be74-5683-b722-c2694647b840");
  expect(reading).toBeDefined();
  expect(reading?.current.note).toContain("root-route-modal-load.md");
  expect(view.premises.find((p) => p.statement.id === GOD_EXISTS)?.readings.length).toBeGreaterThan(0);
  const corpus = getCorpus();
  const scope = new Set(view.premises.map((premise) => premise.statement.id));
  const resultIds = new Set(corpus.results.map((result) => result.id));
  const argumentIds = new Set(corpus.arguments.map((argument) => argument.id));
  const statementIds = new Set(corpus.statements.map((statement) => statement.id));
  for (const premise of view.premises) {
    expect(statementIds.has(premise.statement.id)).toBe(true);
    for (const bundle of premise.bundles) {
      expect(argumentIds.has(bundle.id)).toBe(true);
      for (const id of bundle.premise_statement_ids) { expect(scope.has(id)).toBe(true); }
      for (const proof of bundle.proofs) { expect(resultIds.has(proof.id)).toBe(true); expect(proof.theorem).toBeTruthy(); }
      for (const id of bundle.openLeaves ?? []) { expect(scope.has(id)).toBe(true); }
    }
    for (const bundle of premise.alternatives) {
      for (const id of bundle.premise_statement_ids) { expect(scope.has(id)).toBe(true); }
      for (const id of bundle.argument_ids) { expect(argumentIds.has(id)).toBe(true); }
      for (const id of bundle.result_ids) { expect(resultIds.has(id)).toBe(true); }
    }
    // Every finding keeps a direct link to its canonical attempt page.
    if (premise.attempts.length) {
      const html = renderToStaticMarkup(createElement(CasePremiseDetail, { view, premise }));
      for (const attempt of premise.attempts) { expect(html).toContain(`href="/attempts/${attempt.id}"`); }
    }
  }
}, 120_000);


test("the ordinary premise dossier displays the current judgment and links its own evidence and next test", async () => {
  const statementId = "0881e859-c4c3-53ff-9bec-b61294e12d51";
  const html = renderToStaticMarkup(await DossierPage({ params: Promise.resolve({ statementId }) }));
  const judgmentsStart = html.indexOf('id="assessments"');
  const sourcesStart = html.indexOf('aria-labelledby="dossier-sources"');
  expect(judgmentsStart).toBeGreaterThanOrEqual(0);
  expect(sourcesStart).toBeGreaterThan(judgmentsStart);
  const judgments = html.slice(judgmentsStart, sourcesStart);
  const attempts = getDossier(statementId).attempts;
  const selectedId = judgments.match(/<option value="([^"]+)" selected=""/)?.[1];
  expect(selectedId).toBeDefined();
  const selected = attempts.find((attempt) => attempt.id === selectedId)?.current_assessment;
  if (!selected) throw new Error("The displayed judgment lacks an assessment in this dossier");
  expect(selected.statement_ids).toContain(statementId);
  const scopedDates = attempts.flatMap(({ current_assessment }) =>
    current_assessment?.statement_ids.includes(statementId) ? [current_assessment.date] : []);
  expect(selected.date).toBe(scopedDates.sort().at(-1));
  expect(judgments).toContain(renderToStaticMarkup(selected.assessment));
  expect(judgments).toContain("Next test");
  expect(judgments).toContain(renderToStaticMarkup(selected.next_test));
  expect(judgments).toContain(renderToStaticMarkup(selected.evidence));
  expect(judgments).toContain(`href="/attempts/${selectedId}"`);
  for (const id of ["4e4a3c81-3e59-4d2d-82f3-7668e7aa560e", "efe9809e-be74-5683-b722-c2694647b840"]) {
    expect(judgments).toContain(`<option value="${id}"`);
  }
}, 120_000);
