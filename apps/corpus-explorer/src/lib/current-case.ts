import type { Corpus } from "./corpus";
import type { PremiseDossier } from "./premise-dossier";
import { resultKind, statementState, type FrontierReport } from "./site-state";

export const GOD_EXISTS = "8626f8a5-9531-5da7-9ebd-f901e74b1129";
export const GOD_SENSE = "88f9f6e8-997b-5f7d-afa1-c501954c3807";
export const GOD_DISAMBIGUATION = "205a39c3-915d-5fe4-8076-a9ff91329e08";
export const ATTRIBUTE_IDS = [
  "9f4e5f17-e808-5c58-9eac-faacbb5c3a56",
  "33b18ae7-4578-54bc-a2b5-edce99b21fc2",
  "29818edd-9f5a-5414-baa2-9a7d0c8abf18",
  "66aecdd7-ea4e-55c6-9377-10db08893854",
] as const;

export type RecordedAssessment = {
  kind: "assessment" | "rival_analysis";
  section: string;
  path: string;
  heading: string;
  line: number;
  date: string | null;
  dated_by: string;
  excerpt: string;
  matched_record_ids: string[];
};
export type AssessmentBatch = Record<string, RecordedAssessment[]>;

/** Presentation only. No closure, philosophical ranking or prose synthesis. */
export function currentCase({ corpus, report, dossiers, assessments, revision }: {
  corpus: Corpus;
  report: FrontierReport;
  dossiers: Record<string, PremiseDossier>;
  assessments: AssessmentBatch;
  revision: string;
}) {
  if (report.root !== GOD_EXISTS) {
    throw new Error("The current case requires the God-existence frontier root");
  }
  const statements = new Map(corpus.statements.map((statement) => [statement.id, statement]));
  const target = statements.get(GOD_EXISTS);
  const sense = corpus.definitions.find((definition) => definition.id === GOD_SENSE);
  if (!target || !sense) {
    throw new Error("The current case target and selected sense must exist");
  }
  // The frontier owns root-route reachability. Never use the default Catholicism paths.
  const scoped = new Set([GOD_EXISTS, ...report.reaching_root_statements]);
  const options = new Map(report.support_options.items.map((item) => [item.statement_id, item]));
  const rootRoutes = new Map(report.routes.routes.map((route) => [route.argument_id, route]));
  const bundles = corpus.arguments
    .filter((argument) => scoped.has(argument.conclusion_statement_id))
    .map((argument) => {
      const results = corpus.results.filter((result) => result.argument_id === argument.id);
      const route = rootRoutes.get(argument.id);
      let status: "verified" | "transcription" | "unverified" = "unverified";
      if (results.length) {
        status = results.some((result) => resultKind(report, result.id).kind === "derivation") ? "verified" : "transcription";
      }
      return { ...argument, status, resultIds: results.map((result) => result.id),
        openLeaves: route?.open_premise_statement_ids ?? null };
    })
    .sort((a, b) => a.id.localeCompare(b.id));
  const paths = new Map<string, string[]>([[GOD_EXISTS, [GOD_EXISTS]]]);
  const queue = [GOD_EXISTS];
  for (let cursor = 0; cursor < queue.length; cursor += 1) {
    const conclusion = queue[cursor];
    for (const bundle of bundles.filter((entry) => entry.conclusion_statement_id === conclusion)) {
      for (const premise of bundle.premise_statement_ids) {
        if (!paths.has(premise)) {
          paths.set(premise, [premise, bundle.id, ...(paths.get(conclusion) ?? [])]);
          queue.push(premise);
        }
      }
    }
  }
  const premises = [...scoped].flatMap((id) => {
    const statement = statements.get(id);
    if (!statement) {
      throw new Error(`Missing current-case statement ${id}`);
    }
    const frontierItem = report.items.find((entry) => entry.statement_id === id);
    const usedBy = bundles.filter((bundle) => bundle.premise_statement_ids.includes(id));
    const option = options.get(id);
    return [{ statement, state: statementState(report, id), established: report.established_statements.includes(id),
      path: frontierItem?.path_to_root ?? paths.get(id) ?? null,
      usedBy: usedBy.map((bundle) => bundle.id),
      bundles: bundles.filter((bundle) => bundle.conclusion_statement_id === id),
      directAssumption: option?.direct_assumption_available ?? true,
      alternatives: option?.verified_alternative_bundles ?? [],
      assessments: assessments[id] ?? [],
      attempts: dossiers[id]?.attempts ?? [],
      objections: corpus.relations.filter((relation) => relation.object_id === id && ["attacks", "alternative_to"].includes(relation.predicate)),
    }];
  });
  // Centrality is navigation only; deterministic tie-breaking does not rank warrant.
  premises.sort((a, b) => b.usedBy.length - a.usedBy.length || a.statement.id.localeCompare(b.statement.id));
  const recorded = new Map<string, { assessment: RecordedAssessment; statementIds: string[] }>();
  for (const premise of premises) {
    for (const assessment of premise.assessments) {
      const key = `${assessment.section}:${assessment.line}`;
      const entry = recorded.get(key) ?? { assessment, statementIds: [] };
      entry.assessment = { ...entry.assessment, matched_record_ids: [...new Set([...entry.assessment.matched_record_ids, ...assessment.matched_record_ids])].sort() };
      entry.statementIds.push(premise.statement.id);
      recorded.set(key, entry);
    }
  }
  const attempts = [...new Map(premises.flatMap((premise) => premise.attempts).map((attempt) => [attempt.id, attempt])).values()]
    .sort((a, b) => a.id.localeCompare(b.id));
  return { target, sense, revision, premises, bundles, attempts,
    routes: bundles.filter((bundle) => bundle.conclusion_statement_id === GOD_EXISTS),
    assessments: [...recorded.values()].sort((a, b) => a.assessment.section.localeCompare(b.assessment.section)),
    attributes: ATTRIBUTE_IDS.flatMap((id) => {
      const statement = statements.get(id);
      return statement ? [statement] : [];
    }),
    established: report.established_statements.includes(GOD_EXISTS),
    state: statementState(report, GOD_EXISTS),
  };
}

/** Stable static destinations, derived from proposition identity, never a registry. */
export function casePremiseHref(statementId: string) {
  return `/case/god-exists/premises/${encodeURIComponent(statementId)}`;
}
