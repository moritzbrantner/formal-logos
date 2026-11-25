import { truthJson } from "./truth-cli";
import { currentCase, GOD_EXISTS, type AssessmentBatch, type RecordedAssessment } from "./current-case";
import { getCorpus } from "./corpus";
import { getDossiers } from "./premise-dossier";
import { getBuildInfo, getFrontierReport } from "./site-state";
import { currentAssessment, record, revisionImpact } from "./current-judgments";

function assessment(value: unknown): value is RecordedAssessment {
  return record(value) && (value.kind === "assessment" || value.kind === "rival_analysis")
    && ["section", "path", "heading", "dated_by", "excerpt"].every((key) => typeof value[key] === "string")
    && typeof value.line === "number" && Number.isInteger(value.line) && value.line > 0
    && (value.date === null || typeof value.date === "string")
    && Array.isArray(value.matched_record_ids) && value.matched_record_ids.every((id) => typeof id === "string");
}
export function parseAssessmentBatch(value: unknown): AssessmentBatch {
  if (!record(value) || !record(value.statements) || !Array.isArray(value.current_assessments)
    || !Array.isArray(value.revision_impacts) || !value.revision_impacts.every(revisionImpact)) {
    throw new Error("Invalid recorded-assessment report");
  }
  const statements: AssessmentBatch["statements"] = {};
  for (const [id, entries] of Object.entries(value.statements)) {
    if (!Array.isArray(entries) || !entries.every(assessment)) {
      throw new Error(`Invalid recorded assessments for ${id}`);
    }
    statements[id] = entries;
  }
  const current_assessments = value.current_assessments.map((entry: unknown) => {
    if (!currentAssessment(entry) || !("attempt_id" in entry) || typeof entry.attempt_id !== "string") {
      throw new Error("Invalid scoped current assessment");
    }
    return { ...entry, attempt_id: entry.attempt_id };
  });
  return { statements, current_assessments, revision_impacts: value.revision_impacts };
}

/** One bounded batch: no full research brief or evidence graph per premise. */
export function getCaseAssessments(statementIds: string[]): AssessmentBatch {
  return parseAssessmentBatch(truthJson(["brief", "--assessments-for", statementIds.join(",")]));
}

let cachedCase: ReturnType<typeof currentCase> | undefined;

/** Share one projection and assessment batch across the static case pages. */
export function getCurrentCase() {
  if (!cachedCase) {
    const report = getFrontierReport(GOD_EXISTS);
    cachedCase = currentCase({ corpus: getCorpus(), report, dossiers: getDossiers(),
      assessments: getCaseAssessments([...new Set([GOD_EXISTS, ...report.reaching_root_statements])]),
      revision: getBuildInfo().commit });
  }
  return cachedCase;
}
