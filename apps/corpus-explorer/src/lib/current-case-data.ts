import { truthJson } from "./truth-cli";
import { currentCase, GOD_EXISTS, type AssessmentBatch, type RecordedAssessment } from "./current-case";
import { getCorpus } from "./corpus";
import { getDossiers } from "./premise-dossier";
import { getBuildInfo, getFrontierReport } from "./site-state";

function record(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
function assessment(value: unknown): value is RecordedAssessment {
  return record(value) && (value.kind === "assessment" || value.kind === "rival_analysis")
    && ["section", "path", "heading", "dated_by", "excerpt"].every((key) => typeof value[key] === "string")
    && typeof value.line === "number" && Number.isInteger(value.line) && value.line > 0
    && (value.date === null || typeof value.date === "string")
    && Array.isArray(value.matched_record_ids) && value.matched_record_ids.every((id) => typeof id === "string");
}
export function parseAssessmentBatch(value: unknown): AssessmentBatch {
  if (!record(value) || !record(value.statements)) {
    throw new Error("Invalid recorded-assessment report");
  }
  const result: AssessmentBatch = {};
  for (const [id, entries] of Object.entries(value.statements)) {
    if (!Array.isArray(entries) || !entries.every(assessment)) {
      throw new Error(`Invalid recorded assessments for ${id}`);
    }
    result[id] = entries;
  }
  return result;
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
