/** The authored fields of an attempt's scoped current_assessment. */
export type CurrentAssessment = {
  statement_ids: string[];
  date: string;
  scope: string;
  assessment: string;
  next_test: string;
  note: string;
  review: "accepted_qualified" | "changes_requested" | "unreviewed";
  publication: "published" | "unpublished" | "merged";
  reviewed_revision: string;
  evidence: string;
  supersedes: string;
};

export type ScopedAssessment = CurrentAssessment & { attempt_id: string };
export type RevisionConsumer = { consumer: string; tier: string; disposition: string; reason: string | null };
export type RevisionImpact = {
  attempt_id: string;
  change: { kind: string; revision: string; statement_ids: string[]; reason: string; previous: string };
  consumers: RevisionConsumer[];
};

export function record(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
export function stringList(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((item) => typeof item === "string");
}
export function currentAssessment(value: unknown): value is CurrentAssessment {
  return record(value) && stringList(value.statement_ids) && value.statement_ids.length > 0
    && ["date", "scope", "assessment", "next_test", "note", "reviewed_revision", "evidence", "supersedes"].every((key) => typeof value[key] === "string")
    && (value.review === "accepted_qualified" || value.review === "changes_requested" || value.review === "unreviewed")
    && (value.publication === "merged" || value.publication === "published" || value.publication === "unpublished");
}
export function revisionImpact(value: unknown): value is RevisionImpact {
  if (!record(value) || typeof value.attempt_id !== "string" || !record(value.change) || !Array.isArray(value.consumers)) return false;
  const change = value.change;
  return stringList(change.statement_ids) && ["kind", "revision", "reason", "previous"].every((key) => typeof change[key] === "string")
    && value.consumers.every((consumer: unknown) => record(consumer) && typeof consumer.consumer === "string"
      && typeof consumer.tier === "string" && typeof consumer.disposition === "string" && (consumer.reason === null || typeof consumer.reason === "string"));
}

export type ReadingLink = { id: string; label: string; href: string };
export type JudgmentReading = {
  current: ScopedAssessment;
  title: string;
  propositions: ReadingLink[];
  routeGroups?: { propositionIds: string[]; routes: ReadingLink[] }[];
  blocker?: string;
};
