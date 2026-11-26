"use client";

import Link from "next/link";
import { useSearchParams } from "next/navigation";
import type { Comparison } from "./argument-synthesis";

type EvidenceLink = { label: string; href: string };

type ComparisonContext = {
  argumentId: string;
  evidence: Record<string, EvidenceLink>;
  statements: Record<string, EvidenceLink>;
};

export function ComparisonOutcome({ comparison, argumentId, evidence, statements }: ComparisonContext & {
  comparison: Comparison;
}) {
  const alternatives = comparison.supporting_arguments.filter((id) => id !== argumentId);
  const statementList = (ids: string[]) => (
    <ul className="ml-5 list-disc">
      {ids.map((id) => <li key={id}><Link className="link-quiet" href={statements[id].href}>{statements[id].label}</Link></li>)}
    </ul>
  );
  const argumentLink = (id: string) => <Link className="link-quiet" href={evidence[id].href}>{evidence[id].label}</Link>;

  return (
    <div className="mt-4">
      <p role="status" className="font-medium">
        {comparison.reachable ? "A registered argument reaches the conclusion from the retained inputs." : "No registered argument reaches the conclusion from the retained inputs."}
      </p>
      <p className="mt-2">
        {comparison.selected_applicable ? "The selected argument can be applied." : "The selected argument is missing one or more required inputs."}
      </p>
      {comparison.missing_selected_inputs.length ? (
        <div className="mt-2">
          <p>Required inputs still unavailable</p>
          {statementList(comparison.missing_selected_inputs)}
        </div>
      ) : null}
      {comparison.recovered_inputs.length ? (
        <div className="mt-2">
          <p>Withheld inputs derived from the retained inputs</p>
          {statementList(comparison.recovered_inputs)}
        </div>
      ) : null}
      {alternatives.length ? (
        <div className="mt-3">
          <p>Other arguments that can reach the conclusion</p>
          <ul className="ml-5 list-disc">
            {alternatives.map((id) => <li key={id}>{argumentLink(id)}</li>)}
          </ul>
        </div>
      ) : null}
      {comparison.derivation.length ? (
        <details className="mt-3">
          <summary className="cursor-pointer font-medium">One derivation in dependency order</summary>
          <ol aria-label="Derivation steps" className="mt-2 ml-5 list-decimal">
            {comparison.derivation.map((id) => <li key={id}>{argumentLink(id)}</li>)}
          </ol>
        </details>
      ) : null}
    </div>
  );
}

export default function PremiseComparison({ baseline, comparisons, ...context }: ComparisonContext & {
  baseline: Comparison;
  comparisons: Comparison[];
}) {
  const without = useSearchParams().get("without");
  const comparison = comparisons.find(({ withheld }) => withheld[0] === without);
  const selected = comparison?.withheld[0] ?? "";

  return (
    <>
      <label className="mt-4 block text-sm font-medium" htmlFor="withhold-premise">Withhold one input</label>
      <select
        className="mt-1 min-h-11 w-full border border-[var(--line-strong)] bg-[var(--paper)] px-2 text-sm"
        id="withhold-premise"
        value={selected}
        onChange={({ currentTarget }) => {
          const url = new URL(window.location.href);
          if (currentTarget.value) {
            url.searchParams.set("without", currentTarget.value);
          } else {
            url.searchParams.delete("without");
          }
          window.history.pushState(null, "", url);
        }}
      >
        <option value="">Keep all inputs</option>
        {Object.entries(context.statements).map(([id, { label }]) => <option key={id} value={id}>{label}</option>)}
      </select>
      {without && !comparison ? <p className="mt-2 text-sm">Unknown input in the link. Showing the result with all inputs retained.</p> : null}
      <ComparisonOutcome comparison={comparison ?? baseline} {...context} />
    </>
  );
}
