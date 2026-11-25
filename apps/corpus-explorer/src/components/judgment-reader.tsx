"use client";

import Link from "next/link";
import { useState, useSyncExternalStore } from "react";
import type { JudgmentReading } from "../lib/current-judgments";

type Props = {
  readings: JudgmentReading[];
  statementId: string;
  repositoryUrl: string;
  revision: string;
  caseOverview?: boolean;
};

const subscribeToHydration = () => () => {};

export function JudgmentReader({ readings, statementId, repositoryUrl, revision, caseOverview }: Props) {
  const direct = readings.filter(({ current }) => current.statement_ids.includes(statementId));
  const other = readings.filter(({ current }) => !current.statement_ids.includes(statementId));
  // A selection made on the static page before hydration has no change handler.
  const interactive = useSyncExternalStore(subscribeToHydration, () => true, () => false);
  const [choice, setChoice] = useState("");
  const selected = readings.find(({ current }) => current.attempt_id === choice) ?? direct[0] ?? other[0];
  const options = (rows: JudgmentReading[]) => rows.map(({ current }) =>
    <option key={current.attempt_id} value={current.attempt_id}>{current.scope}</option>);
  const current = selected?.current;
  const review = current?.review === "accepted_qualified" ? "Accepted with qualifications" : current?.review.replaceAll("_", " ");
  return <section className="record-section" aria-labelledby="judgment-heading" id="assessments">
    <h2 className="eyebrow" id="judgment-heading">Current research judgments</h2>
    {!direct.length ? <p className="mt-3">No current assessment explicitly covers this proposition.</p> : null}
    {selected && current ? <>
      {readings.length > 1 ? <label className="mt-3 block text-sm">Choose a recorded judgment
        <select className="mt-1 block w-full rounded border border-[var(--line)] bg-[var(--paper)] p-2" disabled={!interactive} value={current.attempt_id} onChange={(event) => setChoice(event.target.value)}>
          {caseOverview ? <>
            {direct.length ? <optgroup label="Scope includes God’s existence">{options(direct)}</optgroup> : null}
            {other.length ? <optgroup label="Scope includes a case premise">{options(other)}</optgroup> : null}
          </> : options(direct)}
        </select>
      </label> : null}
      <h3 className="mt-4 max-w-prose font-serif text-xl">{current.scope}</h3>
      <p className="mt-3 whitespace-pre-wrap leading-7">{current.assessment}</p>
      {selected.blocker ? <p className="mt-3 text-sm"><strong>Blocker recorded in this attempt. </strong>{selected.blocker}</p> : null}
      <h4 className="mt-4 font-medium">Next test</h4>
      <p className="mt-1 whitespace-pre-wrap">{current.next_test}</p>
      <p className="mt-3 text-sm"><a className="link-quiet" href={`${repositoryUrl}/blob/${revision}/${current.note}`}>Research note</a> · <Link className="link-quiet" href={`/attempts/${current.attempt_id}`} title={selected.title}>Attempt and evidence</Link> · {current.date}</p>
      <p className="mt-2 text-sm">{review} · {current.publication} · <a className="link-quiet" href={`${repositoryUrl}/commit/${current.reviewed_revision}`}>{current.review === "unreviewed" ? "proposed revision" : "reviewed revision"} {current.reviewed_revision.slice(0, 9)}</a></p>
      <p className="mt-1 text-sm">{current.evidence}</p>
      <p className="mt-2 text-sm"><strong>Earlier assessment. </strong>{current.supersedes}</p>
      <h4 className="mt-3 text-sm font-medium">Propositions in this assessment</h4>
      <ul className="ml-5 list-disc text-sm">{selected.propositions.map((link) => <li key={link.id}><Link className="link-quiet" href={link.href}>{link.label}</Link></li>)}</ul>
      {selected.routeGroups?.length ? <>
        <h4 className="mt-4 font-medium">Where these premises enter the case</h4>
        <p className="mt-1 text-sm">Each route listed has a registered argument path through the named premise. Open the route for its other inputs and support options.</p>
        {selected.routeGroups.map((group) => <div className="mt-3 text-sm" key={group.propositionIds[0]}>
          <p className="font-medium">{selected.propositions.filter((p) => group.propositionIds.includes(p.id)).map((p, index) =>
            <span key={p.id}>{index > 0 ? " · " : ""}<Link className="link-quiet" href={p.href}>{p.label}</Link></span>)}</p>
          <ul className="ml-5 list-disc">{group.routes.map((link) => <li key={link.id}><Link className="link-quiet" href={link.href}>{link.label}</Link></li>)}</ul>
        </div>)}
      </> : null}
    </> : null}
  </section>;
}
