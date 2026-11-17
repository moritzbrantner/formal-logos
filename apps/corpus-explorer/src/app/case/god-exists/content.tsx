import Link from "next/link";
import { treeHref } from "@/lib/argument-tree";
import { casePremiseHref, type currentCase } from "@/lib/current-case";
import { getBuildInfo, sourceUrl } from "@/lib/site-state";

type Case = ReturnType<typeof currentCase>;
type Premise = Case["premises"][number];

function namesFor(view: Case) {
  return new Map([
    ...view.premises.map(({ statement }) => [statement.id, statement.label ?? statement.paraphrase] as const),
    ...view.attributes.map((statement) => [statement.id, statement.label ?? statement.paraphrase] as const),
    ...view.bundles.map((bundle) => [bundle.id, bundle.label ?? bundle.id] as const),
  ]);
}
function StatementLink({ id, names }: { id: string; names: Map<string, string> }) {
  return <Link className="link-quiet" href={`/statements/${id}`}>{names.get(id) ?? id}</Link>;
}
function Bundles({ bundles, names }: { bundles: Case["bundles"]; names: Map<string, string> }) {
  return <ul>{bundles.map((bundle) => <li key={bundle.id} className="mt-5" id={`argument-${bundle.id}`}>
    <h3 className="font-medium">{bundle.label ?? bundle.id}</h3>
    <p className="text-sm">{bundle.status === "verified" ? "Verified conditional derivation" : bundle.status === "transcription" ? "Transcription only" : "Verification required"}</p>
    <p className="mt-2">All premises required together:</p>
    <ul className="ml-5 list-disc">{bundle.premise_statement_ids.map((id) => <li key={id}>
      <Link className="link-quiet" href={casePremiseHref(id)}>{names.get(id) ?? id}</Link>
    </li>)}</ul>
    {!bundle.premise_statement_ids.length ? <p>No premises recorded.</p> : null}
    <p className="mt-2 text-sm">{bundle.resultIds.map((id) => <Link key={id} className="link-quiet mr-4" href={`/results/${id}`}>Result {id}</Link>)}</p>
    <Link className="link-quiet text-sm" href={`${casePremiseHref(bundle.conclusion_statement_id)}#argument-${bundle.id}`}>Argument context and expanded support</Link>
  </li>)}</ul>;
}
function Revision({ revision }: { revision: string }) {
  return <p className="mt-3 text-sm">Revision <a className="link-quiet" href={`${getBuildInfo().repositoryUrl}/commit/${revision}`}>{revision}</a></p>;
}
function Assumption({ premise }: { premise: Premise }) {
  return <>{premise.directAssumption ? "Direct-assumption option available." : "No direct-assumption option reported."}</>;
}

export function CaseOverview({ view }: { view: Case }) {
  const names = namesFor(view);
  const target = view.premises.find((premise) => premise.statement.id === view.target.id);
  return <article className="max-w-5xl [overflow-wrap:anywhere]">
    <h1 className="font-serif text-4xl">The current case for God’s existence</h1>
    <p className="mt-4 text-xl">{view.target.paraphrase}</p>
    <p className="mt-3"><StatementLink id={view.target.id} names={names} /> · <code>{view.target.id}</code></p>
    <Revision revision={view.revision} />
    <section className="record-section">
      <h2 className="eyebrow">Selected meaning and current conclusion</h2>
      <p className="mt-3">{view.sense.definition}</p>
      <p className="mt-3"><Link className="link-quiet" href={`/definitions/${view.sense.id}`}>GOD_4 definition · {view.sense.id}</Link> · <a className="link-quiet" href={sourceUrl("corpus/disambiguations/god.json")}>Sense distinctions</a></p>
      <p className="mt-3">{view.established ? "Established under the recorded closure rules." : "God’s existence is not established under the recorded closure rules."} Conditional derivations establish their conclusions only under their premises.</p>
      <p className="mt-3">Historical evidence and specifically Christian or Catholic identification remain deferred.</p>
      <p className="mt-3">{target?.assessments.length ? `${target.assessments.length} recorded assessment excerpts are available.` : "Recorded assessment: unknown."} <Link className="link-quiet" href={`${casePremiseHref(view.target.id)}#assessments`}>Read assessments and rival analysis</Link>. These are separate research records, not a synthesized or endorsed overall judgment.</p>
    </section>
    <section className="record-section" id="support-routes">
      <h2 className="eyebrow">Support routes</h2>
      <p className="mt-3">Directly assuming the target remains an explicit option alongside every conditional route below. Each bundle requires all its premises. Record order does not rank philosophical strength by cost, premise counts, source counts or dates.</p>
      <Bundles bundles={view.routes} names={names} />
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Premises and connections</h2>
      <p className="mt-3">Every proposition in this case is linked below, with its complete support options, path to God’s existence, assessments and evidence. Order follows uses in this case; graph centrality is not philosophical warrant.</p>
      <ul className="mt-4">{view.premises.map((premise) => <li key={premise.statement.id} className="mt-3" id={`premise-${premise.statement.id}`}>
        <Link className="link-quiet" href={casePremiseHref(premise.statement.id)}>{premise.statement.label ?? premise.statement.paraphrase}</Link>
        <p className="text-sm text-[var(--muted)]">{premise.usedBy.length} uses · {premise.established ? "Established" : "Not established"} · <Assumption premise={premise} /> · {premise.assessments.length ? "Recorded assessments available" : "Recorded assessment: unknown"}</p>
      </li>)}</ul>
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Bridges to divine attributes</h2>
      <p className="mt-3">Attribute conditionals do not assert that God exists. Check their witnesses, assumptions and missing bridges separately.</p>
      <ul>{view.attributes.map((attribute) => <li className="mt-2" key={attribute.id}><StatementLink id={attribute.id} names={names} /> · <Link className="link-quiet" href={`/dossiers/${attribute.id}`}>Bridge details</Link></li>)}</ul>
    </section>
  </article>;
}

export function CasePremiseDetail({ view, premise }: { view: Case; premise: Premise }) {
  const names = namesFor(view);
  return <article className="max-w-5xl [overflow-wrap:anywhere]">
    <Link className="link-quiet" href={`/case/god-exists#premise-${premise.statement.id}`}>Current case for God’s existence</Link>
    <h1 className="mt-6 font-serif text-3xl">{premise.statement.paraphrase}</h1>
    <p className="mt-3"><StatementLink id={premise.statement.id} names={names} /> · <code>{premise.statement.id}</code></p>
    <Revision revision={view.revision} />
    <p className="mt-3">{premise.established ? "Established" : "Not established"} under the recorded closure rules. <Assumption premise={premise} /> Conditional derivations remain conditional on their premises.</p>
    <p className="mt-3"><Link className="link-quiet" href={`/dossiers/${premise.statement.id}`}>Full research dossier: sources, findings, objections, blockers and next tests</Link> · <Link className="link-quiet" href={treeHref(premise.statement.id)}>Explore connections</Link></p>
    <section className="record-section">
      <h2 className="eyebrow">Connection to God’s existence</h2>
      <p className="mt-3">One exact path in the God-existence case; shared uses are listed separately. These connections do not rank warrant.</p>
      {premise.path ? <ol className="mt-3 ml-5 list-decimal">{premise.path.map((id, index) => <li key={`${id}-${index}`}>{names.get(id) ?? id} <code className="text-xs">{id}</code></li>)}</ol> : <p>No path reported for this proposition.</p>}
      <ul className="mt-3">{premise.usedBy.map((id) => {
        const bundle = view.bundles.find((entry) => entry.id === id);
        return bundle ? <li key={id}><Link className="link-quiet" href={`${casePremiseHref(bundle.conclusion_statement_id)}#argument-${id}`}>{bundle.label ?? id}</Link></li> : null;
      })}</ul>
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Complete immediate support bundles</h2>
      <Bundles bundles={premise.bundles} names={names} />
      {!premise.bundles.length ? <p className="mt-3">No argument concludes this proposition in the current case.</p> : null}
    </section>
    {premise.bundles.some((bundle) => bundle.openLeaves !== null) ? <section className="record-section">
      <h2 className="eyebrow">Expanded open premises on routes to God’s existence</h2>
      <ul>{premise.bundles.filter((bundle) => bundle.openLeaves !== null).map((bundle) => <li className="mt-4" key={bundle.id}>
        <h3 className="font-medium">{bundle.label ?? bundle.id}</h3>
        <ul className="ml-5 list-disc">{bundle.openLeaves?.map((id) => <li key={id}><Link className="link-quiet" href={casePremiseHref(id)}>{names.get(id) ?? id}</Link></li>)}</ul>
      </li>)}</ul>
    </section> : null}
    <section className="record-section">
      <h2 className="eyebrow">All expanded verified support options</h2>
      <p className="mt-3">Each option requires all its listed premises together. The direct-assumption option remains separate.</p>
      <ul>{premise.alternatives.map((bundle, index) => <li className="mt-4" key={index}>
        <ul className="ml-5 list-disc">{bundle.premise_statement_ids.map((id) => <li key={id}><Link className="link-quiet" href={casePremiseHref(id)}>{names.get(id) ?? id}</Link></li>)}</ul>
        <p className="text-sm">Arguments: {bundle.argument_ids.join(", ")}</p>
        <p>{bundle.result_ids.map((id) => <Link className="link-quiet mr-3" href={`/results/${id}`} key={id}>Result {id}</Link>)}</p>
      </li>)}</ul>
      {!premise.alternatives.length ? <p className="mt-3">No expanded verified alternative reported.</p> : null}
    </section>
    <section className="record-section" id="assessments">
      <h2 className="eyebrow">Recorded assessments and rival analysis</h2>
      <p className="mt-3">Separate records remain separate, including competing judgments. A note mentioning this proposition or its argument supplies context; an excerpt need not assess every mentioned proposition. These are not synthesized or endorsed judgments. Follow the cited section for full reasons, objections and revision conditions. Dates do not rank warrant.</p>
      {premise.assessments.map((assessment) => <div className="mt-4" key={`${assessment.section}:${assessment.line}`}>
        <h3 className="font-medium">{assessment.heading} · {assessment.kind === "assessment" ? "Recorded assessment" : "Rival analysis"}</h3>
        <blockquote className="mt-2 whitespace-pre-wrap border-l border-[var(--line)] pl-4">{assessment.excerpt}</blockquote>
        <p className="mt-2 text-sm"><a className="link-quiet" href={sourceUrl(assessment.path, assessment.line)}>{assessment.section}, line {assessment.line}</a> · {assessment.date ?? "Undated"} ({assessment.dated_by})</p>
        <p className="text-sm">Explicitly mentioned records: {assessment.matched_record_ids.join(", ")}</p>
      </div>)}
      {!premise.assessments.length ? <p className="mt-3">Recorded assessment: unknown. No matching excerpt retrieved; that absence says nothing about warrant.</p> : null}
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Recorded findings and objections</h2>
      <p className="mt-3"><Link className="link-quiet" href={`/dossiers/${premise.statement.id}#dossier-rivals`}>All recorded objections and rivals</Link></p>
      <ul>{premise.attempts.map((attempt) => <li className="mt-2" key={attempt.id}><Link className="link-quiet" href={`/attempts/${attempt.id}`}>{attempt.kind} · {attempt.outcome} · {attempt.date} · {attempt.id}</Link></li>)}</ul>
      {!premise.attempts.length ? <p className="mt-3">No research attempt retrieved. The dossier links the existing evidence and open questions.</p> : null}
    </section>
  </article>;
}
