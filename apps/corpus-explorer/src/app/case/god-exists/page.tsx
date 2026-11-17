import Link from "next/link";
import { treeHref } from "@/lib/argument-tree";
import { getCorpus } from "@/lib/corpus";
import { currentCase, GOD_EXISTS } from "@/lib/current-case";
import { getCaseAssessments } from "@/lib/current-case-data";
import { getDossiers } from "@/lib/premise-dossier";
import { getBuildInfo, getFrontierReport, sourceUrl } from "@/lib/site-state";

export default function GodExistsPage() {
  const corpus = getCorpus();
  const report = getFrontierReport(GOD_EXISTS);
  const view = currentCase({ corpus, report, dossiers: getDossiers(),
    assessments: getCaseAssessments([...new Set([GOD_EXISTS, ...report.reaching_root_statements])]),
    revision: getBuildInfo().commit });
  const names = new Map([...corpus.statements.map((statement) => [statement.id, statement.label ?? statement.paraphrase] as const),
    ...corpus.arguments.map((argument) => [argument.id, argument.label ?? argument.id] as const)]);
  const statementLink = (id: string) => <Link className="link-quiet" href={`/statements/${id}`}>{names.get(id) ?? id}</Link>;
  const bundleView = (bundle: (typeof view.bundles)[number]) => <li key={bundle.id} className="mt-4">
    <p className="font-medium">{bundle.label ?? bundle.id}</p>
    <p className="text-sm">{bundle.status === "verified" ? "Verified conditional derivation" : bundle.status === "transcription" ? "Transcription only" : "Verification required"}</p>
    <p className="mt-2 whitespace-pre-wrap text-sm">{bundle.meaning}</p>
    <p className="mt-2">All premises required together:</p>
    <ul className="ml-5 list-disc">{bundle.premise_statement_ids.map((id) => <li key={id}>{statementLink(id)}</li>)}</ul>
    {!bundle.premise_statement_ids.length ? <p>No premises recorded.</p> : null}
    <p className="mt-2 text-sm">{bundle.resultIds.map((id) => <Link key={id} className="link-quiet mr-4" href={`/results/${id}`}>Result {id}</Link>)}</p>
    {bundle.openLeaves ? <details className="mt-2"><summary>Expanded open premises ({bundle.openLeaves.length})</summary>
      <ul className="ml-5 list-disc">{bundle.openLeaves.map((id) => <li key={id}>{statementLink(id)}</li>)}</ul>
    </details> : null}
  </li>;
  return <article className="max-w-5xl [overflow-wrap:anywhere]">
    <h1 className="font-serif text-4xl">The current case for God’s existence</h1>
    <p className="mt-4 text-xl">{view.target.paraphrase}</p>
    <p className="mt-3">{statementLink(view.target.id)} · <code>{view.target.id}</code></p>
    <p className="mt-3 text-sm">Revision <a className="link-quiet" href={`${getBuildInfo().repositoryUrl}/commit/${view.revision}`}>{view.revision}</a></p>
    <section className="record-section">
      <h2 className="eyebrow">Selected meaning and current conclusion</h2>
      <p className="mt-3 whitespace-pre-wrap">{view.sense.definition}</p>
      <p className="mt-3"><Link className="link-quiet" href={`/definitions/${view.sense.id}`}>GOD_4 definition · {view.sense.id}</Link> · <a className="link-quiet" href={sourceUrl("corpus/disambiguations/god.json")}>Sense distinctions</a></p>
      <p className="mt-3">{view.established ? "Established under the recorded closure rules." : "God’s existence is not established under the recorded closure rules."} Conditional derivations establish their conclusions only under their premises.</p>
      <p className="mt-3">Recorded assessments below are excerpts from research notes. They are not a synthesized or endorsed overall judgment. Where none is retrieved, the assessment is unknown; that absence says nothing about the premise’s warrant.</p>
      <p className="mt-3">This case follows support for God’s existence. Historical evidence and specifically Christian or Catholic identification remain deferred.</p>
    </section>
    <section className="record-section" id="support-routes">
      <h2 className="eyebrow">Support routes</h2>
      <p className="mt-3">Directly assuming the target remains an explicit option, alongside these conditional routes. Every displayed bundle requires all its premises. Order is by record identifier, with no ranking of philosophical strength by premise counts, cost, source counts or dates.</p>
      <ul>{view.routes.map(bundleView)}</ul>
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Premises and connections</h2>
      <p className="mt-3">Ordered by the number of uses in this case to help locate shared premises. Graph centrality is not philosophical warrant. Each path shows one connection back to God’s existence; the bundles retain all connections.</p>
      {view.premises.map((premise) => <details key={premise.statement.id} className="mt-4 border-t border-[var(--line)] pt-3" id={`premise-${premise.statement.id}`}>
        <summary>{premise.statement.paraphrase} · {premise.usedBy.length} uses</summary>
        <p className="mt-3">{statementLink(premise.statement.id)} · {premise.established ? "Established" : "Not established"} · {report.statement_statuses[premise.statement.id] ?? "Status unknown"}</p>
        <p className="mt-2">{premise.directAssumption ? "Direct-assumption option available." : "No direct-assumption option reported."} {premise.assessments.length ? "Recorded assessments linked below." : "Recorded assessment: unknown."}</p>
        {premise.path ? <ol className="mt-2 ml-5 list-decimal">{premise.path.map((id, index) => <li key={`${id}-${index}`}>{names.get(id) ?? id} <code className="text-xs">{id}</code></li>)}</ol> : <p>No path reported for this proposition.</p>}
        <ul>{premise.statement.id === GOD_EXISTS ? <li><a className="link-quiet" href="#support-routes">All routes to God’s existence</a></li> : premise.bundles.map(bundleView)}</ul>
        {premise.alternatives.length ? <details className="mt-3"><summary>All expanded verified support options ({premise.alternatives.length})</summary>
          <ul>{premise.alternatives.map((bundle, index) => <li key={index} className="mt-3"><p>Premises required together:</p><ul className="ml-5 list-disc">{bundle.premise_statement_ids.map((id) => <li key={id}>{statementLink(id)}</li>)}</ul>
            <p className="text-sm">Arguments: {bundle.argument_ids.join(", ")}</p><p>{bundle.result_ids.map((id) => <Link className="link-quiet mr-3" key={id} href={`/results/${id}`}>Result {id}</Link>)}</p></li>)}</ul>
        </details> : null}
        <p className="mt-3"><Link className="link-quiet" href={`/dossiers/${premise.statement.id}`}>Full research dossier, evidence and comparisons</Link> · <Link className="link-quiet" href={treeHref(premise.statement.id)}>Explore connections</Link></p>
        <h3 className="mt-4 font-medium">Recorded objections and rivals</h3>
        {premise.objections.length ? <ul>{premise.objections.map((objection) => <li key={objection.id} className="mt-2"><p>{objection.predicate === "attacks" ? "Objection" : "Alternative"}: {names.get(objection.subject_id) ?? objection.subject_id}</p><p>{objection.note ?? objection.basis ?? "See the linked dossier for the recorded objection."}</p></li>)}</ul> : <p>No objection or rival relation recorded here. This is not a proof of absence.</p>}
        <h3 className="mt-4 font-medium">Recorded findings, blockers and next tests</h3>
        {premise.attempts.length ? <ul>{premise.attempts.map((attempt) => <li className="mt-2" key={attempt.id}><a className="link-quiet" href={`#finding-${attempt.id}`}>{attempt.kind} · {attempt.outcome} · {attempt.date}</a></li>)}</ul> : <p>No research attempt retrieved. See the full dossier for evidence and open questions.</p>}
      </details>)}
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Recorded findings and remaining work</h2>
      {view.attempts.map((attempt) => <details className="mt-4" key={attempt.id} id={`finding-${attempt.id}`}>
        <summary>{attempt.kind} · {attempt.outcome} · {attempt.date}</summary>
        <p className="mt-3 whitespace-pre-wrap">{attempt.summary}</p>
        {attempt.blocker ? <p className="mt-2 whitespace-pre-wrap">Blocker: {attempt.blocker}</p> : null}
        <Link className="link-quiet" href={`/attempts/${attempt.id}`}>Full finding, evidence and next tests</Link>
      </details>)}
      {!view.attempts.length ? <p className="mt-3">No research attempts retrieved.</p> : null}
    </section>
    <section className="record-section" id="assessments">
      <h2 className="eyebrow">Recorded assessments and rival analysis</h2>
      <p className="mt-3">Separate records remain separate, including competing judgments. A note mentioning a proposition or its argument supplies context; its excerpt need not assess every linked proposition. Follow the cited section for the full reasons, objections and revision conditions. Dates do not rank warrant.</p>
      {view.assessments.length ? view.assessments.map(({ assessment, statementIds }) => <details className="mt-4" key={`${assessment.section}:${assessment.line}`}>
        <summary>{assessment.heading} · {assessment.kind === "assessment" ? "Recorded assessment" : "Rival analysis"}</summary>
        <blockquote className="mt-3 whitespace-pre-wrap border-l border-[var(--line)] pl-4">{assessment.excerpt}</blockquote>
        <p className="mt-2 text-sm"><a className="link-quiet" href={sourceUrl(assessment.path, assessment.line)}>{assessment.section}, line {assessment.line}</a> · {assessment.date ?? "Undated"} ({assessment.dated_by})</p>
        <p className="text-sm">Explicitly mentioned records: {assessment.matched_record_ids.join(", ")}</p>
        <details className="mt-2"><summary>Related propositions in this case ({statementIds.length})</summary><ul>{statementIds.map((id) => <li key={id}><a className="link-quiet" href={`#premise-${id}`}>{names.get(id) ?? id}</a></li>)}</ul></details>
      </details>) : <p className="mt-3">Recorded assessment: unknown. No matching assessment excerpt retrieved.</p>}
    </section>
    <section className="record-section">
      <h2 className="eyebrow">Bridges to divine attributes</h2>
      <p className="mt-3">Attribute conditionals do not assert that God exists. Their witnesses, assumptions and missing bridges must be checked separately.</p>
      <ul className="mt-3">{view.attributes.map((attribute) => <li className="mt-2" key={attribute.id}>{statementLink(attribute.id)} · <Link className="link-quiet" href={`/dossiers/${attribute.id}`}>Bridge details</Link></li>)}</ul>
    </section>
  </article>;
}
