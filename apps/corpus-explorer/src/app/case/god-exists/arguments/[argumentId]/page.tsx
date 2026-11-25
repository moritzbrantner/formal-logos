import Link from "next/link";
import { notFound } from "next/navigation";
import { Suspense } from "react";
import { findArgument, getCorpus } from "@/lib/corpus";
import { caseArgumentHref, casePremiseHref, GOD_EXISTS } from "@/lib/current-case";
import { getCurrentCase } from "@/lib/current-case-data";
import { getFrontierReport, resultKind, sourceUrl } from "@/lib/site-state";
import { getArgumentSynthesis } from "./argument-synthesis";
import PremiseComparison, { ComparisonOutcome } from "./premise-comparison";

export function generateStaticParams() {
  return getCurrentCase().routes
    .filter(({ status }) => status === "verified")
    .map(({ id }) => ({ argumentId: id }));
}

export default async function ArgumentPage({ params }: { params: Promise<{ argumentId: string }> }) {
  const { argumentId } = await params;
  const view = getCurrentCase();
  const verifiedRoutes = new Set(view.routes.filter(({ status }) => status === "verified").map(({ id }) => id));
  if (!verifiedRoutes.has(argumentId)) {
    notFound();
  }

  const { scope, argument, inputs, results, comparisons, baseline } = getArgumentSynthesis(argumentId, GOD_EXISTS);
  const scopedPremises = new Set(view.premises.map(({ statement }) => statement.id));
  const statementHref = (id: string) => scopedPremises.has(id) ? casePremiseHref(id) : `/statements/${id}`;
  const statements = Object.fromEntries(inputs.map(({ id, label, paraphrase }) => [
    id, { label: label || paraphrase || id, href: statementHref(id) },
  ]));
  const usedArguments = new Set([baseline, ...comparisons].flatMap(({ supporting_arguments, derivation }) => [
    ...supporting_arguments, ...derivation,
  ]));
  const corpus = getCorpus();
  const frontier = getFrontierReport(GOD_EXISTS);
  const evidence = Object.fromEntries([...usedArguments].map((id) => {
    const entry = findArgument(corpus, id);
    if (!entry) {
      throw new Error(`Missing supporting argument ${id}`);
    }
    const registered = corpus.results.filter((candidate) => candidate.argument_id === id);
    const result = registered.find((candidate) => resultKind(frontier, candidate.id).kind === "derivation") ?? registered[0];
    const href = verifiedRoutes.has(id) && id !== argumentId
      ? caseArgumentHref(id)
      : result ? `/results/${result.id}#lean-evidence` : sourceUrl(`corpus/arguments/${id}.json`);
    return [id, { label: entry.label ?? id, href }];
  }));
  const comparisonContext = { argumentId, evidence, statements };

  return (
    <article className="max-w-5xl [overflow-wrap:anywhere]">
      <Link className="link-quiet text-sm" href={`/case/god-exists#argument-${argumentId}`}>Support routes for God’s existence</Link>
      <h1 className="mt-6 font-serif text-4xl">{argument.label || argumentId}</h1>
      <p className="mt-4 whitespace-pre-line">{argument.meaning}</p>
      <p className="mt-3">
        <strong>Conclusion. </strong>
        <Link className="link-quiet" href={`/statements/${argument.conclusion_statement_id}`}>{view.target.paraphrase}</Link>
        {" "}· <Link className="link-quiet" href={`/definitions/${view.sense.id}`}>GOD_4 definition</Link>
      </p>
      <p className="mt-3 text-sm text-[var(--muted)]">
        {view.established
          ? "The conclusion is established under the recorded closure rules."
          : "The conclusion remains open under the recorded closure rules."}
        {" "}The comparison below assumes the retained inputs for this test.
      </p>

      <section className="record-section" aria-labelledby="argument-premises">
        <div className="grid items-start gap-6 lg:grid-cols-2">
          <div>
            <h2 id="argument-premises" className="font-serif text-2xl">Explicit premises and commitments</h2>
            <ul className="premise-list mt-4">
              {inputs.map(({ id, paraphrase, role }) => (
                <li key={`${role}:${id}`}>
                  <p className="text-xs font-medium capitalize text-[var(--muted)]">{role}</p>
                  <Link className="link-quiet" href={statements[id].href}>{paraphrase || statements[id].label}</Link>
                </li>
              ))}
            </ul>
            {inputs.length === 0 ? <p className="mt-3">This argument has no registered inputs.</p> : null}
          </div>
          <div className="min-w-0 border border-[var(--line)] bg-[var(--callout)] px-4 py-5 sm:px-6">
            <h2 className="font-serif text-2xl">What follows if one input is withheld?</h2>
            <p className="mt-2 text-sm text-[var(--muted)]">{scope}</p>
            <Suspense fallback={<ComparisonOutcome comparison={baseline} {...comparisonContext} />}>
              <PremiseComparison baseline={baseline} comparisons={comparisons} {...comparisonContext} />
            </Suspense>
          </div>
        </div>
      </section>

      <section className="record-section" id="lean-evidence">
        <h2 className="font-serif text-2xl">Lean evidence</h2>
        {results.map(({ id, theorem, advertised_statement, challenge_path, solution_path }) => (
          <div className="mt-5" key={id}>
            <Link className="link-quiet font-mono text-sm" href={`/results/${id}#lean-evidence`}>{theorem}</Link>
            {advertised_statement ? <pre className="lean-snippet">{advertised_statement.statement}</pre> : null}
            <p className="mt-3 flex flex-wrap gap-4 text-sm">
              {challenge_path ? <a className="link-quiet" href={sourceUrl(challenge_path, advertised_statement?.line)}>Challenge source</a> : null}
              {solution_path ? <a className="link-quiet" href={sourceUrl(solution_path)}>Solution source</a> : null}
            </p>
          </div>
        ))}
      </section>
    </article>
  );
}
