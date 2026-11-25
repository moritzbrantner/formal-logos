# Audit of unconditional corpus consequences

Continues #497, #1007, #1565, #1926, #1987 and #1989. Initial baseline:
`8a8dcdbed7c2c1501b74c9ae8aa408ec5fa25c26`. Draft research checkpoint; no floor marking, relation, proof,
definition, or closure rule is changed here. No new status registry.

## Question and evidence boundary

Which exact existing propositions follow without disputed substantive
premises, and which additional routes can consume them? The primary inventory
is a computed projection of the canonical records, not a list of accepted
claims. In particular, distinguish:

- a theorem of logic or a definition-relative theorem (including universal
  conditional theorems, not the satisfaction of their antecedents);
- a strictly self-refuting denial in a matched performance, content and domain;
- direct actual or first-person warrant (not a universally quantified theorem);
- a necessary precondition of inquiry, with the actual inquiry identified;
- existing met legacy floor bases, with the basis retained;
- deductive consequences of each explicit basis;
- common ground relative to specified rival commitments;
- epistemic self-undermining without falsity;
- conditional certificates, consistency models and hidden application bridges.

Use the canonical [systematic loop](../systematic-corpus-loop.md), the
[frontier](../../truth/README.md#frontier-and-frontier-diff), the registered
support graph and the existing [orphan audit](orphan-graft-map.md#6-retorsion-graft-audit-1926-1963-1007-1008).
The Rust frontier exposes both `established_statements` and
`closed_statements`: the latter can include consequences of open leaves and
transcriptions; it is not the requested unconditional set. The existing
frontier handles bottom cycles; a separate diagnostic of SCCs may explain
their dependencies but must never seed their members as facts. A positive
implication hyperedge fires only when every required premise has a witness.

## First discriminating results (recorded evidence, not a new review)

- #1987's seven non-counting attacks do not turn warrant failure into falsity.
  In particular, epistemic nihilism's result `ec80b13d` does not establish F6
  `f56b2ee7`. The same-relation incompatibility `146b502b` assumes F6.
- Knowledge retorsion `72288c48` excludes knowing universal ignorance under
  factivity, not the truth of universal ignorance. Do not supply knowledge by
  stipulating it.
- The Cogito route `cc1a4204` needs actual assertion `b45ca9db` and cognitive
  realization `1edfc1d1`. Represented occurrence `46c875b1` needs the
  representation bridge; #1979/#1980 retain actual-world presence and
  concreteness. This is a high-value God-existence connection, not a
  premise-free proof of concrete population.
- The V2 verificationism package `92ad4e06` has the recorded premise-free
  refutation `c93862da`; restricted auxiliaries and other verificationist
  theses are different claims. The V1 package instead relies on weak negation
  closure floor `3f979107`. See the [verificationism showcase](../showcase-verificationism.md).
- A theorem certifying a model's satisfiability proves that formal fact, not the
  actual truth of the model's commitments. A universal conditional can itself
  be logically established while its consequent at an actual witness is open.

## Reproduction and completion boundary

In a prepared checkout, run the existing worker preflight and build, then
`target/release/truth --json frontier --routes` (no `--reaching-root`),
`target/release/truth --json orphans` for the default root and for
`--frontier-root STMT-GOD-EXISTS`. Use the complete statement inventory rather
than limiting the audit to either backward slice. Preserve input identity,
result and argument IDs, precise Lean types and every required premise.
Use the existing support-graph export for focused backward slices and
`truth context`, `truth dossier`, `truth semantics` for application checks.
Compare `established_statements` with met floor bases and a zero-input
least-fixed-point computation, explicitly separating consistency witnesses,
transcriptions and actual application conditions.

The current connector environment can read and write individual GitHub files
but cannot check out the corpus (network DNS fails) or run its Rust/Lean
verification. This initial note is not the exhaustive computation, and no
numerical corpus result or new verified argument is asserted. Complete the
full reproducible projection and semantic review before relying on this
audit for new premise establishment. Independent semantic challenge pending.
