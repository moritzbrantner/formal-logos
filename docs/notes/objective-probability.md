# Objective probability laws at the will step (#2151)

Program #2145, will step (`66aecdd7` STMT-GOD-HAS-WILL, `4be0f774` operative
plan, same-witness intellect `29818edd`). Question: can a necessary or
impersonal source fix a quantitative chance law, and does the contingent-fact
PSR demand a reason for the law? Analyst formulations, attribution deferred.

[Research attempt](../../corpus/attempts/cf82ce06-6a8a-4dc1-9b0d-582e2036c993.json)
· spec `specs/objective-probability.toml` · Lean
`TruthCore.Explanation.ObjectiveProbability`. The shared binary law is
`TruthCore.Explanation.BinaryLaw.binaryLaw` (#2144); its quantitative
completion of the will-versus-chance rival lives in
[will-versus-chance.md](will-versus-chance.md#quantitative-grounding-of-the-chance-rival-2026-11-27)
and is not repeated here.

This PR delivers the "Probability-law slice" of the #2145 issue comment of
2026-11-27 09:06, with the deferrals listed at the end.

## Fixed meanings

- A **law** is a Mathlib `PMF` on physical outcomes. It is mathematical data,
  not a causal power, and not a probability over metaphysical worlds. Zero mass
  is not impossibility.
- **Invariance** under a set `G` of permutations: `μ (g x) = μ x` for every
  `g ∈ G`. **Transitive**: `G` carries every outcome to every outcome.
- **Stationary** for a kernel `K`: `μ.bind K = μ`.
- **Tracks value**: a fact `f` of a `PSRStrength.Arena` holds at `w` exactly
  when a selected value (a law, or a selector's adopted content) at `w` equals
  its value at the actual world `a`. **Fixes value**: wherever a reason holds at
  an accessible world, the value is the actual one; determination of a law,
  not necessitation of its outcomes.
- **Realized outputs** is #462's `RealizedOutputs`: outputs of performed acts
  are causal edges of the source.

## Results

### 1. Determination controls (`lawDeterminationControls`)

- **Transitive symmetry fixes one law.** For finite nonempty `E` and a
  transitive `G`, exactly one `PMF E` is `G`-invariant; every mass is
  `(card E)⁻¹`. This generalizes #2144's binary exchange-symmetry control.
- **Two orbits leave the orbit mass free.** On `Bool × Bool` the group
  `{id, flip second coordinate}` is not transitive. For every positive `p, q`
  with `p + q = 1`, mass `p/2` on each point of the first orbit and `q/2` on the
  other is invariant with full support, and different `p` give different laws.
- **Binary stationarity.** For a kernel on `Bool` with real switching masses
  `a = K(true)(false)`, `b = K(false)(true)` and `x = μ(true)`: `μ` is stationary
  iff `x (a + b) = b`. With `a + b > 0` there is exactly one stationary law;
  with `a + b = 0` every law is stationary. The balance equation is stated in
  the kernel's own masses, so `b/(a+b)` is fixed only once the kernel is
  given. A kernel is itself a quantitative law: stationarity relocates the law
  question to the kernel rather than answering it. Controls: the identity kernel has
  two distinct stationary laws; the reset kernel's only stationary law is the
  point mass at `true`; the flip kernel has a unique stationary law.
- **Uniqueness is not convergence.** Under the flip kernel the orbit of the
  point mass at `true` alternates with period two, and no iterate is stationary.
  (No topology is placed on `PMF`, so no convergence claim is made beyond this.)
- **Mixtures.** A `PMF.bind` mixture of invariant components is invariant.
  When the two binary components differ in their `true` mass, the mixture is
  injective in its upper law. When the components are equal, every upper law
  gives the same mixture (`bind_const`), so the upper law is idle unless
  something else constrains it. The slice's worked case: with components of
  mass 3/4 and 1/4 at `true`, the mixture's mass at `true` is `1/4 + t/2`,
  where `t` is the upper law's mass at `true`; `t` stays a separate parameter
  unless something constrains it.

Placement: `tests` DNP_inv `55892476`. It probes the cost of the CHANCE_3
rival to DNP_inv when the rival is made quantitative. One symmetry orbit fixes
only the uniform law. Positive switching fixes a stationary law only relative
to a kernel that is itself a quantitative law. Two orbits, zero switching and
idle mixtures fix nothing. So a non-uniform law needs quantitative input,
which the rival must supply. The result neither supports nor refutes DNP_inv.

### 2. The law fork (`lawSelectionFork`)

- **Fork.** If a fact tracks a selected value and the contingent-fact PSR
  holds at `a`, then either the value is the same at every accessible world, or
  it differs at some accessible world and the fact has an admitted reason.
  This is a fact-PSR application, not the existence-PSR bridge `608a262d`.
- **Constant branch.** If the value is the same at every accessible world, the
  tracking fact is not contingent, so the contingent-fact PSR makes no demand.
  A necessary law and a necessary adoption alike pass this branch.
- **Symmetry.** If the operating law is the law a selector adopts, and the law
  varies at an accessible world, then both the law fact and the adoption fact
  need an admitted reason. Personal selection does not escape the demand that
  it places on an impersonal law.
- **Matched controls.** Two contexts with the same finite record and the same
  credence carry different laws (3/4 versus 1/4), and neither law gives any
  finite record zero independent-trial likelihood. In the matched arena the law
  fact is contingent. Without an admitted reason the contingent-fact PSR fails;
  with the everywhere-true base fact admitted as its reason the PSR holds, but
  that reason does not fix the law. An admitted reason is weaker than a
  law-fixing reason.

Placement: `connection_plan` to `66aecdd7`. The missing bridge has two joint
parts:

- (a) the root's law or content fact is contingent, which puts it on the
  fork's second branch. For content, this is the existing open premise
  `fbd0a6d3`: every actual root withholds its giving of each grounded actual
  concretum at some accessible world.
- (b) at the actual root, the only admissible reason for such a contingent fact
  is an intentional exercise of a rational power.

Part (a) alone yields only an admitted reason, and clause 4 shows that such a
reason need not fix the law or be intentional. Blocker: no recorded premise
supplies (b), and the symmetric fork cannot supply it.

### 3. Realization and sample (`realizationSampleControls`)

- **Support does not settle realization.** #462's `varying` profile and the
  same profile with its causal edges removed (`emptied`) share source, existence
  table, act and outputs. For every full-support law on the two world labels,
  the support of its image law is exactly the output set in both profiles. Only
  `varying` realizes its outputs causally. The emptied relation is a
  structural independence control, not a countermodel to an actual
  intrinsically productive disposition.
- **Adopting a law does not settle its sample.** In a one-agent STIT frame
  whose cells are fixed by the adoption coordinate, the agent sees to the
  adoption (deliberatively: it is not historically necessary). The actual
  sample is `true`, but the agent sees to neither the sample nor its contrary.
  Rationally choosing a law is not necessarily choosing its sample.
- **General STIT lemma.** In every frame, if an agent sees to some
  proposition at a history and the same cell contains a history where an effect
  fails, the agent does not see to the effect. The STIT vocabulary has no plan
  or governing relation.

Placement: `tests` `2f9a99cc`, which concludes argument `9203e79c`: each
rationally given actual effect is directed to an end. If a giver's choice
settled only a law, seeing to the law's adoption would not see to the
particular effect. Per-effect direction then needs `9203e79c`'s premises to bear
on each effect, not on a law. The model tests this only at the level of
seeing-to. `4be0f774` itself allows one plan to govern many effects and makes
no claim that plans fix outcomes, so it is not the target.

## Comparison at matched scope

- **Necessary intrinsic law.** If the law is necessary and intrinsic to an
  actual productive power, a determinate law-level explanation is possible in
  principle, with contingent effects. Result 2's constant branch places no
  contingent-fact PSR demand on it. Result 1 shows that one symmetry orbit fixes
  only the uniform law. A non-uniform law needs quantitative input: a
  calibrated mass, orbit masses, or a kernel whose own masses fix the
  stationary law. Such input relocates the law question rather than answering
  it. The open questions are whether such input is grounded in the source, and
  whether the law is productively realized (result 3).
- **Contingent brute law.** It conflicts with the contingent-fact PSR at the
  varying branch of result 2. That conflict is not a logical inconsistency
  apart from the PSR.
- **Higher-order mixture.** It helps only if the upper law is itself warranted
  and operative. When the components are equal, the upper law is idle.
- **Personal selection.** It can settle content for reasons, through genuine
  intentional exercise, without necessitating an effect. Under result 2's
  symmetry clause it faces the same demand for any contingent adoption. It must
  exclude retrospective redescription and ties treated as selectors. The
  existing `OptimalCreationChoice` tied optima constrain the eligible outputs,
  not their relative weights (#2144's tied-optima control).
- A chance explanation of an occurrence is not shown to be inadequate. This
  is a numerical counterpart of #1953's range/selection decomposition, not a
  demonstrated defeat of the impersonal account.

## Removed from the earlier draft

- `RealizationRoute` returned its own hypothesis `realizes selected μ`
  together with the existing `necessaryRootAncestor`. It added nothing to that
  theorem beyond a projection. It is removed rather than registered; the
  actual-realizer route is the existing selected-ancestry result applied to an
  actual concrete realizer.
- `ProductiveControl` (a constant PMF attached to the `UltimateAdequacy`
  single and chain exercises) is replaced by result 3's `varying`/`emptied`
  comparison, which the slice specified.
- `FixedBy`, `RepresentsLaw` and the operative flag are replaced by
  `TracksValue` and `FixesValue`. The essential-description clause was only a
  contrapositive of its definition.

## Deferred

- Existence of a stationary law, and uniqueness under irreducibility, for
  general finite kernels, together with infinite-chain controls. Only the
  binary case is certified here.
- Convergence in a topology on `PMF`.
- The 1/12-grid arithmetic diagnostic of the slice. The general binary
  theorems supersede it.
- `PSRLaterAxes.probability` already certifies fixed ranking and the absence
  of universal net selection, so neither is re-proved here.

## Open interfaces (no premise discharged)

- Productive calibration of a law to the actual same root.
- Warrant for the contingent-fact PSR's coverage of the law fact.
- Explanation of the particular outcome beyond comparative probabilities.
- Positive actual rational apprehension and exercise, which go to #2145's
  `beede613`/`4be0f774` and to the same witness for `29818edd`/`66aecdd7`.
