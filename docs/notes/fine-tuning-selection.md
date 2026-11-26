# Observer selection and fine-tuning: conditional comparison

Analyst reconstruction for #418; attribution deferred. This serves the existing
`STMT-GOD-EXISTS` (`8626f8a5-9531-5da7-9ebd-f901e74b1129`) root-route node.
The connection is a plan, not a new argument to that node: calibrate a physical
sampling model, justify designer likelihoods, infer an actual designer under an
explicit epistemic rule, and identify that designer with the stage-one GOD_4
predicate. All four steps remain open. A statistical hypothesis is not a being.

The finite scope is three exclusive cells: fine evidence with observers, other
observer evidence, and no observers. Fine evidence implies observers in this
profile. This is a bounded partition, not a claim that all physical meanings of
fine-tuning have been exhausted. `Sampling` uses nonnegative rational weights
whose Mathlib finite sum is one. Both observer mass and fine evidence mass are
strictly positive. The event-ratio definition conditions on observers; it does
not silently condition on already knowing the fine evidence itself.

`CalibrationDirection` universally quantifies over such distributions. Its
antecedent explicitly bounds designer conditional likelihood below by 3/4 and
natural likelihood above by 1/4. Positivity and ordered-field arithmetic then
put the Bayes factor above one. These numerical bounds illustrate sufficient
calibration; they are not estimates of any actual cosmology. They remain inside
the conditional theorem, not independently defended corpus facts.

The nonvacuity pair has observer mass 1/2 under either hypothesis and conditional
likelihoods 3/4 and 1/4. The selection/multiverse rival retains natural fine mass
1/8 but removes the other-observer cell: its conditional likelihood becomes one
and the factor becomes 3/4. Thus a natural rival with rare observer worlds need
not assign low probability to fine evidence *among observers*. This is a serious
selection alternative, not a refutation of naturalism or an assertion about the
number of universes. Other physical measure and typicality rules remain open.

A second omission retains natural likelihood 1/4 but lowers the designer's to
1/8, yielding factor 1/2. Designer intentions cannot be inferred from the word
“designer.” Both omissions genuinely reverse direction; neither uses a zero
conditioning event. The selected natural model has a zero *other-observer*
cell, an allowed event within a nonzero conditioned population.

Reuse inspected: `Logic.ContrastiveWorldview.Comparison`, `UpdateConstraints`
and `Results.Logic.ContrastiveWorldview.updateConstraints` distinguish posterior
odds from likelihood ratios. Its input likelihoods are scalars, so reusing that
structure alone would leave observer selection unencoded. This batch supplies
finite sampling semantics and uses the same rational event-likelihood meaning;
it does not duplicate the Fifth Way regularity deduction. Prior odds 1/10 times
factor three stay below one. Posterior preference, evidence gain, actual truth,
and GOD_4 identification remain separate. No claim about exhaustive metaphysical
worldviews is licensed by a two-hypothesis comparison.

Rejected: using unconditional fine mass as the observer-conditioned likelihood;
assuming all designers want fine evidence; treating a favorable factor as
posterior victory; identifying a hypothesis label with GOD_4. The missing
encodings need physical sampling and calibration commitments and a typed
actual-designer identification bridge. No new historical attribution is made.

## #1381: proposed findings for independent semantic challenge

Analyst mathematics, 2026-11-10. `Science.FineTuningEvidence` extends the exact
existing `Sampling` meaning without changing its fixtures. `Factorization`
quantifies over all pairs, not just the examples. Write R for raw evidence
factor and S for observer factor. The conditioned factor is R/S, exceeds one
exactly when R>S, and equals one exactly when R=S. Positive evidence and observer
mass are inherited from Sampling. E is the first cell and O the first two, so
E is a subset of O by construction, not an empirical conclusion.

The existing design/natural pair has (R,S,R/S)=(3,1,3); design/selectedNatural
has (3,4,3/4). The latter favors D jointly and N incrementally after O.
Multiplying observer evidence by the *raw* factor would count O twice: sequential
updating instead multiplies S by R/S. Neither ratio alone determines posterior
odds. When other-observer mass vanishes under both hypotheses, each conditional
likelihood is one. The new nonzero screened pair has evidence/observer masses
1/2 and 1/10 and factors (5,5,1). Observer existence can remain discriminating
when additional evidence is screened off. This does not assume that actual
fine-tuning evidence equals observerhood: measurements may distinguish many
observer-permitting worlds.

`PushforwardInvariance` uses arbitrary Mathlib measures on measurable spaces,
`MeasurableEquiv`, `Measure.map`, and the image of both events under the same
bijection. It proves both E probabilities, their ratio, and the conditional
ratio using intersections. Thus it is a genuine measure-theoretic theorem,
including continuous probability spaces, not a finite relabeling surrogate.
The ratios are ENNReal expressions; Lean defines even zero/infinite division.
Those algebraic cases are not evidential Bayes factors. For evidential use,
require measurable E and O, probability measures, positive observer masses under
both hypotheses, and positive n(E∩O) for a finite conditional Bayes factor.
Require positive intersections under both hypotheses for a strictly positive
factor. Positive E and O masses alone do not suffice: E and O can be disjoint.
The inner ratios d(E∩O)/d(O) and n(E∩O)/n(O) are conditional probabilities;
their quotient is the conditional Bayes factor. The unrestricted theorem also
preserves outer-measure values of arbitrary sets, which does not make those
sets measurable probability events. It does not prove a density formula, a
cosmic measure, or a preferred coordinate.

The issue's continuous illustration is a mathematical illustration, not a
separately certified integration result here: on [0,1], masses below a are a
and a² for densities 1 and 2x. The map y=x² transports the cutoff 1/2 to 1/4
and preserves masses 1/2 and 1/4, hence ratio two. A new uniform-in-y measure
assigns 1/4 to that event and changes the comparison to one. The general Lean
result certifies transport *given* a measurable equivalence; it does not certify
this particular interval equivalence or its densities. No continuous invariance
gap remains at the general theorem level; explicit analytic illustration remains
uncertified. Requiring invariance alone cannot select a measure: every candidate
measure enjoys the same covariance under its own pushforward.

### Positive accounts, dependencies and discriminating tests

A physical ensemble account can derive weights from a dynamical distribution
on initial states, a map to effective constants, and a sampling rule for records.
This supplies a positive generative alternative to unexplained uniformity.
A conditional bridge is: if a justified generating measure and record-selection
kernel produce these cell masses, the corresponding ratio applies to the sampled
record. Its price is a real distribution plus sampling interpretation, not merely
many universes. If the relevant sample is an observer record rather than a
universe, number and longevity of observers affect the kernel. Counting universes
and counting records need not agree. A next test needs a specified physical model
and its observer-production/record map; none is supplied here. No theorem about
normalized weights can recover that missing empirical input.

An observer-selection account positively explains a high conditional fine-evidence
likelihood through a viability filter, even with low unconditional observer mass.
The strongest screened version says all possible sampled observers necessarily
see E. Its price is the necessity bridge O→E under *both* accounts and the chosen
reference class. A broader notion of fine evidence can include measurements not
required for observers, defeating that bridge without defeating selection. The
next discriminating test is to separate viability from measured residual features
and derive their distribution conditional on viable records. The three-cell
profile supports this distinction but supplies no actual residual distribution.
Whether the observer datum itself is new evidence must also be fixed: treating
it as background removes S from the incremental update, not from the joint
likelihood. Self-location among records and existence of some observer are
different experiments; a reference class must say which one it models.

A design account can positively generate evidence via a distribution over goals,
capabilities and chosen mechanisms, rather than treating 'designer' as an arbitrary
likelihood flag. A meaningful sufficient bridge would bound its observer-conditioned
E probability below by a and the rival's above by b, with 0<b<a≤1. Existing
calibration supplies one illustrative instance. The price is independent support
for the goal distribution and implementation success. Mere capacity to design
supplies neither preference nor likelihood. Benevolent interest in observers does
not entail preference for this physical implementation over alternative observers;
selection may make both models conditionally certain. Next test: specify an
independently motivated objective/mechanism model and derive residual predictions
beyond viability. No empirical designer-goal distribution is available in this
assignment; inventing one would relocate the inference into an unsupported premise.

A symmetry/maximum-entropy account can positively justify uniformity relative to
a specified invariant volume or constraint set. Its price is justification of
that volume, constraints and physical symmetry. Differential entropy relative
to a fresh coordinate volume generally changes the measure; covariance does not
justify assigning uniformity twice. The next test is a physical transformation
group and its candidate invariant measure, checking normalization and uniqueness.
Without that specification, no coordinate argument selects between rival priors.
An improper invariant volume also cannot be normalized into Sampling without
additional cutoff/limit choices and a demonstrated stable prediction.

A robustness bridge can avoid uniquely selecting one prior: independently delimit
admissible paired measures and show every pair has R>S. This would give stable
incremental direction without a unique distribution. It still needs a warranted
admissible class and bounds. The existing two fixtures already refute robustness
across *all* Sampling pairs, and the indifferent designer reinforces the failure.
Next test is a physically/intentionality justified restricted class, not more
arbitrary fixtures. Thus both unrestricted robustness and coordinate-only prior
selection have concrete negative outcomes, while restricted robustness remains
an informative candidate conditional bridge.

Finally posterior odds require prior odds and an updating policy; actual truth
requires a further epistemic inference. A designed physical world need not have
a unique designer, necessary designer or the GOD_4 properties. The identification
bridge requires an argument about the designer's nature; no statistic above
provides those predicates. These are separate dependencies, not evidence against
design. No accepted floor conflict or internal contradiction has been found for
the positive rival accounts, so their unusual commitments are not declared defeats.

### Provisional assessment and reassessment boundary

Proposed overall judgment: the mathematical evidence distinction and transport
invariance are supported by the exact encodings and successful development
elaboration, pending final certification and independent semantic challenge.
Actual design support remains underdetermined. The strongest surviving accounts
are physical generative sampling with observer filtering and goal-mediated design;
the available facts specify neither distribution, nor residual prediction, nor
which observer datum is background. Shared dependence on these inputs means the
new deductions are not independent cumulative evidence for actual design.
Reopen on an encoding mismatch, failed certification, a justified restricted
measure/goal class, a residual observational discriminator, or an identification
argument. Further actual-world resolution requires those missing inputs; there
is no remaining purely algebraic test in this issue that selects them.

Self-sweep: no source/claim attribution; no new approval marking; no actual design,
God or root conclusion. Internal universally quantified statements have no external
premises, but their applicability is open. Invariance includes intersections for
non-subset events; rational factorization uses the stricter existing subset
profile. Controls witness stipulated compatibility and opposing incremental
results, not physical realizability or metaphysical possibility. The planned
connection remains `STMT-GOD-EXISTS`; physical sampling, designer likelihood,
inference and God identification are all open. Computed frontier-diff is the
premise authority; these disconnected conditional results discharge no root leaf.

Service experiment: corpus record lookup returned the exact expected record and
preview binding. Two full-content submissions used scratch `finetuning1381/Edit.lean`
at clean preview 078c37fd5d77f77c661b0d6ad8a8de5fe22c5d7c. First elaboration
found missing noncomputable annotations on ENNReal division; repaired submission
had no diagnostics (content SHA256 c80bd9c4690833389def1fa59af49e256da5aee5e9e50a3caf375b0bf5cd8b9c).
The repeated full edit reused imports; measured request times were 17.49s then
8.63s, which is not a controlled CLI speed comparison. Retain the service for
bound feedback; revise import preparation to support new modules without combining
source into scratch. Canonical-file CLI checks and delivered-head CI, rather than
these preview diagnostics, govern certification. Shared conventions resolved at
625cb04ca568aebc8d45c90033e107a05e9bd2a0.

### Definition audit and disposition of the rough draft

`Sampling.weight : Fin 3 → ℚ` is a numerical assignment. Its nonnegativity,
normalization, observer positivity and evidence positivity fields are constraints
on that assignment, not definitions of physical observerhood or a cosmic
sampling mechanism. The first cell means E∩O, the second O∖E, the third Oᶜ;
representing all E by the first cell assumes E⊆O. This is the selected evidence
meaning throughout the rational result. Generic physical 'life-permitting
constants' need not entail actual observers. Substituting that broader meaning
would require an E∖O cell and would invalidate the raw-E factorization unless
that cell has zero mass under each hypothesis. The measure theorem instead uses
E∩O explicitly and needs no subset assumption. No new philosophical sense has
been silently assigned to the existing three-cell vocabulary.

`likelihood` is precisely weight(0)/(weight(0)+weight(1)); `factor` divides two
such values. Neither is a posterior, causal propensity or objective chance by
definition. `Calibrated` is an inequality constraint on these values, not a
semantic definition of design. `design`, `natural`, `selectedNatural` and the
new screening fixtures are fully specified rational structures; their labels
are mnemonic, with no primitive God/designer predicate inside their bodies.
`SelectionControls` is a conjunction of evaluated equalities/inequalities,
not an axiom requiring the world to match a fixture. The reused contrastive
`Comparison` has rational prior and likelihoods with positivity/bounds;
`normalizer`, `posteriorW` and `posteriorV` implement a stipulated binary update.
That binary exhaustive interpretation cannot be transferred to all design and
natural hypotheses without model coverage. Pairwise likelihood comparison does
not require exhaustive metaphysical hypotheses; a posterior binary normalization
does require a specified hypothesis partition or explicitly restricted comparison.

The new `raw` and `observer` functions are ratios of the already defined masses;
`Factorization` states a derived constraint on them, not a new empirical premise.
`eventFactor` and `conditionalFactor` use actual Mathlib measures (countably
additive ENNReal-valued set measures) and set intersection. `MeasurableEquiv`
requires a bijection measurable in both directions. This supplies the real
transport meaning; a merely named coordinate correspondence is insufficient.
No new opaque metaphysical primitive, content fork or strength fork is introduced.
Physical interpretation obligations remain explicit prose because no physical
account has been supplied to type, rather than because constraints have completed
its definition. Existing dossiers and attempt [752c6644](../../corpus/attempts/752c6644-d537-4efc-9e45-cbb08372be38.json) retain the previous scope.

Disposition: Finding A's algebra, threshold and neutral screening are elaborated;
its fixtures are preserved and the five-to-one screening fixture added. Its
conditional/unconditional reversal language is corrected to incremental versus
joint comparison. Finding B's general measurable transport is elaborated over
actual measures; its interval-density example remains explanatory and has no
claimed analytic Lean certificate. Fresh-coordinate uniformity is rejected as a
transport operation. The suggested claim that actual prior/reference-class
warrant follows from either theorem is rejected; no such inference exists.
The application remains unresolved for the specific missing generative, sampling,
goal and inference inputs above, not because proof search failed. This review
is not exhaustive across physical cosmologies or designer theories.

Canonical CLI elaboration subsequently passed for vocabulary, frozen Challenge
and Solution using an explicit LEAN_PATH overlay of the warm compiled outputs
(2.02s, 3.54s, 1.74s respectively). Challenge `sorry` warnings are expected;
Solution had none. This is not an equivalent latency benchmark against the
combined service submission. The first CLI attempt exposed namespace-prefix
shadowing by the new output directory; an overlay of existing warm outputs
resolved import lookup without changing shared dependencies. Comparator final
certification was attempted with the supplied verifier and stopped at:
`sandboxed lake build ...Challenge ... Permission denied (os error 13)`.
No sandbox bypass was attempted; binding, axiom, Comparator and NanoDa gates
remain for delivered-head CI. Computed `frontier-diff --base origin/main`:
402 open premises (262 bare, 95 supported, 45 stated) unchanged; lowest expanded
route cost 16 unchanged; verified support alternatives 288 unchanged, added 0.
No premise change. This is a conditional library checkpoint with the explicit
connection plan above, not connected root support.

### Independent semantic challenge

The independent challenge inspected the entire proposed outcome and its exact
proof/model/record evidence at `2f8d927e8e7d4f33bc220d5b4809877202aa7c47`.
Its one P2 finding was the insufficient evidential-use qualification; the text
above now distinguishes measurable probability events from arbitrary-set
outer-measure transport, and states the required positive intersection masses.
The theorem, models and remaining qualified assessment are unchanged. No new
formal verification or real-world design support follows from this prose repair.
The next actual-world test needs a justified physical sampling model and a
specified designer-goal model with a residual prediction beyond observer viability.

## #1569: Which vacuum-energy decade does an observer find?

The homogeneous causal-entropic model assigns about **34% or 43%** to the decade
containing the measured vacuum energy, depending on its star-formation history.
Communication of goodness supplies a reason to create, but gives no ordering of
this decade against adjacent observer-bearing alternatives. A narrower published
purpose, maximizing the fraction of baryons becoming life, does give a testable
ordering criterion. Its astrophysical inputs reach stars; its life yield is still
undetermined. These are comparisons of the same density after observerhood. [Assessment record](../../corpus/attempts/04f0d276-6dce-408e-a258-81b1d0b28944.json)

### One residual and its physical prediction

Use Planck units and write `r = Λ/(8π)`. Restrict both accounts to the
paper's flat, positive-Λ family with the other low-energy parameters held
fixed. Let O mean that the sampled center is an observation record. Attach the
ambient vacuum density to each center, and ask whether **E**,
`10^-123 ≤ r < 10^-122`, holds there. O is background before learning the
density. The record need not itself contain a precision measurement. This
idealization compares true local values, with the published central estimate
`1.25 × 10^-123` identifying our bin. Modeling noisy survey classifications
near the lower boundary would require a measurement-error distribution. The
decimal partition is explicit and the observed bin was picked retrospectively.
The result tests model fit to a known datum. It includes neither a new
prospective success nor an extra update for being observers.

Bousso, Harnik, Kribs and Perez motivate a dense spectrum and population by
transitions among metastable vacua. Their calculation assumes an effectively
flat prior per **linear** density over the relevant range. In a homogeneous
cosmology take a comoving worldline and its causal diamond from reheating to
the asymptotic future. The baseline counts ordinary-matter entropy production
and excludes horizon entropy from de Sitter space and black-hole formation.
Integrate the modeled ordinary-matter entropy production per comoving
volume against the diamond volume at each time. High densities curtail the
volume available during the era of starlight reprocessed by dust. The
combination with the linear prior gives a peak per log decade. No conditioning
on today's age or on measuring during peak starlight enters this integral.
Interpreting this as sampling records requires their expected number per diamond
to be proportional to that entropy. Sampling a vacuum once if it has *any*
observer gives a different weighting. Thermodynamic requirements and the finite
causal region motivate the proxy, while its proportionality across densities and
the effective population prior remain assumptions. [Bousso et al., §§1–2.3, 3.4 and 4.2, Eqs. (2.4)–(2.8) and (3.24)](https://arxiv.org/pdf/hep-th/0702115)

| Star-formation history | Published median of r | Mass of E from Fig. 8 |
| --- | ---: | ---: |
| Nagamine et al. (N) | 5.6 × 10⁻¹²³ | ≈ 0.34 |
| Hopkins et al. (H) | 2.1 × 10⁻¹²³ | ≈ 0.43 |

The last column is our integration of the plotted curves. To reproduce, read
Fig. 8 of v3 (printed p. 27) with horizontal ticks in log₁₀ r and vertical
ticks in probability density per decade. Clip each published polyline to
[−123, −122], interpolate where it crosses the endpoints, and sum trapezoid
areas using the displayed vertical scale. The unrounded plot readings are
0.343 and 0.428. As a scale check the full plotted interval [−126, −120]
integrates to 0.992 and 0.996 respectively. No renormalization to the displayed
window. Both histories use information about our cosmos. They are alternative
calculations on the same datum, with no supplied mixing weights. [Bousso et al., Eq. (1.1), §3.4 and Fig. 8](https://arxiv.org/pdf/hep-th/0702115v3#page=28)

The physical sensitivity reaches the shape of this prediction. With worldlines
uniform in late physical volume, most late diamonds miss bound matter. With
early comoving worldlines tracing matter, some remain in halos. If late
evaporation contributes entropy scaling as halo mass squared and dominates,
Phillips and Albrecht obtain weight proportional to 1/r in the small-r limit.
The resulting log-density approaches a constant. Extending that tail admits
additional decades of comparable weight. A lower cutoff or actual discrete
spectrum is then needed to normalize it and assign E a mass. This gives a
physical mechanism by which the favored scale can disappear. The small-r
asymptote alone gives no revised number for E, and counting evaporation as
observations remains a separate hypothesis. [Phillips and Albrecht, §§IV–VI, Fig. 5](https://arxiv.org/pdf/0903.1622)

### A purpose on the same density axis

Take the corpus's independently specified Thomistic end, communication of
goodness. A source possessing a good can will that another share it; an
intelligent source could choose an order enabling creatures to exercise their
capacities. This explains how creation could be intentional without remedying
a deficiency. The distinction between necessarily willing goodness and
contingently willing particular means leaves open which observer-bearing
orders it would choose. The [contingent-choice investigation](optimal-creation-choice.md)
distinguishes producing an order for an adopted end from explaining the contrast
with each unchosen order. Neither the existence of observers nor the capacity
for such choice supplies relative weights inside and outside E. [Existing
claim and interpretation](../../corpus/claims/q19-communicated-good.json);
[Aquinas, ST I q.19 aa.2–3, bodies](https://www.newadvent.org/summa/1019.htm)

For a sharper comparison, Page examines a biophilic principle that selects
a value maximizing the fraction of all baryons becoming life. Its objective
can be stated without mentioning the observed decade. Taking it as a
creator's *exclusive* choice rule adds a substantive premise to the broader
end. Assuming that life develops from baryons in galaxies, Page factors the
life fraction into the fraction collapsing into galaxies and the life yield
of those baryons. Smaller positive Λ favors collapse. Metal enrichment,
gas retention and stellar environments may affect the second factor, whose
direction of change is unknown. A derivative can test local optimality where
nearby densities are feasible on both sides. Suppose a global maximum is
attained. For the objective alone to rule out **the whole bin** under every
tie-breaking choice, every feasible value in E must be outperformed by an
available alternative. If all maximizers lie outside E, a successful exact
optimizer gives E zero probability conditional on an observation record,
provided such records have positive probability. If maximizers lie on both
sides, a specified choice and sampling rule can still give E zero weight. [Page, §§2–3, especially pp. 6–9](https://arxiv.org/pdf/1101.2444)

There is a numerical check on substituting stellar production for life.
Sorini, Peacock and Lombriser's positive-Λ models give asymptotic stellar
fractions of about 0.27 at 0.1 Λobs and 0.23 at Λobs. In an explicit
stellar-mediated model write the final life fraction as stellar fraction
times life yield per unit stellar mass formed. For the observed point even
to tie that lower-density alternative, its yield must be at least
0.27/0.23 ≈ **1.17 times** the alternative's yield (assuming positive yields).
The lower-density comparator falls outside E. The numerical threshold belongs
to their own fiducial cosmology and stellar prescriptions; transferring it to
the 2007 CEP parameters would require matching those inputs. It tests two points,
leaving other in-bin choices and the yields themselves open. The calculation
concerns total cosmic baryons, as befits Page's objective; it supplies neither
diamond entropy nor a count of centered records. Stellar physics gives a
reason to investigate the yield ratio, and offers no independent reason why a
source would optimize that particular fraction. [Sorini, Peacock and Lombriser,
§4.2, Fig. 10 and §5.4.2 on model sensitivity](https://arxiv.org/pdf/2411.07301)

**Provisional judgment.** The homogeneous stellar CEP has the stronger
quantitative account of this residual under its sampling assumptions. Actual
comparative support for a purposive source remains undirected. For example,
a warranted purpose probability above both plotted masses would favor that
purpose on E against either stellar prescription, if its prediction and the
entropy-to-record calibration applied to the same centers. None of the
examined goals supplies that bound or its reverse. The stronger physical
sensitivity concerns the worldline and late-entropy choices, beyond the
spread of the two stellar curves. A purposive source could also choose a
landscape; comparison of specified generating accounts does not partition
theism and naturalism.

**Reopen** when a physical record-selection rule independently fixes or
bounds E under the alternative worldline measures, or when a purpose account
orders the attainable densities using warranted yields and an independently
motivated choice rule. Either would narrow the missing pair. Use the same
observation timing, and fold in measurement errors on both sides if testing
reported estimates. The experiment/center distinction (322ddba8, #1401) and
incremental factorization (6a84cd7a, #1381) already explain the conditioning;
neither result calibrates these models. Applying the comparison to belief
still needs #1734's epistemic bridge. #1731's intellect/will capacity and
#1730's contingent exercise do not identify a goal distribution or identify
an actual designer with the GOD_4 witness. This research changes no formal
premise or root route.

## #2050: information in the report after observer selection
[Research attempt](../../corpus/attempts/752c6644-d537-4efc-9e45-cbb08372be38.json)

Fix the report to whether a sampled observer falls in the fine-evidence cell
(cell 0 rather than cell 1). The channel uses the existing conditional event
ratio in each sampling row. The prior weights the design and natural labels
**after** conditioning on observerhood. A pre-selection prior would first
require an update by the observer likelihoods. `observerInformation` shows
that, at any comparison prior strictly between zero and one, those two
conditional event ratios agree exactly when the report is independent of the
label. Since the report is binary, the fine-report probability determines
the entire observation law. The same reduction would require checking every
report category in a finer partition.

The strongest positive warrant within this profile is a difference in the
conditional report distributions under the same selection rule. The existing
design and natural rows give 3/4 and 1/4. A fine report then favors design over
that modeled rival (Bayes factor 3), while a non-fine report favors the natural
rival. Mutual information measures the expected discrimination of the
experiment before seeing its output, in nats. The Brier agreement theorem
addresses only the zero condition under coherent binary updates and interior
predictive mass. It leaves both metrics and their interpretations distinct.

The screened pair shows the strongest selection rival within this test. Its
raw fine-evidence masses differ (1/2 and 1/10), but both rows give conditional
probability one because their other-observer cell is empty. Their report
laws coincide at a nonuniform comparison prior (design 1/3 and natural 2/3).
The certain report contributes no further update after observerhood.
The Lean control `screenedObserverhoodSeparates` observes observerhood
before selection in these same two rows. Its likelihoods are 1/2 and 1/10,
so it carries positive information under any interior pre-selection prior.
The existing `selectedNatural` control answers a nearby challenge at the
same scope: restricting observers to fine-evidence worlds can even reverse
a design-favoring factor. A physical ensemble with selection therefore
needs a justified distribution on its observer populations. An impersonal
necessity account can predict the same report if a specified constraint
forces its observer evidence into cell 0. It needs a derivation of that
constraint and its record distribution. A purposive account needs an
independently motivated intention and sampling rule to predict its own
conditional row. The numerical controls supply examples of sampling laws
only. They carry no modal claims about either model.

Provisional assessment: the fine report has conditional evidential force
when calibrated competing rows differ. The existing examples supply no
actual likelihood calibration and give no grounds to rank the actual
origin accounts. Reopen this comparison when a candidate can derive the
distribution of **more specific observed features among observers** under
a shared measurement and selection procedure, or when an independently
justified design distribution and a concrete impersonal rival supply
different conditional predictions under that procedure. Raw rarity cannot
replace that comparison.

The typed graph links test the existing finite calibration and connect
the information criterion to the binary Bayesian accuracy result. The
destination is the existing `STMT-GOD-EXISTS` node. The planned bridge
still requires physical selection and calibrated likelihoods, a warranted
inference to an actual designer, and identification of that witness with
GOD_4. The model-label distinction also cannot supply #1867's missing
inference to unrestricted law continuations: finite probabilities presuppose
a chosen sampling law over admitted outcomes and do not settle which
histories are metaphysically possible. For #930, the accuracy result
specifies an information-sensitive consideration under the modeled update
conditions. Whether it supplies actual pro tanto or categorical reasons
for belief requires the separate epistemic bridge.

The [retention control](../../corpus/results/19bf9149-0b9c-4186-8c6c-619aa8224527.json)
applies the root-linked [teleonomy filter](../../corpus/statements/teleonomy-selection-coverage.json)
to the fine indicator. The fixture retains the whole fine cell and discards
its complement. If both rows have zero other-observer mass, this yields
exactly their observer-conditioned fine likelihoods. The report is certain in
each row and has zero mutual information at every interior comparison prior.
The typed `tests` edge records this application. Its input represents sampled
cells, so it exercises the Boolean filter without interpreting the cells as
organisms or drawing an inference about tending or intelligent direction.
