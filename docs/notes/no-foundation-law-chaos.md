# No ultimate foundation, radical law-change, and whole-history stability

This is an **ontic conditional** for the God-existence-stage explanation question
in #735, extending the exact existing #736 history-selection, #737 predictive,
#743 law-actuality and #1801 persistence-law distinctions. It addresses a
particularly sharp opponent: **there is no ultimate explanation of the order,
and no deeper necessity or actual power constrains which local law governs at a
later time**. Whether the opponent is committed to that second clause, rather
than a merely brute **stable** law, is the decisive live question.

The mathematical result is not an unconditional refutation of naturalism or of
no-foundation views. It asks what a *radically unconstrained future* costs **if
admitted as an ontic range of complete alternative histories**. No extensional
trace model by itself makes these histories metaphysically possible, and no
theorem derives that admissibility from absence of an ultimate ground. The
inference `no ultimate ground → all future transitions admitted` is **OPEN**.

## Exact formal discriminator

`TruthCore/Explanation/NoFoundationLawChaos.lean` imports existing
`UltimateExplanation.Profile`, `Follows`, `Cell`, `openFuture`, `stable`, and
`LawActuality.UsesRecord`, as well as the existing `History`/`SameHistory`
signature. Its four properties have separate frozen Challenge declarations:
`Certificate`, `LawSwitch`, `OneRival`, and `Omissions`.

1. **Unrestricted suffix, not merely one unexpected event.** `splice n tail`
   leaves the exact observed `true` values through `n` and installs an
   **arbitrary whole infinite Boolean suffix** thereafter. `SuffixComplete p n`
   says every such complete path belongs to `Cell p on n`; the exact `Certificate`
   characterizes `Cell (openFuture n) on n` as *all and only* the paths with
   that prefix. Thus any prescribed collection of later flips, including
   infinitely many, is admitted. No external probability or temporal-causal
   relation is assumed.
2. **Populated, distinct whole histories.** `realized : History Trace Bool Nat`
   represents exactly one Boolean state at every time in every path-world,
   with `ExistsAt` agreeing at now=0. For **each** unobserved `k ≥ n+1`,
   two witnesses agree at *every* observed index, differ at `k`, and have
   different `SameHistory` presence extensions. Both are populated, rather
   than a degenerate empty-world control. They represent state values, **not**
   the persistence of one concrete substance with a fixed identity.
3. **Every predictor and every later time.** For any `predict : Trace → Bool`
   satisfying the *existing* `UsesRecord n` (all possible inputs with the same
   entire record receive the same prediction), and **any** `k ≥ n+1`, there
   is no exact prediction uniformly correct across an `SuffixComplete` class.
   This is stronger than #737's failure of its particular persistence
   `forecast`, though related to #743's all-estimator failure at first
   unobserved time for a pair of individually unique laws. It tests a
   **uniform zero-error requirement**, not fallible justified induction.
4. **Every complete-history law claim.** `UniversalProjection p q n` means the
   same candidate `Profile q` is satisfied by **every** path in the admitted
   cell, not simply by one actual path. If `SuffixComplete p n`, any such `q`
   must permit **all four** Boolean successor pairs at every `t ≥ n+1`.
   Therefore *every* candidate law excluding at least one late transition
   fails that universal projection, and **no deterministic candidate law**
   can pass it. The result quantifies over *all* time-dependent relations
   `q.step`, not just persistence, periodicity or a finite list of laws.

The strongest piece is the **iff**, not merely a failure witness. For every
candidate `q`, `UniversalProjection (openFuture n) q n` holds *exactly when*:

| Law component | Necessary and sufficient across all admitted paths |
| --- | --- |
| Initial condition | `q.initial = true` |
| Earlier transitions `t < n` | `q.step t true true` |
| Boundary transition `t = n` | Both `q.step n true true` and `q.step n true false` |
| All later transitions `t ≥ n+1` | `q.step t a b` for **every** `a,b : Bool` |

So a law may still describe the already fixed past, and a fully permissive law
may be universally true; no surviving universal law restricts later Boolean
changes in this explicitly radical model. This is a statement about truth
across the *selected alternative space*, not about whether a stable law can be
true of the *one actual history*. It does **not** show that non-deterministic,
stochastic, dispositional, probabilistic or law-of-law constraints are impossible
under weaker rival commitments.

### One fixed radical rival, with explicit switching rule schedules

An important quantifier control avoids adjusting the theory with the cutoff.
The original #737 profile `openFuture n` changes as `n` changes. `OneRival`
instead uses the **same fixed** profile `unconstrained` at *every* possible
finite cutoff. Its admitted complete paths are exactly the paths with initial
value `true`; for any record prefix, all suffixes are available. This is one
coherent, nonempty alternative *model class* with arbitrarily late deviations,
not a new model selected opportunistically after each observation.

`scheduled switches` gives a different, **individually deterministic**
transition profile for every Boolean law schedule:

- `switches t = false`: next state equals current state (*copy law*).
- `switches t = true`: next state is its Boolean opposite (*toggle law*).
- `generated switches` is its unique complete state path from initial `true`.
- `toggleFrom k` copies through step `k-1` and **switches the rule** to toggling
  at `k` and thereafter. For every `n ≤ k`, its generated trace agrees with
  the never-toggle trace through the whole observed prefix `0..n` but
  disagrees at `k+1`. The laws themselves prescribe opposed transitions
  at `k`; this is not just two outcomes under one unchanged deterministic law.

Moreover, for **every** path `f` with `f 0 = true`, `scheduleOf f` records the
complete path's adjacent changes, and `f` satisfies that schedule's unique
deterministic profile. Therefore one fixed unrestricted class equals the union
of all individually deterministic schedule solutions. It can admit every later
rule reversal without any one governing schedule determining all possible
histories. The extracted schedule is **ex post, dependent on the entire
explanandum**, and is not an independently given mechanism, explanation or
epistemically available prediction. This limit is essential to the argument.

## Crucial omitted assumptions and controls

`Omissions` retains four controls in the same Boolean/model language:

| Comparison | What actually follows |
| --- | --- |
| Stable `Profile`, populated `Cell stable on n on` | All admitted stable paths follow the same copy law. There is no `SuffixComplete stable n`. Scientific stability is logically compatible with leaving ultimate grounding unexplained. |
| One open class, the admitted stable path `on` | `on` is admitted and follows `stable`. Suffix freedom allows a stable *admissible continuation*, rather than asserting that all histories really become chaotic. |
| Unrestricted profile `unconstrained` | It itself projects universally, but forbids no future transition and is nondeterministic. Our result forbids substantive future-excluding *universal* projections, not every tautological/procedural law statement. |
| `impossible` false initial condition with `on` observed | Its cell is empty, so arbitrary law projections pass vacuously. The main discriminator has explicit populated alternatives and does not use this escape. |
| Existing scopes `brute` and `grounded` | `brute` has **no** totality ground but can be paired with `stable`; `grounded` **does** have a totality ground and can be paired with `openFuture`. Grounding status and admissible law alternatives are independent model coordinates until bridged. |

The last control directly refutes the proposed **bare logical inference**
`¬ GroundedTotality → SuffixComplete` in the unrestricted product class. It
does not prove that a real brute world has stable laws, that a grounded world
has open laws, or that `GroundedTotality` is full ultimate adequacy. In #737,
`GroundedTotality` only means some supplied ground of `spacetime`; it does
not mean a necessary self-explanatory God or an adequate reason for everything.

## Whole-history explanation and law actuality: two debts, not one

The radical rival must answer **the same explananda** as a grounded-law account:

1. **Which whole history obtains?** #736 shows that an invariant whole
   reason-vector cannot be transformed by arbitrary information-only operations
   into an entailing selector when accessible different presence histories share
   that vector. #743 adds individually unique deterministic laws with identical
   finite observations and represented populations, without showing why the
   actual law rather than its rival obtains. A Humean best-system description
   can be *true of* the full selected mosaic while the question *why that mosaic
   is actual* remains open. The standard here is **entailing selection**,
   not a theorem that all adequate explanation must entail its effect.
2. **What fixes the laws' continuing operation?** Under the radical thesis,
   no constraint on later law schedules is supplied; every future copy/toggle
   pattern can be a distinct, individually deterministic complete history.
   The universal law projections that would prohibit some transition fail by
   the theorem. Observed regularity alone does not supply a stable cross-time
   restriction. To make robust global forecasts the opponent owes a warranted
   genuine restriction on admissible law schedules, a qualified propensity or
   exception structure, a necessary/dispositional nature, an actual mechanism,
   or a frankly limited methodological rule. Simply labeling the observed
   schedule a law *after the fact* does not select or constrain it.

These debts combine **only under the strong radical premise**. The proof does
not identify lack of ultimate explanation with unrestricted admissibility;
a restriction on law schedules is an additional substantive metaphysical
commitment whose actuality and warrant remain to be explained. The stable
model control and the existing comparisons in #737/#743 preserve this boundary.

At #1801, the dispute about existential inertia is even more specific:
a law plus **earlier existence** may explain a *later state or continuation*
without thereby offering a ground of the complete law/actuality conjunction.
If the law-fact is grounded by precisely the whole-history fact it purports to
ultimately ground, using that same grounding relation in both directions
conflicts **conditionally** with its independently defended asymmetry. Neither
whole-history law-supervenience nor grounding asymmetry, nor an actual present
productive sustaining requirement, is supplied by this module. A law of
*state* does not automatically govern the continuing *existence of the same
received-esse bearer*. The #1801 same-bearer and explanatory-status bridges
to `40a97664` remain **OPEN**, not silently settled by Bool state tokens.

## Provisional comparison and exact open bridges

As of the baseline `4aab093cc06bc1924bdf8067bd5780e11f438770`, the
strong radical rival has a genuine **conditional disadvantage** for global
law stability: it cannot simultaneously grant unrestricted future admissibility
and claim one all-history deterministic/future-excluding transition law, or
a record-only uniformly correct later forecast. This follows from a precise
model-theoretic contradiction, not an appeal to the psychological unpleasantness
of chaos. Its rational reply may reject the universal guarantee criterion,
restrict its metaphysical alternative set, defend a brute stable law or adopt
qualified empirically successful but fallible inference. Those are distinct
positions and must be reassessed under their own commitments.

It remains an **OPEN philosophical bridge** to infer from mere lack of a
necessary foundation that all possible future transitions or every law schedule
are ontically available. It is a further **OPEN bridge** that a real adequate
ultimate explanation must select this law/history in the strict #736 sense.
Theist accounts also owe a substantive account of how their proposed ultimate
ground sustains the particular governing structure and makes actual law use
and epistemic access possible. An unexplained choice by a necessary being
does not become an explained law schedule just by being attributed to God.

The most discriminating next test is therefore a defended **modal/causal
restriction principle about change in laws**, paired with a counterfactual
model at the same ontology and observed history. Does the radical rival
actually affirm arbitrary future law schedules, or only absence of ultimate
reason? What independently warrants the selected restrictions on whichever
side asserts them? If a law is said to ground whole-history actuality, test
the same fact/ground direction rather than transferring the result from a
mere law of state succession.

## Provenance, challenge and verification boundary

- Exact reuse: `TruthCore.Epistemology.UltimateExplanation.Profile/Follows/Cell/Deterministic/openFuture/stable/on`, `TruthCore.Explanation.LawActuality.UsesRecord`, `TruthCore.Modern.Hume.Regularity.GroundedTotality/brute/grounded`, and `TemporalHistory.History/CoherentAtNow` plus `HistoryContrastive.SameHistory`. No new logic, agent, evidence authority, grounding ontology or source claim.
- Prior #737/the pinned Hume *Enquiry* IV/V material compares finite past
  observations to future continuation; #736/#743 notes pin the global
  explanation and law actuality comparisons. Leibniz *Monadology* §§32,
  36–38 is the inherited PSR contrast; no new exact historical quotation or
  source attribution is asserted here. Source fidelity and the rival's
  metaphysical applicability must be judged separately.
- Frozen new Challenge:
  `TruthCore/Results/Explanation/NoFoundationLawChaos/Challenge.lean`, SHA256
  `c6b58fafc294479ea27516f8661d97532b2ae32240ffbc4339c4345bcabbcbed`.
  The `Solution.lean` proof is an independent draft consuming this unchanged
  Challenge interface.
- **Verification status:** no Lean/lake and no prepared `truth` CLI are present
  in this local research clone. Kernel, theorem binding, Comparator and NanoDa
  checks, the exact-head build and independent final-outcome review remain
  required. Neither this written proof draft nor its theorem names should be
  called mechanically certified until those checks pass.
- **Root impact:** four new analyst statements, premise-free conditional
  arguments, inference records, result records and Comparator configurations
  were generated from `specs/no-foundation-law-chaos.toml`. Existing root
  routes, premise statuses, closure flags and source claims were not changed.
  Expected root-frontier impact: **none**; exact `frontier-diff` remains pending
  the coordinator's CLI/CI. The live connection is an explicitly proposed
  bridge to the ultimate-ground and persistence explanatory comparison, not
  an already established root entailment.


## Upstream recombination/closure checkpoint — 2026-11-23 (#1867)

This section extends the earlier suffix-complete downstream results, without
re-proving their forecast, law-projection or strict-norm consequences. The new
certificate is `NoFoundationLawChaos.RecombinationFork` and its result record
`765d8679-3405-4276-be0f-f71b8248b863`. Its scope is a fixed set
`allowed : Trace → Prop` of **complete** Boolean histories, intersected with
the same `Cell (openFuture n) on n` observed through `n`. The selector is
not itself a grounded law, an explanation or metaphysical accessibility.

### Argument graph and exact assumptions

```text
U: no sufficient ultimate why-this-total-order explanation
  X→ N: no essential/governing/modal transition constraints       [OPEN]
  X→ R: local temporal recombination (same history selector)     [OPEN]
  X→ C: prefix closure of the admitted infinite-history class   [OPEN]

Population + R (OneStepRich) ──[Lean conditional]──> F (FiniteRich)
F + C (PrefixClosed)        ──[Lean conditional]──> S (WholeSuffixRich)
S ──[Lean-only adapters, unregistered; then existing #1809]──> D1:
  no record-only exact forecast at a later index, no deterministic or
  future-excluding Profile holding on every admitted history
S at every cutoff, one fixed selector
  ──[Lean-only adapter, unregistered; then existing #1808]──> D2:
  an additional stance's OWN strict guarantee norm + positive
  entitlement leads to its internal contradiction

Whole-order explanation (#736/#735), ontology of law (#743), epistemic
norms (#932/#737) and the God-existence stage (#143):
  U-vs-necessary-ground comparisons remain relevant;
  U→R, U→C, ontic actuality, access and same-source production are OPEN.
```

Here **R** is precisely the `OneStepRich` *complete-history*
extension property: given an already allowed history and a cutoff after the
observed record, choose either next bit while keeping the previous finite
segment; the resulting history must again be allowed by **the same selector**.
This is not merely permission to describe a local patch independently of
global boundary conditions. **F** allows a *different complete extension for
each finite cutoff*. **C** asserts that one particular infinite candidate
whose every finite prefix is individually extendable is itself allowed.
C is not implied by recursively repeating R; the witnesses for each cutoff
may be different. With a populated cell, R gives F by ordinary finite
induction. F+C then gives S by applying C to each spliced target history. No
ontic absence-of-foundation premise occurs in either Lean implication.

Mathematically, the F+C→S step is the standard Cantor-space fact that a
closed set dense in a cylinder contains the whole cylinder, and the
eventually-constant countermodel is the standard dense-but-not-closed set.
The progress here is the application, the exact separation of R, F, C and
population as distinct premises of the law-chaos inference, not new
mathematics.

**Adapters to the downstream certificates.** S is stated over a global
selector (`WholeSuffixRich allowed n`), whereas #1809's `certificate` takes
`SuffixComplete p n` and `UniversalProjection p q n` over a Profile cell, and
#1808's `internalDiscipline` takes `BothSuccessors s` over `Stance.admits`.
`TruthCore/Results/Explanation/NoFoundationLawChaos/Adapters.lean` bridges
both formally. `wholeSuffix_profile` shows that a Profile `q` holding on every
selector-admitted history is suffix-complete and universally projected on its
own cell, so `wholeSuffix_future_total`, `wholeSuffix_no_deterministic` and
`wholeSuffix_no_forecast` are #1809's conclusions for the selector.
`selector_bothSuccessors` shows that one fixed selector with S at **every**
cutoff gives `BothSuccessors` for the stance admitting exactly the
selector-admitted histories (using `splice n (fun _ => true) = on` and
`splice n (delayedFailure (n+1)) = delayedFailure (n+1)`), and
`selector_internalDiscipline` composes it with #1808. These are Lean-only
lemmas, not registered corpus results, and they connect only the formal
hand-off: whether any real law space satisfies S is the OPEN applicability
question above.

### Three contrasting populated selectors

| Fixed complete-history selector (all share the observed prefix) | R / F | C | S | What this establishes |
| --- | --- | --- | --- | --- |
| `finiteSwitchClass` = eventually constant (finitely many switches) | yes / yes | no | no | At every finite cutoff the proposed pattern can be realized and then stabilized; the single infinite alternating trace is excluded. A stage-rich nonempty rival does **not** admit all infinite outcome traces (and their ex-post `scheduleOf` codings). |
| `stableOnlyClass` = just the always-true history | no / no | yes | no | A positive stable history with strict law restriction can be closed. Closure alone does not create choices. The separate `Omissions` certificate already permits this alongside `¬ GroundedTotality brute`. |
| `allHistoryClass` = every Boolean trace | yes / yes | yes | yes | A coherent fully unrestricted comparator; the downstream chaos certificate applies only once this strong selection is warranted. |

`emptyHistoryClass` satisfies R and C vacuously, but fails S, so actual
**population** is an additional necessary hypothesis for deriving F from R.
It is not a candidate view of our populated world. These selectors are
structural mathematical controls, not independently certified metaphysically
possible universes. The alternating trace is a complete, countably infinite
path; it differs from every eventually constant path at arbitrarily late
times. A single finite switch, a finite but unbounded number of switches, and
an infinite sequence of switches must not be conflated.

### Positive grounds and limits of the disputed transitions

**Why might R hold?** A Humean recombination advocate can argue that local
successor configurations have independent modal standing and that there are
no cross-time constraints beyond the preserved past. This can make the
one-step substitution plausible, especially for explicitly stipulated
independent Boolean states. However, independence of intrinsic local qualities
is *not yet* independence of entire governing law schedules. A single
time-independent law, conservation invariant, global boundary value,
dispositional essence or dependence relation can forbid the replacement
even if the altered finite state-description is logically consistent.
To apply R, the advocate must show that every chosen next outcome has an
admissible **complete** continuation under the actual intended modality
and retained background, rather than stipulate the conclusion.

**Why might C hold?** If every admissibility exclusion has a *finite local
witness*, then the complete-history class is closed under agreement on all
finite prefixes: any excluded candidate has a finite prefix that excludes all
its completions. For one fixed ordinary `Profile` with initial value and
time-indexed pointwise transition constraints, a failure of `Follows` occurs
either at time zero or at one finite successor pair. Thus its class of
satisfying complete paths has this *mathematical* closure property
(`Adapters.follows_prefixClosed : ∀ q n, PrefixClosed (Follows q) n`, a
Lean-only lemma, not a registered result). This is a
positive structural rationale for C when **all** admissibility constraints
really are of that form. It does not establish that ontic/metaphysical
admissibility is exhausted by those local law equations.

Conversely `EventuallyConstant` is an explicit *global tail requirement*:
no fixed finite prefix identifies failure, because it can always be completed
by a constant tail. It is a coherent extension policy with F but without C.
This matters because metaphysical possibility may be sensitive to global
histories, persistence, infinite actualization requirements or other
non-finitely-witnessed restrictions, rather than only local safety constraints.
First-order logical compactness or arbitrary mathematical limit-taking does
not by itself prove the ontological admissibility of the **specific** limiting
trace. A further modal closure or finite-witness account of all exclusions
is the live philosophical premise. The model does **not** prove that
eventually-constant global constraints are actually fundamental.

**Law schedules versus state outcomes.** The old `LawSwitch` establishes
that every Boolean history with the specified initial state has an *ex-post*
deterministic copy/toggle schedule. That mathematical coding does not show
that distinct schedules are independently physically available or can change
the *fundamental* governing structure. To derive actual law arbitrariness,
R/F/C must apply to a justified domain of law configurations with fixed
bearers, dispositions, consistency conditions and time horizon—not merely
to output bits. That application bridge remains OPEN.

### Explanatory and epistemic alternatives at matching scope

| Proposed stopping/explanation | Continued actual stability | Alternative histories / modal restrictions | Remaining why-question and epistemic test |
| --- | --- | --- | --- |
| Brute cosmic order | Its actual long-lived regularity can be taken primitive; no inconsistency follows. | The selector may be stable, finite-switching or otherwise restricted; no particular modal space follows from primitiveness alone. | Why this exact mosaic and its stability, rather than another? Successful induction may be defeasible and empirically warranted even if the whole-order why-question is left brute. |
| Humean best system | Summarizes, predicts and unifies the actual mosaic by a comparatively simple informative system. | Best-system lawhood is not automatically a governing restriction on *metaphysically possible* alternative mosaics; the chosen recombination principle must be supplied. | Explains pattern-under-description and practical theory choice; whether it adequately explains *why this mosaic obtains* is the exact #735 contrast. |
| Primitive governing law | Actual law may be a real modal constraint ruling out contrary transitions even without an explanation of its own actuality. | A fixed transition principle provides a genuine admissibility restriction. | Its instantiation, persistence, exceptions and epistemic detection require separate assessment; the primitive itself is an allowed stopping point. |
| Dispositional/essential powers | Stable effects follow from the powers that concrete subjects possess. | Intrinsic identities and powers constrain which successors are coherent, potentially rebutting R at a definite local step. | The actuality and distribution of those powers and the composition of the whole order may remain open; test concrete causal conditions rather than an opaque label. |
| Necessary impersonal ground | A necessary structure might constrain law space. | Necessity of the bearer alone does not select the actual contingent law unless the same relation is shown to do so. | Needs actual productive/grounding efficacy, explanatory adequacy and empirical access; a necessarily existing idle structure is no sufficient account. |
| Classical-theistic source | A necessary intelligent source may provide a unified reason for the order and its continued applicability. | Sourcehood does **not** by itself show why this particular world/law is selected or exclude unexplained contingency in the source's choice. | Same source, actual causal activity, sufficient contrastive reason, law persistence and intelligibility to finite inquirers are separate OPEN burdens (#735/#737 and intellect/will routes). |

The **provisional assessment** for the stated #1867 target is that the
unqualified inference **U → S is not supported**. The already certified
brute-stable control (`Omissions`) shows only that the bridge-free inference
fails in this formalization: U-style ungrounded totality and a stable law
coexist in the product model. It does not show that a substantive U→R or
U→C bridge is false. R has a substantive
recombination rationale **only** for modalities satisfying genuine
cross-time/local independence; C gains conditional rationale from
finitely-witnessed exclusions, but does not follow from F. C and U are
independent by construction in the product model; no theorem relates U to
selectors, so "C does not follow from U" is a fact about the model's shape,
not a separate theorem.
U alone is consistent in this formalization (`Omissions`). Whether naturalism or U undermines epistemic entitlement
(EAAN, e519065f) remains OPEN and is not assessed here. Under S,
all-continuation **certainty**
fails; under S plus a rival's *own* strict certainty norm plus positive
entitlement there is an internal conflict (#1808, through the Lean-only
adapter above). Scientific induction,
probabilistic calibration, explanation conditional on laws and robust
practical decisions remain possible without deductive guarantees; what
warrants their real-world reliability must be evaluated separately (#737,
#932, #1734). A bare U claim is not formally self-contradictory.

**Next test (reopening condition):** obtain a concrete, independently
defended ontology of laws and metaphysical recombination that both permits
unrestricted successor substitution and shows *all* relevant global
admissibility exclusions are finitely witnessed. Run the identical-history
test on an actual law-configurations domain, not just on state traces. If
that package survives, instantiate S and only then compose the existing
#1809/#1808 epistemic consequences through the adapters. Alternatively,
identify a specific
necessary or dispositional restriction that independently refutes R at the
same fixed history and law identity; compare its explanatory actuality
with the brute stable and necessary-ground options. The #735/#737
God-existence-stage link is **comparative**; no new root route, premise
discharge, anti-atheism theorem or stronger interpretation is claimed.

**Connection plan (OPEN, not an existing route).** #735's whole-order
explanation target is `STMT-LEIBNIZ-SERIES-SUFFICIENT-REASON` (702e4171),
which does not itself reach the root. The nearest root-route node whose
rival this work prices is the local existence PSR for contingents,
"Every being contingent at w has some reason for its existence" (608a262d,
bare), which reaches `STMT-CATHOLICISM-TRUE` through B2 (a8823bd2), the
First Way necessity step and the quarta via route (fa24c576). Its rival is
brute contingent existence. The missing bridges are (1) a sense-checked
bridge identifying the denial of 608a262d (no #312 reason token for some
contingent being's existence fact at w) with U here (no `GroundedTotality`
of the supplied #737 scope for the whole order of transitions): the
explananda and the relations differ; and (2) the U→R and U→C applicability
bridges above. Even with both, the result would bear only on the comparative
cost of the brute-contingency rival, not derive 608a262d, and D2 binds only a
rival that endorses the strict norm. Blocker: no independently defended
ontology of law recombination instantiates R and C, and no reason-token to
grounded-totality bridge has been formalized.

**Verification and review tracking:** The new theorem's Challenge, Solution,
spec, result/comparator record and this note are proposed on PR #1874 for
#1867. An independent semantic challenge of that PR (repair pass 1) found
one unbuilt connection drawn as existing (now built as Lean-only adapters),
one unsupported universal non-entailment claim about naturalism (replaced),
and several wording and scope overstatements (corrected). Mechanical Lean,
binding, Comparator, NanoDa and the computed frontier-diff are evaluated on
the exact PR head in CI.


## Causal propagation of a brute contingency (2026-11-23, #1867)

**Proposed checkpoint; independent semantic challenge and canonical validation
pending.** Owner hypothesis: an existential exception might not remain
isolated, because a being that obtains without a reason can exercise causal
powers whose effects influence the rest of reality and all empirical
evidence. Investigate an analogue of explosion, but do not identify
metaphysical possibility with classical entailment from a contradiction.
This is an upstream continuation of #1867, not a repeat of #1874/#1809's
suffix theorem, and does not edit #1910's exemption analysis or #1904's
historical-evidence note. Analyst formulations; no new source attribution.

### Three different propagation theses

Fix actual world w, the same rigid concrete candidate b, an accessible
absence alternative v, and a specified family of actual positive empirical
facts Q. Grant for this investigation that b exists contingently and has
no adequate actual existential reason. That is stronger than the mere
absence of a selected causal predecessor. The formal token-level
`b36104ba` rival is related but not an adequacy certificate.

1. **Ultimate explanatory dependence.** If an adequate *complete*
   explanatory account of a fact q must account for the actuality of b
   (not merely cite b or give a conditional mechanism), and b lacks an
   adequate actual reason, no such complete account of q succeeds.
   Proof: a purported successful account would, by the explicitly stated
   completion condition, supply an adequate reason for b, contrary to
   the premise. This is relative to the complete-account standard; no
   new theorem says every explanation must meet it. A real causal
   dependence can justify including b in a complete account, but graph
   ancestry or mere material implication does not certify explanatory
   inclusion. The local mechanism can explain q and thus q is not
   necessarily brute. The missing reason is upstream.
2. **Modal transmission.** Suppose for each q in Q, q actually obtains
   and q's obtaining in any accessible history requires the existence
   of b in that history (not necessarily at the same time if q is an
   effect of an originating act). With the admitted b-free alternative v,
   each q fails in v. Hence each q is contingent at w on the chosen
   scope, with one common absence witness. For existential facts this
   is the strong selected dependency reading of
   `STMT-DEPENDENCE-EXCLUDES-BEING-WITHOUT` (000e1f65), not mere
   causal ancestry. Event/state facts require their own interpretation
   bridge. For a sustaining source, retention of the bearer and the
   relevant concurrent receipt must be established; for an originator,
   its existence somewhere in the relevant complete history is the
   issue. This does not establish unrestricted independent variation
   of the q's or the failure of empirical knowledge; v might have no
   observers at all.
3. **Arbitrary selection of empirical values.** Fix the background
   laws and retained conditions, a nonempty set of admitted possible
   source configurations U, and an observation map F into the
   outcomes for the specified empirical facts. Here U is a mathematical
   parameter, not the earlier section's abbreviation U for no ultimate
   explanation. To make terminology unambiguous below write S for
   the source-configuration set. Individual variability means that
   each selected Boolean output coordinate takes both values on F(S).
   Joint arbitrariness means that F(S) contains every proposed joint
   assignment in the selected output domain. Neither follows from
   explanatory incompleteness; individual variability is strictly
   weaker than joint arbitrariness. A complete deterministic map can
   still satisfy the latter if the source has enough admitted
   configurations and the map realizes their distinctions.

The first conclusion is a sense in which a brute root's explanatory
deficit can propagate to an entire order **even if every physical law
and every local mechanism is stable**. It is not the claim that all
facts become ontologically uncaused. The second gives shared contingency,
not arbitrary laws. The third is closest to the requested explosion,
but requires an explicit modal and causal amplification premise.

### Why connectedness is insufficient, and what is sufficient

Reuse #1399 / merged #1406
([causal transitivity](causal-transitivity-1399.md), result
1ab3858a-b0cb-4475-b22d-b397858a76a2). In the actual Boolean
intervention model X=Y=Z=1, Y=X and Z=(X==Y), intervention X=0
changes Y, intervention Y=0 changes Z with X held actual, yet
intervention X=0 leaves Z true after recomputation. The registered
result also proves the pure binary chain conditional and the
compensating-direct-effect boundary. Do not read transitive closure
as actual difference-making or existence-giving. Even complete
causal connectivity in a selected graph is not a certificate of
universal influence. Conversely, a positive account of productive
contribution may retain causal ancestry despite endpoint cancellation;
that is not enough to show the endpoint could be different.

A second discriminator isolates the quantifiers. One free Boolean
input b with a deterministic copying mechanism gives n outputs
(b,b,...,b). Each coordinate can differ from its actual value, but
there are exactly two joint vectors, not 2^n when n>1. The input
could stand for the presence of a stipulated trigger in an admitted
alternative; that requires an interpretation of real existence not
given by the bit. Neither the copying law nor the many outputs
creates new independently selectable information. In general a
deterministic map from m allowed configurations has at most m
distinct joint output vectors. A single presence/absence choice
with everything else fixed cannot generate unrestricted assignments
of even two binary facts. It can, however, affect every output
at once in an appropriate model. This makes the owner's common-mode
intuition precise without claiming classical explosion.

### Stronger mechanism: stable laws, unrestricted empirical histories

The #1874 investigation derived suffix richness from one-step
recombination and prefix closure on **output traces**. Here consider
an alternative *causal implementation* of suffix richness with
the same fixed transition at every time, rather than a changing
law schedule or an unconstrained transition. It is a mathematical
surrogate for causal powers, not a model of concrete existential
actualization.

Let the initial state be a Boolean tape a : Nat → Bool. At each
step the one fixed deterministic transition shifts the tape one
place, L(a)(i)=a(i+1), and the observer reads O(a)=a(0).
After t shifts, O(L^t(a))=a(t), by induction on t (the stronger
identity L^t(a)(i)=a(i+t) is preserved by one shift).
Let the admitted initial tapes be a fixed class I. Then the set of
complete observed traces is exactly I: the forward inclusion is
the readout identity, and every a in I realizes itself as the
observed trace. Hence:

* If I admits every tape with the actual recorded prefix, every
  future observed suffix is admitted, despite the single fixed,
  deterministic microstate transition L.
* The same holds if I has the #1874 one-step richness, nonempty
  prefix cell and prefix closure, applied to initial tape values.
  The previously certified consequence supplies complete suffix
  richness of the tape class; the readout identity transfers it to
  the observed trace selector. This is a proposed mathematical
  application of the existing result, not a built Lean adapter.
* If I contains only the two constant tapes, the observed cell
  after the first read has a unique trace. If it contains the
  eventually constant tapes, all finite extensions are admitted
  but not arbitrary infinite traces. The *same* mechanism and
  observation map are retained. The decisive difference is what
  source states are admitted and how they propagate, not the name
  "deterministic".

The law L is deterministic on full tapes, not on the observed
single bit. #1809's all-suffix result can therefore defeat
restrictive universal **observed-bit transition** profiles without
contradicting determinism of the full state law. To use the existing
Profile-cell adapters the observed profile must admit the selected
traces; the full tape law is not itself a Boolean Profile. For
physical interpretation, a source containing arbitrarily selectable
information and a mechanism releasing it would suffice to make
arbitrary late outcomes compatible with stable local equations.
The unrestricted initial-state assumption is substantial. A
single brute concrete being need not have an infinite tape's
information capacity or even two independently variable powers.
Nor does absence of an explanation of its existence make every
initial tape admissible. The construction shows a pathway from
unrestricted source configurations to observed chaos that does
not need fundamental law switching; it does not establish the
required modal or physical application.

A finite check (Python enumeration, 8-bit tape with zero-fill
shift, first eight reads) found 256 distinct traces and 32
continuations after prefix 111. Copying one shared bit into eight
positions gives exactly two vectors with both possible values in
each coordinate. These are exact checks of finite controls only;
the infinite readout identity is the elementary induction above,
not a Lean-certified result in this checkpoint.

### The intruder question: why should the exception be contained?

The strongest philosophical challenge is not that no causal law can
coexist with an unexplained initial condition. It is whether the rival
can justify a **specific modal boundary** on new, unreceived causes
and their powers. Consider a proposed unexpected cause that would
bring about a particular admissible local effect. Distinguish:

* Is that sort of cause eligible to exist underived at all?
* If it is eligible, can it exist in this very causal background,
  at this place or moment, with these powers?
* If it can coexist, can its actual exercise reach the target without
  a compensating response or violation of a retained law?
* Can the choices be made jointly for many targets, including the
  relevant evidence and calibration apparatus?

An argument for broad propagation can begin with actual causal
mechanisms: localized changes can travel through interactions, and
a change in a shared upstream condition can change many downstream
facts. The explicit copying and shift mechanisms exhibit why this
is not a mere metaphor. A proponent of arbitrary underived local
causes would need a reason to deny the same kind of causes in
otherwise comparable regions. If the opponent's only ground for
admitting b is that contingent actuality need not have a reason,
that ground alone does not discriminate b from a candidate intruder.
This is an epistemic argument about the warrant offered for the
restriction, drawing on #756/B2's feature-relative parity, **not**
a modal rule that every distinct candidate is admissible. To infer
actual or possible intruders, defend a positive co-admissibility
principle (e.g. independently possible causal powers and compatible
background recombination). The joint powers, conservation/identity
constraints and endpoint efficacy must be retained, not read off
from absence of a reason.

A primitive, globally constrained stable history can answer the
intruder question: only its specified input configurations are
admitted and the full law forbids unlicensed additional causes.
A dispositional rival can appeal to a nature that constrains
which powers may be exercised in those conditions; a causal-isolation
rival can give an independently restricted interaction domain.
These are substantive ways to deny a step of the propagation
argument. Their explanatory cost is that if the law, its application
or the particular initial state is itself an unexplained contingent
fact, there remains an ultimate why-question (assuming the selected
complete-account standard). It does not follow that a constraint
whose obtaining is unexplained cannot genuinely constrain, or
that a necessary constraint must itself have a contingent bearer.
An independently justified essential prohibition of a new intruder
would defeat the proposed modal extension even if the actual
foundation were brute. The comparison therefore advances #1910's
exemption problem: a relevant restriction must constrain the
existence or exercise of the cause, not merely label one allowed
exception as fundamental.

### Epistemic propagation: correlated evidence rather than random facts

A common cause affecting evidence can matter more than merely
making an outcome contingent. Reuse the common-mode/local distinction
in [#1584](preface-connectivity-1584.md), and #737's record-only
and epistemic-warrant boundaries. As a simple application, let the
target truth p and an upstream offset b be Boolean. Every displayed
record r_i reads p XOR b under a fixed mechanism. (p,b)=(1,0)
and (0,1) produce identical records r_i=1 for any number of displays,
yet opposite p. A method seeing only these records cannot be
uniformly factive over both admitted cases. A genuinely independent
observation of the offset or target would distinguish them. For
a metaphysical application both populated alternatives, the
offset's causal efficacy, access to the relevant records and
the absence of independent disambiguating evidence must be
established; this is not a new proof of #1904's historical
underdetermination. The finite XOR comparison was checked for
all four assignments and eight repeated records.

The important potential implication is that **the same arbitrary
factor might affect the evidence by which an inquirer tries to
detect it**. Many observations need not be independent safeguards
against common-mode error. Under a justified restriction excluding
the offset, actual calibration, or a separately reliable process,
the rival can retain empirical entitlement. Even admitted
indistinguishable error scenarios defeat universal zero-error
guarantees, not by themselves defeasible, probabilistic or
externalist knowledge. Do not assign equal weights to alternatives
or infer a low probability of truth without a probability/selection
account. In particular this comparison does not establish
`STMT-ULTIMATE-GROUND-EPISTEMIC-NECESSITY` (e519065f): that
much stronger bridge explicitly retains genuine process reliability
and relevant evidence. Merely allowing a common-mode failure does
not show that the actual process is unreliable.

### Proposed assessment, root connection and next discriminator

High confidence in the distinction between upstream incompleteness,
common modal contingency, individual variability and joint
arbitrariness; also in the finite controls and fixed-shift readout
argument. Provisional philosophical preference for the limited
ultimate-dependence propagation principle when the complete-account
requirement and genuinely indispensable existential dependence are
warranted. This is a stronger comparative cost for a brute *common*
root than for one isolated brute entity, without an unexplained-fact
counting argument. No warrant yet for unconditional metaphysical
explosion. Retain the restricted primitive/dispositional account as
the strongest rival. A necessary source with an unexplained
contingent act or law choice must face the same completeness and
admissibility test; if intentional or other nonnecessitating
explanation is adequate, do not identify nondetermination with
bruteness (see #755 and #1910).

The root-route premise 608a262d (local existence PSR for contingents)
and B2 remain the intended comparative beneficiaries. The missing
links are actual explanatory adequacy of reasons, the applicability
of the complete-account standard to all relevant dependents, and
whether the rival's permitted source configurations and causal
powers have the necessary effective reach and modal richness.
The fixed-shift argument provides a concrete alternative to the
earlier law-switch route: defend source-state richness plus effective
transmission, not U→arbitrary governing laws. Once justified, the
existing #1874/#1809 downstream results can be reused on the
observed trace selector with the existing adapters, after checking
their exact hypotheses. No new support edge, premise discharge
or God-existence conclusion is claimed.

**Next test:** choose one real proposed brute-foundation ontology
(e.g. primitive necessary powers with a contingent base, or a
brute governing-law bearer), hold its positive laws/essences fixed,
and identify what excludes or permits a same-background unreceived
causal input with a power targeting the evidence channel. Test a
nonempty family of inputs with actual local joint conditions and
an admissible complete history, not just the logical consistency
of a description. If those inputs can be jointly varied, test
whether the fixed readout realizes the desired output patterns;
if not, identify the exact invariant that blocks them. Compare
that restriction and its warrant with the necessary-source rival
at the same scope. Revise toward global explosion only when a
substantive co-admissibility and reach principle survives this test;
revise against it for a positively warranted invariant that
allows a brute exception but forbids the proposed substitutions.
A claim about epistemic self-undermining also needs the rival's own
entitlement norm and relevant evidence conditions, as #1808/#737
already require.

**Claim/type self-sweep:** the prior #1399, #1874, #1809, #737 and
#1584 results retain their exact scopes. Nothing equates a Boolean
input, a tape or a record offset with a rigid concrete being.
No historical attribution, new graph proposition or Lean declaration
is introduced; the finite enumeration is not Comparator evidence.
Local CLI and installed conventions cannot be checked in this
connector-only checkout; independent semantic challenge and
canonical checks must still be completed before relying on this
checkpoint as reviewed.
