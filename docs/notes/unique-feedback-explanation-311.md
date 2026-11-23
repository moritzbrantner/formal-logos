# Unique feedback and whole-chain explanation (#311)

The state equations `a = !b`, `b = a && b` have one satisfying
Boolean pair, `(true,false)`. Their gates are nonconstant: negation
changes across its two inputs; conjunction changes when either input varies
with the other held true. These are logical constraints. They are not
world-local causal edges, temporal evolution, pure copying of plans, or
borrowed instrumental powers. Sensitivity is a truth-table property, not
an assertion that each single-bit perturbation at the solution changes
both outputs.

| a | b | First equation | Second equation |
|---|---|---|---|
| false | false | fails | holds |
| false | true | holds | fails |
| true | false | holds | holds |
| true | true | fails | holds |

`UniqueFeedback.Controls` certifies sensitivity, the satisfying witness,
and equality of every consistent state with it. The proof does not select
an observed boundary value or assume uniqueness. It eliminates the other
three states. This is a nonvacuous satisfiability/uniqueness control; no
explanation predicate is present.

## Reuse and nonduplication

- Merged #299's `EssentialPowerUnderdetermined.essentialPowerUnderdetermined`
  gives all-on/off solutions and cut responses. Its local rule is preserved.
- `LocalObservationSelectsSolution.localObservationSelectsSolution` supplies
  determinacy only after fixing an observation. This control needs none.
- `RegressDomains.CycleAndConverseBoundary` admits equal least/greatest fixed
  points on an intrinsic self-loop. That supplied intrinsic predicate is not
  used here; neither fixed-point selection convention is used.
- Pending #619 owns complete-presence-history contrasts and differing reason
  assignments on the same memberwise structure. It is comparison evidence,
  with no dependency on its unmerged declarations. Those assignments are not
  repeated here.

No existing philosophical conclusion is imported as a fresh premise.
The previous theorems are comparison evidence; the new result proves only
its own distinct finite control.

## Surviving explanation question

Mathematical solution multiplicity cannot be the entire objection to logical
feedback: the constraints here are satisfied and have no second solution.
This does not prove an adequate ontological explanation or prove its absence.
The strongest rival says that the intrinsic global structural fact explains
the satisfying state. A brute global fact and a non-well-founded grounding
account are distinct further answers. None is eliminated by this table.

To reject the structural answer, one must specify which obtaining fact needs
explanation, what counts as sufficient explanation of it, and why satisfying
these global constraints does not meet that norm. A whole-series PSR or a
contrastive requirement must enter explicitly; neither automatically implies
externality or rules out explanatory circularity. No notion of explanation
is defined to prohibit loops. Conversely, uniqueness alone supplies no
independent defense of those norms or of the global structural answer.

The issue's original plans bootstrap still requires a richer interpretation:
these gates are not an inventor-free copying history. No inference from lack
of an inventor to impossibility, from consistency to metaphysical possibility,
or from explanatory dissatisfaction to an original causal source is made.
EXP-SCOPE, EXP-LOCAL-TO-GLOBAL, EXP-NONCIRCULAR and EXP-ULTIMATE remain open.
Source attribution remains paused; no historical claim is added.

## Self-actualization of existence is a different problem from feedback

The bearer of a productive **act** and the being whose **existence** the act
produces are distinct sorts of explanatory relatum, even when the same being
is named on both sides. The companion Lean certificate
`PerSeCausalLoopImpossible.noExistentialSelfActualization` models an act `a`
and an existential token `inl x`, rather than identifying an event or an
explanation token with a concrete being:

1. An occurring act presupposes its bearer: the bearer's existence-token is
   prior to the act (`hBearerPrior`). This is the substantive formulation of
   "it must already be in act to exercise a power"; its applicability to a
   proposed kind of creation needs argument, not a name change.
2. If the act actualizes a being's existence, the act is explanatorily prior
   to that existence-token (`hProductPrior`). This says *existential
   production*, not mere maintenance, dependence, or temporal feedback.
3. Priority is irreflexive (`hNoSelfPrior`) and transitive (`hTrans`). These
   are shared Aquinas-reading predicates applied to the **mixed** domain of
   being-existence tokens and acts. Their extension to that domain is an
   explicit, still-open metaphysical bridge.

If `a` produces the existence of its own bearer `b`, the first two interfaces
give `existence(b) ≺ a ≺ existence(b)`. Transitivity contradicts
irreflexivity. **Lean proves this conditional**. No clock or initial instant
is used: the paradox is explanatory/ontological, not a chronological claim.

The omission controls certify the exact load-bearing property of the order:
on two tokens, `x ≠ y` permits the cycle if transitivity is removed;
universal priority permits it if irreflexivity is removed. A separate
three-rank finite model (`otherBearerCanActualizeExistence`) permits an
existing bearer to actualize the existence of a **different** being while
satisfying all four premises. The result is therefore a targeted prohibition
on productive self-origin, not a prohibition on ordinary productive acts.

### Rival cases and missing routes

| Case | What this result says | Further burden |
| --- | --- | --- |
| Efficiently producing one's own existence | Impossible **given** the two priority interfaces and a strict transitive order. | Defend those interfaces for the exact proposed kind of act. |
| Ordinary self-change or self-maintenance | Not excluded: the produced item is not the bare existence of the act's bearer. | Distinguish the changed respect or persisting state from the originating existence fact. |
| Time traveler supplying a plan to an earlier inventor | Not thereby an existential self-actualization: an information loop may be a consistent constraint without an originating productive act. | Show that the loop actually generates the existence of its own bearer, not just information. The unique-feedback model already defeats a claim of universal logical inconsistency. |
| Contingent thing explaining its own existence by its essence | `BruteFoundationExplanations.contingentExcludesNecessaryNecessitatingReason` supplies the modal contradiction **if** that intrinsic reason is necessary across the relevant worlds *and* suffices to necessitate that particular being. | A contingent, world-local, or nonnecessitating explanation does not generate that contradiction merely from the fact that the being fails to exist elsewhere. |
| Necessary being's intrinsic reason for existence | Not efficient self-production and not refuted by this theorem. | Argue for its actuality and genuine explanatory adequacy; calling it necessary is not an instantiation proof. |
| Distinct predecessor for every contingent being | Acyclic, infinitely descending support is not ruled out. `BearerRegress.ChainBranchModel` already certifies a chain with no terminus, and the new positive control shows distinct productive bearers are compatible with the local order. | Defend a ban on source-free non-well-founded **existential production** or a stronger global explanatory/PSR principle; also deal with brute contingent termini. |

The strongest reply is that a contingent individual can have an intrinsic
*nonnecessitating* explanation at just those worlds where it exists, or that
a consistent whole feedback structure has an adequate global explanation.
Neither reply has been shown adequate, but neither contradicts the local
Lean theorems as stated. Conversely, the proof cannot be promoted to a
necessary being by quietly assuming that every actual contingent being is
productively actualized by something, that all such precedence is governed
by one strict order, or that every unbounded external chain is impossible.

### Origin-to-exercise warrant reassessment (2026-11-12)

The separate root-reaching result
`OriginExerciseBridge.noSelfOriginFromNoSelfProduction` consumes the **OPEN**
`OriginHasProductiveExercise` bridge: every `CausesOrigin c x` edge has an
*occurring* exercise `a` with `bearer a = c` that produces `x`'s existence.
The result was verified on PR #1526, head `fe55756c`, with full CI and a
completed finding-free Codex review. Since #1610 a sibling result,
`OriginExerciseBridge.SelfEdge.noSelfOriginFromSelfExercise`, reaches the same
conclusion from the weaker self-edge bridge `OriginHasProductiveSelfExercise`;
the frozen universal-premise result above is unchanged and stays a support
alternative. Neither verifies this bridge's applicability. The warrant question is now substantially narrower than whether
all things generically called causes involve positive production.

**Positive argument for the selected productive reading.** A merely capable
builder does not build a house; the builder *building* is the actual productive
cause. Aristotle distinguishes potential and actually operating causes in
*Physics* II.3, especially the builder/building example around 195b16-21.
On a positive, efficient reading of origination, attributing the resulting
coming-to-be to `c` therefore calls for the actual exercise of `c`'s causal
capacity, not merely a static dependence of the outcome on the presence of `c`.
If it originates `x` rather than merely modifies or maintains `x`, the
productive exercise must terminate in `x`'s coming-to-be. This supplies a
conceptual **warrant for** the bridge in that reading; it does not deduce the
whole universal quantified bridge from a historical example. In particular,
the maker of a house may cause a new composite from existing matter without
producing its matter ex nihilo. The intended `produces a x` is production of
the *being of the resultant individual*, not of all its constituents out of
nothing. It is the same `produces` as in `NoSelfProduction`
(DEF-NO-EXISTENTIAL-SELF-PRODUCTION): both premises of the argument read the
shared parameter as production of `x`'s being, never as mere production of
`x`'s coming-to-be. The builder therefore illustrates only the
actual-exercise requirement. A builder is the standard example of a cause of
a house's *becoming* rather than of its *being* (Aquinas, *ST* I q.104 a.1),
so the builder case is not an undisputed instance of `produces` in that sense.
The step from "c is responsible for x's coming to be" (`CAUSE_4`) to "an
exercise of c produces x's being" is part of the bridge's OPEN content
(DEF `9022c4bf`, statement `be90bb15`), and it is the step that the builder
case leaves open.

**Why the bridge is universal and its self-edge sibling.** The bridge
quantifies over every `CausesOrigin` edge, but the argument `e9a9eeaf` uses
only self-edges. The universal form (statement `be90bb15`, DEF `9022c4bf`) is
kept as the productive reading of `CAUSE_4` itself, because its warrant (the
actual-exercise requirement) is stated generally. Since #1610 a sibling
argument (`noSelfOriginFromSelfExercise`, Challenge
`OriginExerciseBridge.SelfEdge`) consumes the weak self-edge sibling
`OriginHasProductiveSelfExercise` (`∀ x, CausesOrigin x x → ∃ a, Occurs a ∧
bearer a = x ∧ produces a x`, DEF `62acf1f0`) with the same NoSelfProduction
premise. That proof shows the strong version is not needed for the
conclusion. `e9a9eeaf` and its frozen Challenge are kept unchanged as the
earlier support alternative, with no `strong_version_needed` reason (the
frozen-Challenge rule, invariant 12, forbids re-pointing it). The universal form strengthens the sibling
(verified instantiation result `selfExerciseOfExercise`). Their certified
difference (#1598) is `NonSelfOriginHasProductiveExercise`: every origin edge
is a self-edge or is realized by its source's productive exercise, that is,
classically, the bridge for edges between distinct beings. The premise-free
`universalOverSelfExact` proves universal ⇔ self-edge ∧ delta without decidable
identity, and the other-only frame (`true` originates `false`, no exercises)
separates them: the sibling holds there vacuously and the universal form fails.

Warrant difference. The sibling follows from the universal form, so it has at
least its warrant, and every defeater of the sibling defeats the universal form.
The converse fails. The builder, a cause of a house's becoming but not of its
being (*ST* I q.104 a.1), and Hall-style omission and prevention cases have
distinct relata and bear only on the delta. The broad dependence reading of
`CAUSE_4` behind Hall's cases bears on the sibling only through a self-edge
such as the Smith whole below, which stays OPEN. The sibling keeps only the
self-edge case of the coming-to-be-to-being step. That case is where the Smith/Newman whole-universe
dispute sits: whether a whole said to originate itself through its constituents'
reciprocal origination bears an exercise producing its own being. That dispute
is not lightened by the weakening and stays OPEN. The weakening removes
irrelevant exposure, not the live objection, and it establishes neither bridge.

**Non-temporal activity and the divine case.** Aquinas, *ST* I q.45 a.3,
distinguishes creation from motion or change and identifies active divine
creation with divine action/essence rather than a temporally new accident in
God. Therefore `Occurs a` may mean that a causal activity obtains, **not**
that a distinct temporal event begins or that God's action is an accident
ontically separate from God. Conversely, treating `Sum Being Exercise`'s
different formal tags as proof of a real distinction or a strict priority
between divine essence and divine action would be illicit. The priority
interfaces must receive their own metaphysical warrant.

**Specific rival mechanisms and their exact relevance.** Ned Hall, *Two
Concepts of Causation*, §§1,5,7, argues for a difference between
counterfactual **dependence** and event **production**; omissions can figure
as causes in the former sense without being productive exercises. This is a
substantive challenge to the bridge **if** `CausesOrigin` is interpreted broadly
enough to count absence-based dependence as originating causation. It is not
yet a counterexample to its narrower positive/efficient reading. In a more
challenging case, Gott and Li, *Can the Universe Create Itself?* (1998),
§§IX–XI, give self-consistent examples of closed-timelike-curve spacetime/field
configurations and **separately propose** that a later-generated baby universe
might be identical to the earlier universe. That identification is a
conditional physical scenario, not a solved dynamical self-generation model.
It is a concrete candidate **phase/region-loop mechanism** rather than a bare
logical permission slip, but it does not alone prove that a single whole being
has an exercise producing the total existence of that same whole. A critical
extra step is the part/whole and identity transfer
`causes(phase₂, phase₁)` to `CausesOrigin(universe, universe)` together with
`produces(act_of_universe, whole_universe_existence)`. If that step can be
justified, the rival challenges at least one of the bridge's bearer/product
scope or the mixed priority properties; the present result does not refute it.
The CTC solution plus conditional baby-universe identification supplies a
meaningful research target, **not** an observation that our universe has this
topology, an established baby-universe loop, or a proof of metaphysical
self-production.

Primary-text navigation inspected for this reassessment (not newly pinned
corpus claims or source-fidelity certificates):

- Aristotle, *Physics* II.3: https://etc.usf.edu/lit2go/98/physics/1663/book-2/
- Aquinas, *Summa Theologiae* I q.45 a.3: https://www.newadvent.org/summa/1045.htm
- Ned Hall, *Two Concepts of Causation*: https://fitelson.org/269/Hall_TCOC.pdf
- J. Richard Gott and Li-Xin Li, *Can the Universe Create Itself?*:
  https://arxiv.org/abs/astro-ph/9712344

**Overall provisional judgment (2026-11-12).** The positive efficient
origination reading makes an actual productive exercise a strong conceptual
expectation. This **favors** the bridge within that reading, especially over
an interpretation that calls a mere potential capacity an actual originator.
It does not establish unrestricted `CausesOrigin` as productive. Hall gives a
positive broader-causation alternative; Gott–Li gives a concrete cyclic
cosmology whose precise mapping to whole-existence production is unsettled.
No actual-world self-origination, unconditional no-self-origin law, and no
necessary-being conclusion is established or defeated here. Reversal tests:
(1) identify a bona fide `CAUSE_4` origination caused only by an omission or
dependence, with no positive exercise; (2) provide an identity-preserving
mapping of a CTC model's phase edges to **whole** self-origin, including the
actual bearer/product claims; (3) justify or reject strict mixed priority for
non-temporal creation. These are discriminating tests, not generic pleas that
an unknown counterexample might exist.

### Further strengthening: event-loop self-causation and a weaker priority law

**A stronger positive rival.** Anthony E. Newman, *Causal Loops and Direct
Self-Causation*, *Journal of the American Philosophical Association* 12(1)
(2026), §§3–5, explicitly defends a part/whole causal inference. If a link
causes each constituent event in a causal chain, it can cause the extended
chain-event. On his transitive or full-causal-ancestry reading, in any causal
loop, even one with an external cause, every link can cause every other link,
including itself indirectly. Newman argues that
the loop-event is therefore caused by its own parts and, because those parts
compose it, can count as directly self-caused. His domino-chain and
backward-influenced name-writing analogies supply a positive justification
for his proposed part/whole rule; this is not a mere assertion that causal
loops might somehow be exceptions. He distinguishes being causally affected
from having an *ultimate* explanation of the whole affair.

Crucially, §5 endorses as *plausible* a stronger existential-origin example
from Quentin Smith (1999: 581): at `t = 0`, a universe consists of `a,b,c`,
whose simultaneous states cause one another. Smith additionally supposes
that each constituent is caused **to begin to exist** by something within
the universe, then infers
that the universe begins to exist through its own constituents and thus is
self-caused. Newman recognizes why a beginningless infinite internal chain
would not support the same inference, and argues that the mutually causal
finite loop has a stronger claim: each member causes every member. His
footnote 1 explicitly allows recasting the discussion with *things* rather
than events as causal relata. This scenario targets existential origin,
not merely the occurrence of an event. It is a hypothetical metaphysical
model, not evidence of an actual self-creating universe. Primary text:
https://www.cambridge.org/core/journals/journal-of-the-american-philosophical-association/article/causal-loops-and-direct-selfcausation/5B4DE9F9DEA48B8B58D923665700EA14
This is primary-text research navigation, not a new pinned corpus claim or
an assertion that the whole event-level causal theory has been established.
The parity question these cases raise is mapped as PP-01 in
[`explorations/principle-parity-self-origination.toml`](../../explorations/principle-parity-self-origination.toml)
and [`docs/principle-parity-challenges.md`](../principle-parity-challenges.md#first-worked-test-universe-versus-omnipotent-being-pp-01).

**The precise scope of his challenge.** The Smith/Newman case is a genuine
proposed countermodel to a universal `¬ CausesOrigin b b`: if (i) beginning
of all mutually producing constituents suffices for productive beginning of
their composite `U`, (ii) the same `U` is both the originator and originated
whole, and (iii) this supplies `CausesOrigin U U`, then the bare prohibition
is false on that causal reading. Merely labelling the whole an *event* does
not defeat this proposal. The disputed inference and interfaces are:

1. **Composition and identity.** From every `a,b,c` being caused to begin
   existing by another member, what establishes that the *aggregate's own
   beginning* is productively caused by the **numerically identical**
   aggregate, rather than a collection of mutually caused first-stage
   states? Smith proposes a positive finite-loop answer, not an unspecified
   loophole. If `U` simply is the whole at `t=0`, the challenge is acute.
   If `U` is an enduring bearer or complete 4D history, an additional
   account must connect these first-stage productions to the existence of
   that **entire** bearer, not merely its initial state.
2. **Exercise and strict priority.** For the corpus proof the origin edge
   needs the self-edge bridge `OriginHasProductiveSelfExercise` (the
   universal `OriginHasProductiveExercise` only through it): an *occurring*
   exercise borne by `U`
   and producing `U`'s existence, rather than only exercises of proper parts.
   Mereological inheritance of those exercises by `U` is a substantive
   candidate bridge, not something to reject by definition. If such a
   whole-borne exercise exists, the proof still needs
   `BearerPrior` (bearer's existence prior to its exercise) and
   `ProductPrior` (exercise prior to product existence) under **one** strict
   order. Smith's simultaneous example specifically challenges whether
   both relations express strict existential priority in this setting.

This does **not** refute Smith/Newman merely by an event/bearer category
distinction. The task for its defender is to substantiate the proposed
whole-origin composition, bearer identity and producing relation. The task
for the no-self-origin defender is to establish the productive-exercise
bridge and strict existential/act priority *even if* the parts coexist and
mutually produce at the first moment; it cannot assume temporal precedence
or dismiss the cosmology for being cyclic. The Gott–Li baby-universe scenario
remains conditional, not an observed instance or a fully solved
self-generative history.

**A positive warrant to test against Smith.** The most promising defense is
the **actual-source principle**: for something to produce an existence,
there must be an *actual* bearer of the producing capacity while it is
exercised. A merely possible or not-yet-actual producer cannot exercise a
power; this is the force of Aristotle's actual builder/building distinction
above. The principle does not require an earlier clock time. If Smith's
`a,b,c` are alleged to cause one another's *very first existence*, rather
than only the first states of already existent causes, then each purported
productive exercise needs an actual source whose own being is supplied only
by another exercise in the very same inaugural loop. This supplies a
specific *ontological* question: how is any originating power actual in the
finite loop if no source's existence can be presupposed? The no-self-origin
defender may argue that actual productivity and an existence whose actuality
is produced by that same activity are incompatible; the rival may instead
defend simultaneous reciprocal actualization. The principle that a bearer
must be actual *while* it exercises its power gives only **co-actuality**, and
Smith's simultaneous loop grants co-actuality. *Strict* `BearerPrior` needs a
further clause: **the bearer's existence is not supplied by that same
exercise or by the loop that contains it.** That clause, not co-actuality,
does the work against Smith. It is close to the contested point itself, and
it stays **OPEN** against the rival of simultaneous reciprocal actualization.
The principle is therefore a substantive warrant for the co-actuality part of
`BearerPrior`. It is **not** a proof that Smith's posited causation is
impossible, and it does not establish the strict part without the extra
clause. The rival is a definite alternative that owes an account of actual
powers; it is not a vague exception. Furthermore the defender must
give a reason that `ProductPrior` is *strict explanatory* priority, not
just that the cause and effect share the label `prior`.

**A strictly weaker deductive route is available.** The existing two-token
proof uses irreflexivity and transitivity of mixed priority, but their only
joint use is to exclude the reciprocal pair
`Prior (inl (bearer a)) (inr a)` and
`Prior (inr a) (inl (bearer a))`. The single structural assumption
`∀ p q, Prior p q → ¬ Prior q p` (asymmetry) suffices directly with
`BearerPrior`, `ProductPrior`, and the self-edge bridge
`OriginHasProductiveSelfExercise` (unregistered
`SelfEdge.noSelfOriginFromAsymmetricSelf`; the older unregistered checks use
the universal `OriginHasProductiveExercise`).
Irreflexivity plus transitivity imply asymmetry, but not conversely: an
irreflexive directed three-cycle can be asymmetric while failing transitivity.
Thus no global transitivity or well-foundedness is needed for the **local**
productive self-origin contradiction. A CTC cycle among three *different
stage-events* does not automatically yield the prohibited reciprocal pair
between a bearer-existence token and its own productive exercise. The
Smith/Newman finite simultaneous-origin case is stronger: if its collective
production really is the whole's self-origin, either the strict priority
interfaces must be defended against that case or they cannot be used to
exclude it. Asymmetry itself remains OPEN in this interpreted domain;
calling the relation "priority" is not a proof of asymmetry.

The narrower route is **Lean-checked but not registered as a new corpus
result**. Unregistered theorems in
`TruthCore/Results/Causality/OriginExerciseBridge/Solution.lean` check three
things. `noSelfProductionOfAsymmetric` and `noSelfOriginFromAsymmetric` check
the route itself. `asymmetricOfIrreflexiveTransitive` checks that the old
bundle implies asymmetry. `threeCycle_asymmetric_not_transitive` checks that
the converse fails. Asymmetry remains an OPEN premise, and none of these
theorems has a corpus result or a Comparator certificate. A trial of the normal batch generator was rejected by
the existing `DISAMB-MIXED-EXISTENTIAL-PRIORITY` sense index: it treats the
`BearerPrior` and `ProductPrior` *properties of one supplied relation* as
distinct senses requiring a bridge. The disambiguation's own resolution
states that these are structural interfaces, not rival readings. Inventing
a philosophical cross-sense bridge just to bypass the check would misstate
the argument. The invalid generated batch was removed; the existing verified
route is unchanged. Revisit this registration when the sense taxonomy can
faithfully represent multiple laws of **one and the same** mixed relation.

**Updated provisional assessment.** The no-self-origin claim is more robust
than the original four-priority-premise presentation indicated: conditional
on positive existential production, it needs only the two activity interfaces
and absence of *mutual* existential/act priority. Newman's ordinary event
loops do not by themselves establish productive bearer-origin, but his
Smith-style simultaneous-universe example **expressly challenges that
boundary**. The decisive disagreement is whether collective reciprocal
origination gives `CausesOrigin U U` and, if so, whether the corpus's
exercise and strict-priority premises hold for it. Nothing here establishes
the relevant actual-world ontology, refutes a self-creating cosmology, or
establishes the still-open no-self-origin premise.

This is an **analyst conditional**, not a newly attributed quotation from
Aquinas and not a proof of the open P2/P3 bridges. The source-derived
`SecundaVia` exclusion of efficient self-causation remains separate; the
`EssenceEsseExternalCause` reading likewise keeps the external-cause
exhaustiveness burden visible. No root premise is marked closed.

## Premises, verification and service evidence

Intended and actual root-path open-premise delta: zero. The closed certificate
has no ordinary premises and no new root connection. All root philosophical
premises are retained; none is discharged.

The Challenge was frozen before proof work, SHA256
`80249ef71f3aa529bc97d4343b15e5af74788f8de1b0b631226a2b897a91325d`.
The shared persistent service accepted repeated full-content edits without
mutating its checkout/imports, at workspace
`/home/brantner/privat/truth-core-sprint-proof`, head
`75192b1c3efdf19f25601e52a06116e706420f11`, session `causal-harvest`,
path `Scratch/issue311.lean`. HTTP 200, final content SHA256
`d9a641f7007215a7884b0ec70d00651952546916e250d2df5e99cb870ae8c949`;
no errors and `#print axioms` reports no axioms. Initial implicit unfolding
failed; explicit unfolding and direct Boolean contradiction proofs fixed it.
Lease wait was 0.000010s, first request 0.836s, corrected warm request 0.230s.
Retain the warm serialized service for small edits; no second session or
benchmark rerun was needed. These are interactive diagnostics, not final
Comparator verification.

Canonical final CI owns build, binding, Comparator and NanoDa. After build,
reproduce the result gate with
`python3 scripts/worker_env.py -- scripts/verify-result.sh UNIQUE-FEEDBACK-CONTROL`.
The attempt record retains rejected interpretations and precise evidence.

## Explanatory-adequacy audit: what an endless series is asked to explain

The renewed Agrippa/Münchhausen question is about whether a regress supplies
what an inquiry requires, not whether an infinite set is contradictory. The
explanatory version in #311 has a specific primary-source argument. The pinned
Latta translation of *Monadology* §§31–45 was materialized and read in full
(`LEIBNIZ-MONADOLOGY-31-45`, text SHA256
`48c8019d588af3c5d262323ea365382be7021bf4f4ee23f7f0b68eb6650b6d04`).
This is an explanatory argument, not a historical attribution of Agrippa's
modes to Leibniz and not an inference from skeptical suspension to causal
impossibility.

### The source's demand and proposed answer

1. **Scope, §32:** a real/existing fact or true statement calls for a sufficient
   reason why it is so rather than otherwise. A reason may be unknown to us;
   lack of discovery is not absence of explanation. This is the stated PSR,
   not something the existing mathematical controls establish.
2. **Necessary truths, §§33–35:** their reasons are sought by analysis into
   simpler truths, terminating in primary identity principles whose opposites
   contradict. This is a proposed nonarbitrary analytical terminus, not a
   license to stop at any favored assertion. Its legitimacy still needs
   defense against rival epistemologies.
3. **The explanandum, §36:** contingent truths include the sequence or
   connection of created things. The example of the present act of writing
   allows infinitely detailed efficient and final causes. Thus the argument
   does not simply demand finitely many prior events or deny infinite detail.
4. **The insufficiency step, §37:** those further contingent details again
   require analysis for their reasons. Leibniz takes that renewal to leave
   the final question unsettled and concludes that the sufficient final
   reason lies outside the contingent series, however infinite it is.
5. **Proposed ground, §§38,45:** the conclusion is a necessary substance;
   §45 describes this proposed necessary being as having the reason for its
   existence in itself. This is not efficient self-production. Necessary-truth
   analysis in step 2, a de re modal existence predicate, and a sufficient
   intrinsic existence reason are not interchangeable.

These are sourced argument steps and open commitments, not a newly certified
inference application. The existing
`STMT-LEIBNIZ-SERIES-SUFFICIENT-REASON` already records the final
outside-the-series conclusion. The new readings expose what drives it rather
than registering the desired conclusion as another bridge assumption.

The distinctive criticism is **explanatory deferment**: an account of why
this contingent reason obtains merely introduces a further contingent reason
whose obtaining remains owed an account under the same norm. An endless
sequence of these local answers does not, *on Leibniz's stated view*, finish
the original why-question. Its length alone is not the defect; the alleged
unresolved explanatory dependence is. The burden is therefore to defend the
whole-sequence demand and why no admissible global or non-well-founded account
can satisfy it, rather than to point at infinity or assume that all adequate
explanation has a finite proof tree.

### What is already checked, and what remains a philosophical premise

| Existing certificate | What it settles | What it leaves open |
| --- | --- | --- |
| `TruthCore.Results.Causality.UniqueFeedback.controls` | Nonconstant global equations can have a unique consistent solution without observed boundary data. | Why these equations obtain; whether their structural fact is an intrinsic sufficient explanation. |
| `TruthCore.Results.Modal.HistoryContrastive.controls` | The same infinite memberwise causal/explanatory labels admit a necessary nondiscriminator or a contingent internal discriminator. | Whether discrimination is required or sufficient; whether the internal marker explains its own obtaining. |
| `TruthCore.Causality.BruteFoundationExplanations.necessaryReasonAndNecessitation` | A necessary reason plus explicit necessitation makes the specified individual's existence necessary. | Whether adequate explanation necessitates; why the full reason is necessary; independent sufficiency of a proposed necessary ground. |
| `TruthCore.Logic.Regress.Graph.grounded_eq_lfp` and `TruthCore.Results.Logic.RegressSchema.regressSchemaPackage` | Inductive finite grounding is the least fixed point, distinct from a source-free all-on successor assignment in the greatest fixed point. | Why actual power, epistemic warrant or complete explanation must meet that inductive norm. |

None needs to be reproved here. In particular, the Boolean uniqueness control
is not a counterexample to the *source's whole-series PSR*: it contains no
adequacy interpretation. Conversely it prevents dismissing a global-structure
reply merely because local copying equations can have multiple solutions.
The history discriminator is a separate minimal test, not the answer to the
stronger question of why its own contingent premises obtain.

### Strongest replacement accounts face the same question

These are explicit rival answer profiles, not new historical attributions or
certificates of metaphysical possibility.

| Account | Positive answer offered | Commitment it rejects or must defend |
| --- | --- | --- |
| Leibnizian final reason | The contingent order has a sufficient reason outside that order, in a proposed necessary being with an intrinsic reason. | Defend unrestricted/whole-series scope, the deferment-to-externality step, actual instantiation and intrinsic sufficiency. Necessity alone does not discharge these. |
| Memberwise sufficiency | An account of each member and its relations accounts for the series; there is no additional obtaining fact left over just by collecting the members. | Defend that sufficiency and the treatment of totality. The reply challenges the independent whole-series explanandum, not simply the existence of a first event. |
| Intrinsic global structure | The actual laws/whole constraints explain their jointly determined state, rather than one member originating it. | Explain or justify primitiveness of the constraints' obtaining, or defend an intrinsic account of that obtaining. A unique solution relative to supplied constraints establishes neither adequacy nor its absence. |
| Non-well-founded explanation | A whole pattern of explanatory dependence can be adequate without an inductive terminus. | Give a non-question-begging adequacy criterion and address vicious circularity/deferral. An infinite graph or local label assignment alone does not establish this reply. |
| Brute global fact | The complete obtaining contingent structure is a primitive fact, not an unexplained gap within a claimed total PSR account. | Reject or restrict the PSR openly. This leaves the why-question unanswered on the PSR standard; it does not become logically inconsistent merely for declining that demand. |

The first account is held to the same standard: calling a ground necessary,
self-existent or divine does not by itself show why its nature is instantiated
or why its intrinsic reason is sufficient. §45 proposes such an answer; it is
not established by the notation `NecessaryAt` or by the source's assertion.
Likewise, an epistemic foundationalist may defend noninferential warrant, an
infinitist available reasons, or a coherentist a holistic criterion. Their
justificatory standards must not be imported into ontic causation without an
independently defended cross-domain bridge.

### Exact open obligations and premise comparison

- **EXP-SCOPE:** defend why the contingent sequence's obtaining is a live
  explanandum beyond the supplied local facts, and which PSR applies to it.
- **EXP-LOCAL-TO-GLOBAL:** decide whether memberwise explanation, together with
  explicit totality/closure principles, answers that question. Neither a
  predecessor count nor a copied value is a sufficient argument.
- **EXP-NONCIRCULAR / EXP-ULTIMATE:** defend the exclusion of a global intrinsic
  or non-well-founded final reason rather than build externality into the word
  explanation. §37 takes the outside-the-series step; the rival can contest it.
- **Intrinsic adequacy and actuality:** establish the proposed necessary
  ground and its reason, without turning necessary status into an existence
  proof or an exception to the universal demand.
- **ACT-GROUND and temporal scope:** remain separate. Explanatory
  insufficiency does not itself show that a source-free causal system cannot
  act, and neither result would by itself forbid an unbounded temporal past.

Intended and actual root-path change: none. All 63 counted open premises and
the eight route costs are retained; no argument/result or root connection is
added. The five source readings are prose-only and do not certify the norms
they report. The dossier-linked attempt and the
`CONTINGENT-SERIES-EXPLANATION-ADEQUACY` candidate preserve the unresolved
burden. The next decisive task is an argument for or against that norm on a
shared global-structure case, rather than another solution-counting example.

## Positive infinitist account: common explanation and its exact limit

### Witness and reading boundary

The positive rival is now supported by an accessible primary argument:
Evan Welchance, *Metaphysical Infinitism and Theoretical Virtue*,
*Erkenntnis* (2026), DOI [10.1007/s10670-026-01084-1](https://doi.org/10.1007/s10670-026-01084-1).
`WELCHANCE-INFINITISM-1-3` pins the official CC BY 4.0 publisher PDF,
selected physical pp.1–18 (§§1–2.4 through p.18). The complete
21-page PDF was read for conclusion and context; the selected argument
range was materialized and read. The source's argument is defeasible philosophical
reasoning; no Lean theorem or new root commitment is advertised.

The Bohn candidate's title was inaccurate. Publisher metadata identifies
*Indefinitely Descending Ground*, pp.167–181, DOI
[10.1093/oso/9780198755630.003.0009](https://doi.org/10.1093/oso/9780198755630.003.0009).
PhilArchive identifies an author manuscript at `https://philarchive.org/archive/BOHIDG`,
but direct and versioned fetches returned HTTP 403. The author's University
of Agder page links the institutional record `https://hdl.handle.net/11250/4022949`,
whose NVA landing page was inaccessible to the browsing tool. These are
promising witness locators, not a reading. No Bohn view is attributed from
its abstract, another author's quotation, or a paywall. The source ID is
retained; the chapter remains unread and has no pinned passage here.

### The positive argument actually read

Welchance's §1.1 means facts obtaining in virtue of other facts, illustrated
by Socrates and his singleton. §§1.2–1.3 impose a shared question about
existence, including fundamentalia. A brute or unexplained foundation does
not lose every explanatory use; by parity, neither must an unexplained
chain. This defends local explanatory value without claiming to explain
the whole chain. §2.1 grants foundationalism's virtue of a relatively small
common explanatory base. §§2.2–2.3 offer a rival virtue: one underlying
explanatory theory applies throughout concrete existence. The motivation is
a defeasible preference for explaining instances of one phenomenon alike,
illustrated through vagueness. §2.4 considers uniform identity-based and
different-kinds-of-existence replies, arguing that each has costs. The
conclusion is parity on these considerations, expressly not infinitism's
truth or overall superiority. §1.3 n.15 mentions explaining explanatory
links through further prior facts but leaves that strategy undeveloped.

### Five-question audit and independent appraisal

The following is repository analysis of that proposal, not an attribution of
additional theses to Welchance.

1. **Ordinary meaning.** An in-virtue-of answer specifies what makes a fact
   obtain, rather than who first produced a thing or what a person must know.
   That is a plausible target of ontological explanation, but it covers more
   than efficient causation. Its relata here are obtaining facts, including
   basic existence facts about particular objects. An interpretation in terms
   of beings themselves needs a defended translation, not a silent change of
   the variable type.
2. **Examples and granularity.** Socrates's existence and his singleton make
   the proposed direction intelligible; they do not establish an actual
   endless concrete chain. Wood/atom/chair examples suggest constitution,
   but the existence of atoms alone plainly omits arrangement and relevant
   composition conditions. The source's §2.4 explicitly distinguishes an
   existential claim from basic existence claims and instance facts. An
   adequate reconstruction therefore preserves plural/full explanatory
   grounds. A binary edge from one contributing fact need not itself be a
   sufficient explanation. One must not replace joint sufficiency with the
   assertion that every fact has one predecessor.
3. **Exclusions.** Temporal ancestry, persistence after production, efficient
   action, logical entailment, covariance, beliefs supported by further
   beliefs, and a consistent graph are not automatically instances of the
   proposed relation. Ordinary constitution cases do not identify it with
   direct present-esse conservation `R`. No epistemic infinitism is doing
   ontological work here.
4. **Why structural properties?** Constitutive priority and the singleton
   example motivate direction in those cases. They do not by themselves
   establish universal asymmetry, transitivity, or well-foundedness. The
   positive infinitist motivation is continuity of explanatory practice:
   changing level need not change what it is to explain an existence fact.
   If that motivation is sound, indefinitely many adequate local explanations
   need no special originating explanation merely to count as local answers.
   This is a reason to resist an automatic termination requirement, not a
   demonstration that every local chain is adequate. The foundationalist can
   answer that a genuine distinction between derivative and intrinsic
   existence justifies differing explanations. That reply must defend the
   distinction and the intrinsic answer; the infinitist must defend treating
   the relevant existence facts as one explanatory kind. Neither side earns
   its preferred relation property through notation.
5. **Abstraction.** A formal comparison would need explicit existence facts,
   plural full grounds and any conditions under which explaining members
   explains a totality. It must distinguish immediate explanation from its
   ancestral closure, and fact grounding from efficient conservation. No
   finite inductive generator is proposed as the definition of actual
   explanation. The already certified PLG non-well-foundedness example
   settles a logical-rule boundary only; its uninterpreted atoms do not
   supply this missing interpretation.

### Strongest objection and the consequential fork

The ground-floor objection deserves its strongest form: each local explanation
may depend on obtaining facts whose explanatory efficacy is itself borrowed.
If every explanation merely passes on that same unpaid obligation, why does
the chain explain any actual existence rather than characterize a possible
pattern of dependence? Supplying infinitely many labels, or unique solutions
to given constraints, would not answer that objection.

The rival's positive answer has two parts. Local explanation may be
constitutive determination rather than transmission of an explanatory
quantity that must first be deposited somewhere. Uniformity then supports
continuing the same explanatory practice without a privileged level.
Furthermore, an unexplained explanation-base is not generally inert: a
foundationalist who permits a brute basic entity to explain derivatives
must give a relevant reason why a brute globally structured chain cannot
explain its members. These are substantial reasons, conditional on genuine
local sufficiency and the proposed symmetry of explanatory burdens. They
are not merely an assertion that infinity is consistent.

The strongest foundationalist response rejects that symmetry: the required
intrinsic sufficient reason is independently defended, whereas the chain's
whole obtaining remains unanswered. A demonstrated intrinsic answer would
therefore defeat this parity argument; simply naming a necessary object
would not. Conversely, even a successful parity argument would show that
neither *bare* foundation nor *bare* chain finishes the total inquiry. Equal
unanswered questions do not become answered questions.

This gives a discriminating fork rather than a new mathematical fixture:

- With a memberwise explanatory aim, genuine full local grounds plus the
  uniformity reason provide a positive infinitist account. Its actuality,
  local adequacy and relation interpretation remain to be defended.
- With a whole-series/existence PSR, the present infinitist proposal leaves
  the totality question open or admits a brute totality. It does not discharge
  `EXP-SCOPE`, `EXP-LOCAL-TO-GLOBAL`, `EXP-NONCIRCULAR` or `EXP-ULTIMATE`.
  Extending upward explanation of grounding links is a further proposal,
  not an already supplied totality explanation.
- With direct existential conservation as the target, neither memberwise
  fact explanation nor explanatory uniformity establishes an `R` instance,
  an independent sustainer, or its absence. The relation bridge remains OPEN;
  see the five-question audit in `docs/power-existence-scope-boundary.md`.

The positive account therefore challenges the claim that foundationalism
wins merely by possessing a base, and supplies a concrete reason for
preferring explanatory continuity. It does not refute independently
supported causal-finitism/patchwork premises; their joint-realizability
argument must be assessed on its own relation and background assumptions
(`docs/notes/causal-finitism-367.md`). Nor does it show that all-branch
well-foundedness is the weakest needed condition: an adequate intrinsic
full explanation could matter more than the shape of every ancillary
partial-ground path. No implication between those requirements is added.

Intended and actual root-premise delta: zero. No premise is added, removed
or discharged, and no graph/result/type changes. Rejected interpretations:
Bohn's abstract as a read chapter; uniform explanation as total PSR success;
parity as proof of actual infinitism; a binary partial edge as a full ground;
fact explanation as efficient present-esse support. The next decisive
comparison is an independently defended intrinsic existence explanation
against this explicit uniformity/parity case, holding the explanandum fixed.
The companion intrinsic-nature analysis in `docs/psr-scope-countermodels.md`
now assesses that positive reply and its individual-actuality burden; it
does not declare the intrinsic account or this rival discharged.

### Finite access, the reason for the order, and comparative economy

The owner's further objections sharpen three separate demands. These are
argument candidates and appraisal, not new source attributions or established
premises. The existing [epistemic infinitism analysis](infinitist-justification-adequacy.md),
especially its Klein–Turri §§4a–b reading, already distinguishes available
reasons from an actually completed infinite performance. That reply is reused,
not counted as a new finding.

**Can a finite thinker ever progress?** If justification of the first claim
requires first completing verification of every later reason, an endless
chain cannot meet that condition through successive finite inquiry. That is
a strong objection to that particular completion requirement. The infinitist
must defend a different adequate epistemic status: finite inquiry can answer
particular challenges or improve support without finishing the whole chain.
Calling those steps progress still requires a truth-conducive reasonhood norm,
not mere accumulation of further assertions. A finite schema can make further
steps intelligible, but neither a schema nor arbitrarily many individually
possible responses establishes one actually suitable available chain.

Ontic determination is a different target. The facts that constitute a chair
are not required to await a thinker's inspection in order to obtain. Finite
cognitive limitations therefore do not by themselves exclude infinite ontic
dependence. Conversely, calling dependence ontic does not entitle a finite
thinker to claim knowledge that it adequately explains the chair. The rival
owes accessible warrant for the proposed dependence account and its scope,
while a totality explanation remains owed if that is the common demand.
There is no inference from human inability to traverse a chain to the chain's
nonexistence, or from the chain's obtaining to human access to its explanation.

**Any rule can be questioned; why this order?** A request for justification
is not itself a refutation. If every answer were rejected solely because a
further question is grammatically possible, the same veto would apply to a
finite foundation and to the vetoing rule. The substantive challenge is whether
the rule and its application are independently warranted or merely borrow
all their force from the very order they purport to vindicate. A general
rule must discriminate correct from incorrect applications; repeating it
at another level does not supply that discrimination. This burden applies
also to an asserted noninferential warrant or intrinsic existence reason.

For ontic explanation, an order is not merely the order of enumeration,
a causal chronology, or an arbitrary chosen relation. Even necessary
co-obtaining or mutual entailment does not select a direction of explanation.
The account must say which facts make which others obtain, why those full
grounds are sufficient, and why reversal changes the relevant constitutive
or essential dependence. If a contribution is only a partial ground, the
rest of the joint ground and its arrangement cannot be hidden inside a
binary arrow. The source's §1.3 n.15 proposes further explanation of the
explanatory links but does not develop a vindication of this whole order.
So the new open demand is precise: defend the obtaining and direction of
these constitutive links and their governing rule, not just explain each
member given that rule. Merely redescribing an unexplained order with a
short recursive clause would relocate this demand.

A constitutive or essence-based reason for the direction could answer a
local order question without tracing an infinite history. That is a possible
shape of answer, not an independently established reason in this batch.
For present-esse support, it would additionally need the conservation
interpretation defended above; a fact-grounding answer cannot substitute
for it. For epistemic rules, the corresponding obligation concerns warrant
and truth-conduciveness, not ontic constitution. The two demands must not
be merged because both use the word “because.”

**Is an infinite regress infinitely less economical?** The strongest
parsimony argument is conditional: for the *same* explanandum and adequacy
standard, if a finite account explains at least as much with fewer gratuitous
independent commitments, prefer it other things equal. A regress that adds
independent unexplained entities or merely relocates an unexplained ordering
rule has a real cost. Infinitism does not answer that criticism by announcing
that all its members depend on something else.

The comparison nevertheless needs an explicit inventory. Number of entities,
number of kinds or laws, number of independently unexplained commitments,
and length of a generating specification measure different things. A finite
base may explain infinitely many dependent entities; a uniform infinite
chain need not introduce an independent assumption for every member.
Equally, a short specification may describe infinitely many things without
explaining why any of them or that ordering rule obtains. Compression alone
establishes neither explanatory adequacy nor an infinitist advantage.

Welchance's already-read §2 comparison concerns precisely competing kinds
of unity: a relatively small common base and a common explanatory theory.
Our appraisal does not convert their alleged parity into a general result
about economy. A finite proposal must supply its base, the relevant
production/constitution principles and the reason they obtain; an infinite
proposal must supply its local full grounds, their direction/order and the
status of the totality. Count any independent brute commitments on both
sides, retain differences in what each explains, and only then apply the
conditional preference. Neither “infinitely many members” nor “one source”
alone settles that comparison.

The material delta is thus a sharper open ordering/rule obligation and an
explicit conditional parsimony test. The finite-mind availability answer
was already covered in #669; it is not repackaged as new support. No new
independent defense of infinitism, causal conservation or an intrinsic
foundation is supplied here. Root-premise change remains zero.

### Witness extraction repair

The initial full pp.1–21 selection passed locally but failed CI40782499547
on its extracted-text hash, with the full-PDF bytes unchanged
(`1f98353914c8e4650660d0bdd84549912ed4b0ec76a318877be72dbd7f6c8f9f`).
A bounded comparison used local Poppler26.01.0 and Ubuntu:noble
Poppler24.02.0, matching CI's extraction. The sole normalized difference
was the arrangement of zero-width characters in the CC-license URL on
physical p.19; no philosophical text differed. Restricting the materialized
selection to pp.1–18 avoids that extractor-sensitive footer while retaining
the positive and critical arguments at issue. The full-PDF raw hash remains
pinned, and its conclusion, license and references remain consulted context,
not an additional selected passage. The historical passage ID is retained.
No extraction normalization, integrity gate or repository dependency changed.
The publisher HTML was considered but rejected because repeated fetches
changed raw bytes; it was not substituted as a stable witness.

### Independent registration of the existential-production proof

`NO-EXISTENTIAL-SELF-ACTUALIZATION` now has its own argument/result, rather
than being described only beside the older causal-loop theorem. Its four
named premises are `STMT-EXISTENTIAL-BEARER-PRIOR`,
`STMT-EXISTENTIAL-PRODUCT-PRIOR`,
`STMT-MIXED-EXISTENTIAL-PRIORITY-IRREFLEXIVE`, and
`STMT-MIXED-EXISTENTIAL-PRIORITY-TRANSITIVE`; the conclusion is
`STMT-NO-EXISTENTIAL-SELF-PRODUCTION`.
`EXISTENTIAL-SELF-ACTUALIZATION-CONTROLS` separately registers the existing
omission edges and positive productive interpretation. No model is copied.

The named interfaces in `Causality.ExistentialSelfActualization` are only
aliases of the branch's existing formulas, for exact type/premise binding.
They introduce no new priority relation or Profile. The registered Solution
imports `PerSeCausalLoopImpossible.noExistentialSelfActualization` and its
existing controls. The original Challenge, its type and proofs are unchanged;
a separate Challenge freezes the named registration.

The new premises are explicitly unattributed. The fact that the original
irreflexivity/transitivity templates are also used in Aquinas readings does
not defend their extension from beings to the mixed `Sum Being Exercise`
domain. `DISAMB-MIXED-EXISTENTIAL-PRIORITY` records this reading boundary.
Both structural laws and both productive interfaces require independent
justification for the proposed act; applying transitivity across unlike kinds
of explanation is itself part of that open burden.

The left tokens merely **label** bearer/product existence. There is no
`ExistsAt` or truth predicate in this signature, and the theorem does not
prove that a label denotes an actual existing bearer. Similarly `produces`
is a supplied relation whose productive interpretation remains open. An
ordinary embodied action motivates a bearer/act distinction but does not
establish creation of bare existence. No undisputed empirical instance of
that stronger existential production is supplied here. Intrinsic noncausal
explanation and consistent feedback remain serious alternatives to that
interpretation, not contradictory merely because they reject a productive
interface. Root-path premises remain unchanged.

The same branch also registers `AQUINAS-NO-SELF-MOTION-SAME-RESPECT` and
`AQUINAS-MOVED-BY-ANOTHER` and imports them into both First Way Solutions.
That source-preserving motion argument and this mixed-priority argument are
distinct routes. Neither supplies the other one's existential application
premise; see `docs/power-existence-scope-boundary.md` for the exact no-self-motion
scope and the qualified specialization to an esse respect.

Focused build, exact corpus binding, Comparator and NanoDa passed for both
registered results and the expanded original causal-loop result, with zero
permitted axioms. Named-interface Challenge SHA256: `da713a6343a7cfdf02ac4b81556794a32e268694758634ea4e622d46c4c2cde4`.
Root route costs and open-premise membership remain unchanged: 11 routes,
62 open premises. Full-library integration and reverse-dependency checks remain
delivered-head CI obligations.


### First-principle entitlement audit: existential availability (2026-10-31)

This bounded follow-up retains the owner's actual population and working PSR.
It asks what independently licenses existential production, rather than reopening
bare coherent regress tables as adequate rivals. Reuse inspection covered the
actual borrowing-cut, contingent-dependence and borrowed-exercise dossiers and
the existing cumulative supply and #780 attempts. No new model is needed.

**Narrow positive argument.** An actual exercise cannot be the whole productive
source of the very existential availability required for that same exercise.
Here “required” concerns the actuality of this exercise in this respect, not a
temporally earlier instant or a merely possible power. In a bearer-based account,
there must be an actual bearer to exercise a power. If producing that bearer's
existence is what allegedly supplies this requisite actuality, production must
already be exercisable to supply what makes it exercisable. The proposed act
therefore cannot fill that role by itself. This is a constitutive-priority
argument, for which demanding a temporally earlier production would be a mistake.
The existing mixed-priority theorem captures its conditional structure; no new
formal proof or self-evident corpus marking is supplied by this appraisal.

This gives a substantive reason for the bearer-presupposition interface, once
“an exercise of this bearer” has been established. Its limit matters: an
unowned episode has not thereby acquired a substantial bearer, and a causal
process that maintains a living system presupposes current constituents rather
than producing their bare existence. A source's existence need not be caused by
its activity; intrinsic explanation is not efficient self-production. Transitivity
across bearer-to-act and act-to-product priority still requires one coherent
sense of existential productive priority. Treating any counterfactual necessary
condition as that priority would illegitimately include reciprocal conditions.

**Materialized sources and context.** Re-materialized and read the complete
existing passages `ARIST-MET-IV-4`, `ARIST-MET-II-2`, and
`AQUINAS-ST-I-Q104-A1-EN` using `scripts/source_evidence.py materialize`.
The first two are the pinned Greek witnesses; the third is the recorded
Dominican translation. These are source readings and analyst appraisal,
not newly attributed claims.

Aristotle, *Metaphysics* IV.4, 1006a11–28, supplies a positive model of elenctic
entitlement: the disputant's determinate signification supplies the concession,
rather than a demonstration from a supposedly prior demonstration of everything.
This supports rejecting the demand that every first principle have a prior
proof. It does not turn the existence of a meaningful denial into a concession
of all-subsets existential foundation. A denial of its own meaningfulness, as
meaningful communication, undermines that performance; denying the borrowing
cut does not deny determinate signification. The extra claim that every meaningful
performance has source-complete existential Supply would already carry the
foundation application under investigation. A new performance-to-Supply alias
would relocate this claim, not vindicate it.

Aristotle, *Metaphysics* II.2, 994a1–19, argues from the causal role of the first
in a first/middle/last ordering to the insufficiency of endlessly intermediate
causes. The parenthetical extension from one middle to many, finite or infinite,
is precisely the consequential move. Its strongest productive reading is that
an intermediary's causal contribution is wholly derivative in the relevant
respect: multiplying intermediaries never supplies the primary contribution.
It is not merely the claim that an infinite chain is psychologically impossible
to inspect. But the source's three-position illustration does not independently
prove that every member of a beginningless existential structure has that
wholly derivative role. Calling all of them “middle” in the source's strong
sense already commits to what their actuality fails to supply. The later
knowledge/infinite-traversal discussion is not substituted for ontic production.

Aquinas, *ST* I q.104 a.1, corpus and ad 4, gives a useful positive discriminator:
a cause of becoming may cease while the product remains, whereas dependence
on a cause of being lasts with the relevant action. The house/building and
heated-water examples prevent equating every historical producer with a present
existential supplier. Direct conservation is distinguished from removing a
corrupting factor. Reply 4 explicitly describes continued giving of esse without
motion or time, so a temporal initial event is not the intended necessity.
However, the universal application compares creatures with illuminated air only
after invoking God as essence-identical existence and creatures as participated
being. Those are substantive prior metaphysical commitments, not consequences
of the lamp/air analogy. This source cannot independently supply the borrowing
cut here by presupposing its intended divine terminus. The existing claims
`AQUINAS-ST-I-Q104-A1-BECOMING-BEING-CAUSE` and
`AQUINAS-ST-I-Q104-A1-CONSERVATION-CONTINUES-ESSE` preserve the relevant readings.

**Exact remaining proposition.** For every nonempty collection S of actual
concreta under this selected existential-production relation, if S contains no
underived contribution, some actual member must receive a sufficient productive
contribution whose whole contributing basis is outside S. This is the existing
`STMT-ACTUAL-CONCRETE-BORROWING-ESCAPE`, with the recorded graph's sourcehood
reading, not a newly weaker principle. The all-immediate-ground recording also
means that applying it requires identifying complete productive contributors,
not merely identifying one helpful cause or an enabling condition.

The strongest collective argument is that a collection whose members contribute
only existential actuality borrowed within that collection cannot supply the
actuality those borrowings all require. Its independent burden is collective
non-generation: why no arrangement of exclusively derivative contributions can
possess existential productive actuality that none supplies independently. The
single-act argument establishes no such extension merely by plurality or
transitivity. Nor does working PSR alone select the externality and strict
priority of the proposed adequate reason. This identifies what must be defended;
it does not concede that a bare infinite diagram answers the demand.

**Generation audit and next discriminator.** Defining actual production to be
inductively generated Supply would secure the conclusion by the chosen standard.
That is not independent entitlement. The existing borrowing-cut/WF equivalence
shows the cut has full well-foundedness strength on the selected actual graph;
it is not a weak local no-self-production axiom. Conversely the present narrow
availability argument assumes neither a finite population nor finite branching,
and says nothing by itself about an infinite strictly prior order. The decisive
source/semantic task is to defend collective non-generation for bare existential
actuality, allowing joint contributors and distinguishing intrinsic sufficient
reason from efficient self-production. A source that merely repeats “no first,
no middle” or labels every relation derivative is insufficient without that
interpretation defended. No new theorem, source claim or root premise is
introduced, removed or discharged. Intended and actual root-premise delta: zero.
Shared convention sourceRevision: `c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.

### Actual existential foundation: collective non-generation audit (2026-11-11)

**Independent semantic challenge: qualified acceptance of the complete outcome
and synthesis at `486b956a909765605cec6fa321c435859400a88f`; no substantive
repair requested.**
Evidence baseline: `6d9b380099158c877373eaf34e2c6a9e4e6d01e4`, fetched from
normal `origin/main`. The seeded Lean preview revision is not this research
baseline. The question is independent warrant for actual existential foundation,
not another equivalent rank or cut formula. Its root connection is premise
`82cfaf26-fc86-54ab-8328-9a7b2bdbbe21` (`ActualGroundingWF`) of argument
`df542c04-6033-5d7d-b681-b81263dc1245`'s necessary-concrete-underived route.
Resolve that argument's full identity by its stable legacy name
`NECESSARY-CONCRETE-UNDERIVED-COMPOSITION`; the dossier/context are navigation,
not verification. The selected relation is the SAME actual-concrete existential
support of `NecessaryRootFork`, not signal copying, historical generation,
ordinary conservation of energy, or fact-level sufficient reason.

The strongest positive argument says that existential actuality wholly
received from other members cannot be collectively made available by a roster
whose complete productive contributions are all received within that roster.
Its strongest relevant rival proposes genuinely obtaining, directed, full
existential dependence at every stage, with no initial supplier: either a
beginningless productive structure or a constitutively explanatory organization.
Neither a bare Nat diagram nor calling an organization a law supplies that
interpretation. The question is whether the positive argument independently
excludes this stronger interpretation, holding the explanandum fixed.

#### Existing evidence and exact strength

Reuse inspection included the current root context, `related` and dossier for
actual grounding WF, the borrowing-cut dossier, the joint-power argument
context, and #311/#613/#545/#487 notes and attempts. Exact controls consumed:

- `EssentialPowerUnderdetermined.essentialPowerUnderdetermined`: all-on/off
  successor transmission and edge-cut dependence; no actual productive
  interpretation is certified.
- `LocalObservationSelectsSolution.localObservationSelectsSolution`: a datum
  selects the chain's activity. It supplies determination conditional on a datum,
  not a reason for the datum.
- `UniqueFeedback.controls`: unique sensitive Boolean feedback without an
  observed datum. Its negation/conjunction constraints are not pure existential
  transfer, and have no explanation/production predicate.
- `DerivativeJointPower.certificate`: all-contributor Supply, its trap
  obstruction, powered-group/Escape comparison, and the exact source-anchored
  infinite branch. A graph-source path is insufficient for the selected
  all-contributor standard; that standard's actual applicability is open.
- `TruthCore.Causality.NecessaryRootFork.chainHornModel` and
  `TruthCore.Results.Causality.BearerRegress.chainBranch`:
  actual endpoint assignments and acyclic endless support under the respective
  explicit profiles. These are structural interpretations, not metaphysical
  existence proofs.
- `PerSeCausalLoopImpossible.noExistentialSelfActualization`, its two omission
  controls and `otherBearerCanActualizeExistence`: the bearer/act/product
  interfaces with a strict transitive mixed priority prohibit production of
  the act's own bearer, and allow another bearer to be the product.
- `ConcreteExistentialSupply.supplyRootEquivalence` and
  `borrowingEscapeWFEquivalence`; `WholeRosterFoundation.actualRootExists`
  together with the existing registered whole-roster/root equivalence.
  On their exact profiles, source-backed existential Supply already has root
  existence strength; the all-subsets cut has WF strength under explicit EM;
  the inhabited whole-roster restriction has actual-root-existence strength.
  These are not three independent warrant sources.

Unqualified theorem names in this list abbreviate their existing
`TruthCore.Results.Causality` namespaces except the self-actualization results,
which are in `TruthCore.Results.Alternatives`. No theorem, Challenge or
verification record is changed. The computed cut dossier explicitly reports
`proved; established: false`. A proved producer from an open application
principle does not establish actual existential foundation.

Current-main #1378 also advances beyond a scalar analogy: see
[contractive borrowed power](contractive-borrowed-power-1378.md), continuation,
and `TruthCore.Results.Causality.QuantitativeTransferPaths`. A bounded network
with uniformly subunit total transfer gives a finite positive-input path;
vanishing cumulative products suffice on a chain. Whole-network conservative
and nonuniform positive assignments remain controls. These conditional results
do not supply a universal measure, loss law or existential interpretation.
They are reused, not replaced with another quantitative campaign.

#### Walk the positive argument: what is independently motivated?

**1. An exercise requires something actual to exercise.** For an exercise
attributed to a bearer, the bearer cannot obtain its entire existential
availability from that very exercise. Otherwise the exercise would have to
supply what makes it exercisable. This remains the strongest local availability
argument in the preceding audit. It motivates bearer-presupposition once an
act really is an act of that bearer. It does not justify assigning a substance
to an unowned episode or treating reciprocal necessary conditions as strict
explanatory priority.

**2. An actual supplier need not be an independently actual supplier.**
The positive argument must not slide between “there is no actual giver” and
“there is no giver actual independently of every other giver.” The serious
beginningless rival affirms actual givers and recipients throughout. Thus it
accepts that nonexistents cannot act and that unrealized potency cannot act by
itself. Its denial is that every actual giver must ultimately have an
independent giver. Calling the former commitments violations of actuality
would already import the latter. The same distinction applies to “has nothing
of its own”: lacking intrinsic actuality does not mean lacking actual received
actuality at the selected world.

**3. Counterfactual loss does not settle the intact case.** The explicit cut
controls grant that deleting a supplier can extinguish downstream exercise.
They thereby capture a real constraint the positive argument should preserve.
But the intact rival posits no such deletion: its prerequisites all obtain.
Conditionality of each member's actuality does not entail that some condition
is unfulfilled. Requiring all prerequisites to have *already been settled
without dependence* is a further foundation norm, not merely the requirement
that they be actual. This is an ontic distinction; finite agents' inability to
traverse the chain does not decide it.

**4. Strict priority excludes return, not endless priority.** The mixed
bearer/act/product proof supports the no-return argument under its interfaces.
Nothing in strict transitivity makes a beginningless strict order inconsistent.
A beginningless productive rival can put each supplier's existence prior to
its exercise, and that exercise prior to the distinct recipient's existence,
while every supplier is itself supplied farther upstream. This is an unrefuted
interpretive proposal, not a newly certified mixed-domain model. Existing
endless-order controls establish the structural boundary; they do not certify
the proposed meaning of each productive edge. Adding that such priority is
always accessible would supply precisely the stronger disputed premise.

**5. Why should collecting derivative contributions not generate actuality?**
For transfers of a measured quantity, noncreation can follow from an independent
accounting law. But “each member has no independent source” is not “each actual
member contributes quantity zero.” The former permits positive received
contributions; the latter would exclude them in advance. The #1378 conservation
and loss controls show why purity or absence of double counting is insufficient
for extinction without further premises. Bare existence is not presently
identified with an additive productive magnitude. There is no independently
warranted universal dissipation law here from which the metaphysical collective
claim follows.

The strongest *nonquantitative* reason is that an instrument's entire efficacy
is another's efficacy exercised through it. Adding instruments changes routes,
not the kind of contribution demanded. This gives a defeasible motivation for
seeking an independent contributor; it is more than an objection to cardinal
infinity. Its unresolved step is whether a complete source-free organization
can itself constitute the actuality of the contributions, rather than merely
route a contribution whose independent actuality is presupposed. Ordinary
instruments illustrate routing, but do not establish that every candidate
existential support has that structure. Defining “instrument” as already
having a principal supplier would settle a classified instrument case while
leaving universal existential classification open.

**6. The collection cannot be treated as one self-producing bearer for free.**
A plausible attempted extension says that, because the roster's exercises
produce all its members, the roster produces its own existence, contradicting
the local proof. To instantiate that proof requires an actual single bearer,
an act of that bearer, and that act's production of its own bearer. A plurality
of distinct acts on a beginningless order supplies none of these identifications
by collection alone. If a proposed whole really satisfies those interfaces,
the local exclusion applies. Otherwise the extension needs an independently
defended plurality/whole-to-act bridge. This attempt therefore neither refutes
the strongest distributed rival nor licenses a new self-production theorem.

#### Selected source test: SCG I.13 and the reception ambiguity

To test the strongest positive source argument rather than merely list the
open cut, re-materialized and read **all of SCG I.13 [1]–[35]** in the existing
Pegis translation witness `AQUINAS-SCG-I-13-EN`, passage
`92bd0343-4334-512b-98cd-74b784fd566c`. Materialization succeeded against the
existing pins; the manifest records normalized text SHA256
`aecaef150587d0823de8273bdb8f1284c55c3b73a16571f527eac61f8047d619`.
No Latin comparison, new passage, or new attributed corpus claim is asserted.
The following distinguishes source reasoning from this worker's appraisal.

The source separates several arguments. [12]–[13] appeal to bodies,
contiguity and moving an infinite body in finite time; [14] and [33] use the
first/intermediate-cause argument; [15] uses instruments and principal action.
The last two provide the direct collective argument considered here. [17]–[19]
are a distinct second way, and should not be silently imported as a proof of
[14]–[15]'s inference. [29]–[30] explicitly discuss the eternity of the world;
the case should not be represented as requiring a first temporal event.

In [7], the dependence conditional can be accepted even with an impossible
antecedent. Therefore the source is not answered by demanding a physically
performable removal of a first mover. The live issue is the scope of that
dependence: that removing an actual first supplier removes its derivatives
does not itself show that every possible derivative organization has such
a first supplier. [15] supplies an additional substantive instrument/principal
claim, which the existing #741 capacity/exercise controls already isolate.
The source therefore presents more than a bare finite illustration, but the
universal classification and collective availability remain its contested work.

The further [19] argument is particularly useful as an **over-exclusion test**.
For the same learning/teaching episode and knowledge, being taught there
requires the absence of knowledge that teaching there requires. Across a
finite range of motion kinds the source also considers repeated kinds.
Its act/potency contradiction must retain the same subject and relevant
respect; repetition of a label at different subjects is not by itself that
contradiction. This paragraph does not certify or reject the source's entire
second way.

For existential conservation, the crucial application distinction is between
**receiving an actuality one presently lacks** and **depending for an actuality
one presently has**. A conserved bearer can have actuality while receiving
its continued support. Treating any existential receiving as present absence
of the very actuality needed to act would prohibit even an instrument in a
finite founded series from acting while dependent. It would therefore defeat
the positive founded case as well as the infinite rival. The earlier q.104
continued-esse reading supplies the source-side reason to preserve this
contrast; its universal divine application still has the open burdens audited
above. This is an analyst constraint on the proposed transfer, not a claim
that SCG [19] itself teaches existential conservation or that all its motions
are receiving esse.

The constructive improvement is thus a sharper sufficient challenge: an
anti-borrowing defense must reject **endless actual reception** without treating
all actual reception as unrealized potency. The narrow no-self-production
argument meets that constraint but does not settle endless reception. The
collective routing/principal argument attempts to meet it, at the exact cost
of its independently disputed non-generation application. A new theorem
repeating strict priority or the cut would not decide this contrast.

#### Walk the strongest replacement: what would make its support real?

**Constitutive infinitism.** The best positive replacement does not claim that
an effect efficiently creates itself. It says that the existence of each
organized concretum is fully constituted by actual constituents in the relevant
arrangement, with the same explanatory kind continuing without a minimal level.
Essences/constitution would give the direction and relevance of support; mere
co-obtaining or a relabelled arrow would not. Ordinary constitution motivates
asking this question, but does not establish endless constitution or that all
arrangement conditions have themselves been explained. The full ground must
include those conditions. A singleton membership or one helpful constituent
is insufficient.

Descend one level: if the arrangement is fixed by an obtaining law, is that
law only a condition on possible realizations, or does its nature explain an
actual realization? In the first case the existence of the configured domain
remains owed an answer under a global actuality demand. In the second case
the rival owes a positive account of that explanatory nature and its
instantiation; “the structure exists” alone restates the target. If arrangement
facts depend on further facts of the same kind, explaining them remains useful
local progress but does not automatically settle the unrestricted demand.
This revisits the ordering/rule burden above, without substituting another
uninterpreted adequacy flag.

**Beginningless productive support.** This stronger causal proposal affirms
actual bearers, occurring exercises and genuinely existential products, not
just constitutive explanation. Its price is allowing productive actuality to
be wholly derivative at every stage without a first contributor. It must
defend both the existence-to-exercise and exercise-to-existence interfaces on
one non-temporal relation; ordinary energy transfer or persistence of an
already existing bearer is insufficient. No independently verified real
example of this entire infinite existential arrangement is supplied. But the
foundation advocate cannot reject its actual suppliers merely by calling
them nonexistent in isolation. The live conflict concerns collective sufficiency,
not the local prohibition on action by a nonexistent bearer.

**Global explanation has two materially different applications.** If an
irreducibly actual whole is itself an independent concrete existential
supporter of the members, then it is a candidate foundation relative to that
roster, even if its internal dependency pattern is infinite. It need not be
a necessary being, unique or God, and its independence and concrete
supporterhood still need warrant. This version is not automatically a
counterexample to the demand for an underived source. If the “whole” is instead
only the organization of the same exhaustively derivative members, no new
independent bearer follows: its global obtaining must be explained, intrinsically
vindicated, or accepted as brute under the selected explanatory aim. Conversely,
a global explaining fact is not a concrete supporter merely because it is
called the source. This is an application test, not an exhaustive ontological
classification or a newly proved fact-to-being bridge.

**Determination and realization remain distinct.** Unique feedback defeats a
universal claim that loops cannot determine a state. For pure transfer,
zero-preservation retains an inactive fixed point; uniqueness across the full
assignment space would then exclude a positive fixed point. A rival can instead
restrict to populated/actual assignments, or give a nonzero boundary datum.
Such a restriction need not be a dishonest trick: the investigation already
has independent evidence that something is actual. It supplies no explanation
of why those conditions obtain, however. Nor does zero-preservation have an
automatic interpretation when the node domain itself consists only of actual
existents: the empty assignment changes the represented interpretation and is
not thereby an admitted metaphysical world. No mathematical fixed-point
comparison here decides that admissibility or the ultimate reality of support.

#### Provisional judgment, shared dependencies and revision conditions

For the selected existential relation, the narrow bearer-presupposition and
no-self-production argument is substantively motivated under its stated
interfaces. It does not independently warrant all-subsets foundation or the
whole-roster source-existence principle. The strongest collective argument
adds a meaningful explanatory demand: actuality cannot be accounted for by
routing already-received contributions unless the account explains their
collective availability. Its application to every actual concretum, and its
exclusion of genuinely constitutive or beginningless productive realization,
remain insufficiently discriminated by the evidence inspected here.

Accordingly, the foundational conclusion is **not independently established
by this investigation**. The comparison remains underdetermined at collective
non-generation and actual realization; this is neither endorsement of a bare
infinite diagram as adequate nor a finding that the foundation claim is false.
The strongest rival's price is accepting an obtaining but everywhere derivative
existential order, together with a substantive account of its real full grounds,
direction and global status. It has not supplied that completed account here.
The foundationalist's corresponding burden is to defend why such collective
actuality must receive a contribution not wholly derivative within the selected
roster, without simply defining adequate actuality as source-backed Supply.
Neither price has been shown contradictory with an accepted floor item.

The **weakest immediate target is one actual root**, not exclusion of every
infinite branch. `WholeRosterFoundation.necessaryActualRoot` already turns
that root, actual population and contingent dependence into a necessary
actual root under EM. A genuinely exhaustive source-free rival challenges
that target. An infinite chain alongside a root challenges all-branch WF
only, and does not defeat this weaker sufficient source route. An independent
whole that really supports members without itself being supported could
satisfy the weaker target despite infinite internal detail. Whether its
supporting act is intrinsic, and whether the whole is concrete and actual,
remain application questions rather than consequences of its size.

For the stronger underived endpoint, the existing
`UnderivedRootRoute.underivedOfNecessaryRoot` can preserve a supplied necessary
actual root under its explicit support-transport and supporter-concreteness
interfaces. This reuse does not require a newly established all-branch WF
once the required root is supplied. It does not remove those interfaces or
prove the parent modal-union requirements. The research target must therefore
not be inflated into proving universal WF when the selected route needs only
one actual source plus its stated local/modal interfaces. No new route or
premise substitution is registered here.

Cumulative support must not double-count source-backed Supply, the borrowing
cut, WF and the whole-roster equivalent as independent defenses. Their useful
strength comparisons preserve the common unresolved applicability burden.
Moreover, even an independently warranted underived supporter would establish
less than WF of every branch: the exact source-anchored infinite controls
remain relevant. The necessary-concrete-underived parent also retains its
contingent-dependence, modal-support and union-WF obligations; no finding here
discharges those distinct premises or the further attribute routes.

This assessment would strengthen toward foundation if an independently
specified account of existential support justified collective non-generation
and excluded the strongest constitutive/causal realization *in that same
meaning*, including joint contributors and arrangements. It would weaken if
a positive actual-realization account supplied relevant full grounds and
explained its own global obtaining without importing an independent concrete
supporter or an unexplained selector. It would be suspended if the intended
relation were revised from concrete existential support to signal dynamics,
mathematical determination or general fact explanation. A source-existence
argument alone would revise only that obligation; it would not validate the
stronger all-branch WF or cross-world-union requirements.

The next discriminating inquiry is the **independent direction and sufficiency
of an explicit constitutive existence account**, compared with the proposed
purely routing interpretation. It should identify the actual relata, joint
arrangement conditions and status of the global realization, then test the
collective argument against that same account. Another Nat rank, Supply/WF
alias, loss inequality without existential calibration, or repeated “no first,
no middle” would not answer this missing application question. The present
worker returns this reassessment for allocation rather than expanding into the
parallel fact-PSR, modal-support or essence/identity assignments.

One selected existing source witness was re-materialized and read as recorded
above; no new source or attributed corpus claim was introduced. Historical
readings retain their prior source evidence. No new philosophical statement, proof, model,
source record, closure marking or owner-choice gate is introduced. All quoted
formula strengths refer to the existing explicit profiles. Actual premise
change: none. Source fidelity, actual interpretation and independent warrant
remain distinct from theorem validity. Required integration CI remains in
place; unchanged theorem verification is reused. The proposed judgment and
its synthesis received qualified acceptance in the independent semantic
challenge recorded above. This review does not establish the open premises;
final integration CI remains required.

Focused offline validation for this documentation/attempt delta: corpus
validation and attribution-check completed; no new or changed stating claim.
`frontier-diff --base 6d9b380099158c877373eaf34e2c6a9e4e6d01e4` computes
421 open root-reaching premises (282 bare, 94 supported, 45 stated) unchanged,
303 verified support alternatives unchanged, zero added alternatives, and
“no change.” Whitespace check passes. No proof input changed, so no build,
binding, Comparator or NanoDa rerun is claimed or needed for this delta.

## Current foundation judgment on the existence-only case (2026-11-17)

**Complete proposed outcome for independent challenge.** Whole-roster
foundation is a well-motivated candidate primitive about actual existential
support: derivative contributions do not explain their collective availability
merely by being redescribed as a network. Its strongest positive rationale is
an account of genuine contributions and their actual realization, not a ban
on infinity. The serious rootless rival instead takes a complete distributed
constitutive or productive order as obtaining, with a uniform account of its
members and arrangements. That is a substantive alternative; the inspected
evidence does not demonstrate its adequate realization or defeat it.

The existence-only case has a second, comparative support route through
maximum-in-esse causality and nonreciprocity at maximal targets. A new checked
comparison shows that **within the retained existence-bundle prefix**, that
nonreciprocity policy and whole-roster foundation are equivalent. This locates
the real choices of warrant: availability/foundation directly, or independently
supported comparative/causal content plus nonreciprocity. Repackaging either
policy through the other adds no corroboration. Shared premises do not erase
the possible warrant of either rationale.

Rootless distributed support challenges foundation. A fundamental natural
supporter can satisfy foundation and challenge later universal-source or
naming premises instead. This distinction is essential to the current overall
case; naturalism is not a general denial of foundation. No theistic winner,
root establishment or defeated rival is announced.

### Exact target, meaning and existing evidence

Baseline is `5a59f633da2aa983232ae823631e7510d703b1a5`. The current focus in
AGENTS commit `acd90e93a5cf92b3717cb5f957d55c813bb3acce` was read and applied:
God-existence first, coherent fixed-meaning routes, cumulative provisional
warrant, direct primitive options and meaningful horizontal support. No policy
file is copied or changed in this slice.

Target `5c898d24-d1f7-5087-b09e-3287a723e787` is
`WholeRosterNotTrapped`. Its consumer is existence-only argument
`5e8e6054-2f55-52dc-bb46-37816032d2de`, result
`973582b8-b190-5f29-ab82-2ae387cffc68`, with God-existence conclusion
`8626f8a5-9531-5da7-9ebd-f901e74b1129`. Related, dossier, brief, novelty and
consumer context were inspected, as were the maximum-target dossier/context
and prior foundation, equivalence, quantitative, cyclic and infinitist records.
The detailed received-being and cessation findings remain in
[the causal note](../eternity-dependence-connection.md); they are not repeated.

Fix one selected situation w, one actual-concrete domain (own esse in re),
one esse respect and one **current existential-support** relation R. The
intended arrows concern the bearer's actual being, not merely past generation,
a state change, observation or enabling condition. A productive contribution
need not be individually sufficient. A constitutive explanation counts as
this R only if it actually supports the whole bearer's existence in the chosen
sense; a fact-level explanation or arrangement label is not automatically a
Being-valued supporter. These are application commitments, not properties
built into `Profile.grounds`. No asymmetry, foundation or sufficient generation
is inserted into the relation's definition.

The exact graph restricts both endpoints to actual concreta. `recorded` lists
all incoming neighbours of each nonsource target; it asserts no sufficiency.
For the **whole** roster, the Trap's second clause is automatically met by
these nonempty records. Its first clause says that no member is a graph source.
The existing `WholeRosterRootEquivalence` therefore gives exactly the one-root
strength under actual population and EM. That theorem is imported unchanged;
this investigation does not duplicate it or identify it with an owner's verbal
commitment to adequate explanation.

A source elsewhere in the roster already satisfies this weak foundation test,
even if another component is rootless. Hence a discovered endless branch or
reciprocal dependent pair does not refute this premise. Conversely, a source
unrelated to the observed bearer is not yet its complete explanation. The
remaining existence-bundle premises must connect the selected root to universal
causal scope. The earlier isolated-root/intermediary correction in
[direct-grounding-warrant.md](direct-grounding-warrant.md#correct-scope-of-the-intermediary-control)
and the source-anchored infinite/cyclic controls remain authoritative.

### Positive warrant and the strongest matched rival

The strongest direct positive argument is that genuinely borrowed actuality
has an explanatory source character: an instrument exercises an efficacy it
receives, and further instruments route that efficacy rather than originate
it simply by being added. This supplies a defeasible reason to seek at least
one contribution actual independently of that routing. The account may stop
at a candidate primitive or intrinsically intelligible foundation; it need
not supply a prior proof of every commitment. Its content and defeaters must
still be explicit. The selected one-root conclusion is less demanding than
requiring every branch to terminate or every existent to have a finite supply
construction.

For the actual roster, this argument still needs a faithful collective
application. Actual received contribution is not zero contribution. An
instrument is not nonexistent while dependent. Nor is a plurality of real
acts automatically one act producing its own bearer. The prior collective
non-generation audit and #1378 whole-network results already test those
shortcuts; another attenuation formula or source-backed `Supply` definition
would not add warrant. The unresolved positive step is why the complete
organization cannot itself be the obtaining basis of all contributions under
this particular existential-support interpretation.

The strongest rival supplies **full actual support**, not merely arrows: each
bearer exists through actual contributors and the relevant arrangements;
those contributors have further actual grounds of the same kind, with no
R-source anywhere in the complete actual-concrete inventory. Its uniform
constitution or production rule explains the local existence facts. Global
obtaining is either explained by a separately characterized structure or is a
primitive commitment of the theory. The prior infinitist reading supports
uniform explanation as a defeasible virtue, not actual infinitism; its
fact-to-concrete-support mapping remains open. Positive fixed-point and local
full-group controls show specified consistency or determination, not actual
existential realization.

At matching explanatory scope, the foundation account also owes an obtaining
foundation and a faithful account of how it supports the derivatives. Bare
necessity or the name “source” does not supply that account. The rival's
primitive global actuality is not disqualified merely for being primitive,
while a source theory's primitive independent actuality is not disqualified
merely for lacking an earlier proof. Compare their independently specified
natures, actual realization, direction, completeness and explanatory economy;
entity counts and one-versus-many diagrams do not decide those questions.

There are two different global replies. An irreducibly actual natural whole
with no incoming R-support is a candidate root when it belongs to the chosen
concrete roster, even if its internal detail is infinite. It **satisfies**
this foundation step; its necessity, universality, attributes and entitlement
to the name God remain later questions. An organization of the same entirely
derivative members, or a global fact outside the concrete domain, does not
supply such a root merely by being called a whole. It can offer a different
explanation, but its precise R-profile and realization must be stated. Neither
classification is a refutation of naturalism.

### Horizontal support and the new discriminating comparison

Existing result `0f141e08-4ff8-5fe5-b8b1-6d5b82913fab` derives the exact
whole-roster premise from maximal-target nonreciprocity `bcf79e03`, alongside
population, actuality/cause correspondence and fixed-esse comparative inputs.
It does not assume all-branch WF or global asymmetry. The existing populated
control retains reciprocal **nonmaximal** dependents and an actual maximal
root. These results are reused, not presented as new findings.

New statement `fb1a8d86-b637-466a-b9b6-bdb5ea2a4b3e`, argument `1f14cdee`,
result `4b5f1d8a-a42c-43cf-a6d1-08998993f724` checks the reverse comparison on
six already-retained inputs of the twelve-input existence-only bundle:
population `56f68b40`, existing-to-act `0436de86`, direct esse-to-ground
`cb1cdea9`, genus causality `d9fad785`, grades-to-maximum `6c27657f` and EM
`ee4ab504`. Under this exact prefix:

```text
WholeRosterNotTrapped m w
  iff AtMaximalTarget m w InAct MoreIn esse
```

[The proof](../../TruthCore/Results/Causality/WholeRosterMaximalComparison/Solution.lean)
imports `actualRootExists`: foundation supplies an actual root n. It then
imports `maximumEqualsRoot` to identify **every** supplied esse maximum with
that same n. No actual incoming ground at such a target is therefore possible.
The other implication imports the existing maximal-target whole-roster theorem.
The six-prefix hypotheses stay inside the universal conditional certificate;
there is no claim of an unconditional equivalence or a minimal comparison
prefix. No new root, grade or explanatory relation is introduced.

This makes the horizontal rationale precise without pretending to prove it.
An independently motivated nonreciprocity claim about actual existential
priority can support foundation together with the comparative/causal inputs.
It is not merely the assertion that the roster has a root. But obtaining that
claim *from foundation* and returning through the existing theorem is no
corroboration. Defining R as strict priority would likewise leave the application
of actual existential contributions to that relation to be defended.

A genuinely rootless rival that retains the six-prefix package must reject
maximal-target nonreciprocity. An acyclic endless account need not reject
nonreciprocity at all: it can instead contest the maximum/comparative or
universal-causality application. Those are different mechanisms. It is invalid
to classify every rootless account as reciprocal, or to answer every such
account by prohibiting cycles. The old nonmaximal-cycle control also shows why
nonreciprocity need not be imposed on every dependent pair for this route.

### Cumulative assessment and continuation

The exact foundation premise has genuine positive motivation as a modest
nonborrowed-availability commitment, and remains a defensible direct primitive
option. The existing maximum/nonreciprocity route is a second substantive
conditional support option when its comparative and dependence commitments
are warranted independently; the new comparison prevents double-counting a
round trip as further evidence. Neither result proves that the positive
rival's whole actual realization is impossible.

The present evidence does not warrant a defeat of rootless full support, nor
an inference from local support coherence alone to foundation. It also does
not warrant treating a fundamental natural account as a foundation failure.
For God's existence, retain one coherent fixed-dictionary support bundle:
foundation produces n, the existing proof gives firstness and identifies
maxima with n, genus gives universal causal scope, and the remaining transfer,
remoteness and explicit nominal bridge name that same n God. Those later
steps are neither assumed into foundation nor supplied by the word “root.”
Modal necessity, intellect, will and the remaining classical attributes are
not established by this existence-only result.

The current branch's concrete advance is a verified comparison of the two
available foundation policies **within that bundle**, plus the matched rival
classification and warrant judgment above. The availability and realization
burden is not resolved by another equivalent source/Supply/cut presentation.
Reopen this premise with an independently specified real full-support account
of the complete roster, a positive argument excluding its rootless realization,
or independent warrant for maximal-target nonreciprocity together with the
retained comparative/causal application. No demand for a disjoint proof tree
or an independent argument for every primitive is imposed.

The next central discriminating allocation is `d9fad785`, universal
maximum-to-cause scope, on this same existence-only route. A fundamental
natural root can already satisfy foundation; ask what independently warrants
identifying a maximum in esse with the actual cause of **every** other being,
rather than merely ranking beings or supplying a local source. The existing
maximum/nonreciprocity approach depends on this same scope premise, so its
warrant affects both routes. Prior grade/cause and Fourth-Way records should
be reused before any new formulation. This is a named next question, not an
assertion that universal causality, naming or God-existence is established.

### Verification and claim/type sweep

The new Comparison's quantifier scope, six internal inputs, selected situation,
actual-concrete guards, esse dictionary, same-root maximum identification and
conditional iff were checked against the definition, statement, inference,
argument, result and generated frozen Challenge. No policy is an external
conclusion of a premise-free argument: only the universally conditional
comparison is certified. The theorem reuses the existing whole-roster/root and
maximum-based results unchanged. No source claim, primitive relation, old
Challenge, shared import/status or allowlist changes. The causal note receives
only a cross-reference to this outcome.

Under the unchanged prepared setup and heavy lock, focused Solution and frozen
Challenge builds pass; binding reports **1 bound, 0 pinned, 0 mismatch**.
Comparator and independent NanoDa accept result
`4b5f1d8a-a42c-43cf-a6d1-08998993f724`; explicit axiom inspection reports
**no axioms**. The Challenge has only its expected `sorry`; the Solution has
none. A generated inference label initially exceeded the metadata length limit;
its owned label/spec were corrected before successful corpus/binding checks.

Offline corpus and attribution checks, spec regeneration, bundle audit,
sense/definition/lexicon ratchets and whitespace check pass. Existing lexical
and ungenerated formal-status warnings remain; shared generation is left to
the coordinator. Convention sourceRevision is
`15f348b072188255da837578eaafc8a98f12fdf0`; no preflight repeated.
Computed `truth frontier-diff --base
5a59f633da2aa983232ae823631e7510d703b1a5 --frontier-root STMT-GOD-EXISTS`
reports **no change**: 404 open premises (283 bare, 76 supported, 45 stated),
lowest expanded route cost 6, 414 verified support alternatives, added 0.
The new comparison dossier was inspected after registration. Fresh independent
challenge of this complete proposed warrant judgment and final integration CI
remain coordinator-owned. No push, PR, watch or merge.

The next genus-causality investigation is retained in
[maximum-definition-fork.md](maximum-definition-fork.md#current-existence-bundle-judgment-select-the-cause-before-identifying-the-maximum-2026-11-17):
an existing common esse ancestor plus the existing narrow causal-composition
and causal-ascent premises yields fixed-esse maximal causality, now explicitly
consumed by a twelve-input existence-only sibling. This does not change the
foundation judgment or turn its one-source conclusion into universal scope.

## Owner reply: relational organization and actual relata (2026-11-17)

The owner's proposed reply improves the comparison by asking what makes the
relations themselves actual. The relevant question is not whether relations
can explain a thing's organization or identity; they often can. It is whether
relations whose obtaining requires the same actual concrete domain account
for that domain's existential availability. Keep the actual-concrete roster,
selected situation, esse respect and current existential-support relation R of
the preceding assessment fixed. Do not replace existence with arrangement,
efficient support with fact grounding, or actuality with mathematical
satisfiability while making this comparison.

### What the reply establishes, and which rival it addresses

| Proposed explanatory item | Positive assessment of the reply | Exact limit |
| --- | --- | --- |
| An abstract relation or rule specifying an organization | Specification gives conditions on a realization. Adding more conditions does not by itself supply an actual instance. Thus a pattern alone is not an actual existential supporter. | A separately warranted necessary and necessarily instantiated structure would be a stronger account, not refuted by this observation. |
| An ordinary real accidental relation among actual things | Its occurrence includes actual relata and, on the inherence reading, depends for its own actuality on an actual subject. It can explain how already actual things stand to one another without being their complete existential source. | Actual relata need not be independently individuated before every kind of relation, and this is not temporal precedence. |
| Relational activity through which members sustain or change one another | Coordination does not remove the bearer requirement for each real exercise. Under the existing mixed-priority interfaces, an exercise cannot productively originate its own bearer. This gives a substantive answer to productive self-bootstrapping. | It does not turn many exercises into one act, rule out all reciprocal maintenance, or prove that every endless path terminates. |
| Full constitutive determination at every level | The reply correctly requires actual constituents and all arrangement conditions, rather than relations drawn between merely possible nodes. A mere diagram or unique solution does not meet this burden. | The strongest rival already accepts actual constituents and full conditions. Mere co-entailment of relata and relation does not decide the direction of constitutive explanation or refute infinitism. |
| An intrinsically actual concrete relational whole | If the whole really is an actual concrete being and has no incoming R-support, it is an actual root under the existing target, whatever its internal organization. This alternative concedes the foundation step. | A global fact is not automatically a concrete bearer; primitive obtaining of a structure does not automatically imply a source in the selected concrete roster. Neither version alone proves necessity, uniqueness or God. |

This is an application comparison, not a claimed exhaustive partition of
possible ontologies. It identifies two unsuccessful substitutes for a source
(bare specification and productive self-origin), one potentially conceding
alternative (underived concrete whole), and the strongest surviving
constitutive alternative. It therefore narrows the dispute more than the
undifferentiated phrase "relationships hold everything up" does.

### The constructive foundational argument

On the selected borrowed-actuality reading, the argument proceeds as follows.
First, the relevant contribution is an actual exercise, not a condition that
would obtain if a domain existed. Second, the contribution's exercise requires
its actual bearer; coordination does not change that fact. Third, where the
members' availability is exhaustively derivative, reorganizing their
contributions supplies no additional *underived* actuality merely in virtue
of the organization. These points give a positive reason to distinguish
routing an actual contribution from accounting for its availability. The
foundation proposal answers the latter with actuality not received through
that same routing. This is a substantive explanatory proposal with prima
facie warrant, not an inference from a shortage of rival diagrams.

The third step supports the comparison without pretending to settle it by
definition. It does not say derivative contributions are zero, that their
sum is zero, or that a whole necessarily has every property of its parts.
The constitutive rival rejects the description of its explanatory work as
exhaustively routing borrowed efficacy: it proposes that actual constituents
and arrangements fully constitute further actual things at every level.
Against it, the discriminating question is whether the complete explanatory
account supplies intrinsic actuality, merely assumes actual realization, or
vindicates a different adequate memberwise explanatory aim. The preceding
Welchance audit supplies an actual positive uniformity/parity argument for
the last option; it is not a fabricated possibility.

An intrinsic answer can be assessed on its own merits; it need not be
efficient self-production or an independently proved premise. If it attributes
nonreceived actuality to a concrete whole, the foundation target is met.
If it attributes explanatory adequacy to a globally obtaining fact while
denying every concrete R-source, the fact-to-concrete-support difference
remains consequential. Calling that fact "a relation" neither answers the
availability question nor defeats the account. Likewise, the foundationalist
must specify a genuinely adequate intrinsic basis: an unexplained object
called necessary earns no advantage over an unexplained relational totality
merely through the name.

### Reuse and source scope

The productive subargument imports existing result
`e60831c7-14fd-5225-9471-060dffa50386`,
`ExistentialSelfActualization.noSelf`, concluding
`8550ca62-92d1-5ef0-af17-9de5bf272262`. Its bearer and product interfaces
`d07314a3-ac99-58df-8fa1-e21f0d53db5d` and
`66b7ac36-56a9-5907-8dc2-3dfb69100c9c`, and irreflexive/transitive mixed
priority `e9da0216-07df-5c7f-b9e8-475d12671f59` and
`37ae2e51-468c-5051-81ca-dfc6ae91f7b5`, remain explicit. The theorem does
not prove that its existence-token labels denote actual bearers. The
actual-whole classification uses the existing `ActualRoot` definition and
`WholeRosterRootEquivalenceAt`; it adds no fact-to-being bridge. The
unique-feedback and endless-chain controls retain their established scope.
No Lean, graph, definition, source-claim or frontier change is proposed.

A selective primary-text check prevents overextending the relation claim.
[ST I q.28 a.2 co.](https://www.newadvent.org/summa/1028.htm) distinguishes
a relation's reference to another from its accidental existence in a subject.
[ST I q.40 a.2 ad 4](https://www.newadvent.org/summa/1040.htm) expressly
distinguishes accidental relations presupposing distinct subjects from
subsistent relations constituting distinction. These consulted passages are
scope checks, not newly registered source readings or a Trinity premise in
the existence argument. They preclude attributing to Aquinas the universal
claim that relations always require antecedently individuated substances.
They do not establish an actually source-free concrete organization.

### Revised provisional judgment and next discriminating test

The owner's reply strengthens the case against a relational pattern offered
as a complete substitute for actuality, and clarifies why an intrinsically
actual concrete whole can concede foundation. Taken with the prior
bearer/act, received-actuality and intrinsic-reason analyses, foundation
retains positive explanatory warrant. The serious remaining comparison is
the full constitutive account's actual realization and explanatory scope,
not whether unsupported arrows are logically consistent. The present
research does not certify that rival as adequate or establish its
impossibility. No zero-change frontier count is treated as a philosophical
objection to the progress made here.

The next useful test is a concrete proposed full constitutive explanation:
hold its relata, arrangement conditions and explanandum fixed, and ask
whether the account explains this actual realization through an intrinsic
basis or only derives further facts conditional on its obtaining. A
successful source-free answer would weaken the collective-availability
warrant; an independently adequate underived answer would strengthen it.
Repeating the no-self-production theorem or imposing all-branch
well-foundedness would not decide that comparison.

## Reviewed owner-reply integration (2026-11-17)

The owner-focused batch integrates the relational reply above with the
[same-source motion reduction](prima-via-strength-consumers.md#2026-11-17-reducing-the-respects-through-the-source-of-esse),
[intrinsic-actuality reply](de-ente-extrinsic-source-1629.md#intrinsic-actuality-and-the-alternatives-own-commitments-2026-11-17),
[unreceived-esse uniqueness reply](de-ente-esse-source-1628.md#unreceived-esse-and-the-two-questions-about-plurality-2026-11-17),
[evil-sense audit](../rowe-evidential-evil.md#sense-by-sense-objection-audit-2026-11-17)
and [hiddenness inclusion](../hiddenness.md#hiddenness-as-a-special-case-of-evil-2026-11-17).
The substantive conclusions and continuing tests remain in those six existing
notes and seven existing attempts; this handoff adds no new research registry.

Two fresh independent semantic challenges reviewed the actual final drafts
and the coordinator's complete proposed conclusions. One checked foundation,
evil and hiddenness against the exact signatures, proofs, controls and selected
primary passages. The other checked motion and intrinsic actuality, with a
separate targeted uniqueness subcheck. Both found no substantive defects;
no repair round was required. This supersedes the pending-review wording in
the dated worker drafts. The review accepts the conditional reasoning and
qualified judgments, not actual divine reasons, premise establishment or a
complete adjudication of the theistic case. No fresh Lean certification follows.

Research started at `c1037682`; integration incorporates main `766c3c08`.
PR #1719's overlapping passive-potency assessment in
[modal-spine.md](modal-spine.md#same-first-being-passive-potency-application-2026-11-17)
was inspected: its preference for the composition support and its remaining
real-principle/esse-cause application question agree with this batch. Shared
reasoning is not counted as independent corroboration. The owner-specific
five-question scope used three disjoint research slices before allocating
fresh challenge of their complete drafts. Shared convention sourceRevision:
`833179f39f2f3848341f93e7a9acb4950b6803f0`.

Canonical context/related/dossier/brief/novelty retrieval was completed.
Offline corpus/attribution checks, bundle audit, research-metadata and label
checks, sense/definition/lexicon ratchets, and whitespace checks pass. All
187 batch specs regenerate unchanged. The affected-result selector selects
zero Comparator results. Existing lexical/status warnings and removable
allowances are unchanged and outside this batch. The local verifier preflight
found the expected exported-toolchain setup absent; it was not repeated.
Existing certificates are reused, and normal delivered-head CI remains required
before merge. No Lean, statement, definition, source claim, result or graph
change is included. The computed God-existence frontier comparison reports
no change; its diagnostic counts are not a judgment of philosophical merit.

## Complete existential-supply comparison: supplier cones and actual constitution (#1724, #1616; 2026-11-23)

**Target and current judgment.** The target is **ClosedActualEsseCollectionsRooted**
(20babef7) under one fixed q3a4 profile, not a ban on infinite past time.
**Provisional assessment: conditionally favorable** to a foundation principle
for exhaustive, currently productive existential supply: an act that borrows
its being cannot be the complete original source of that very actuality, and
mere recombination of such acts does not improve their independent supply.
This is substantive positive warrant for an *explicit primitive*, not proof
of the unrestricted tenseless, causally mode-unspecified application.
The strongest surviving account is an **actually constituted, exhaustive
rootless order**, potentially with a primitive global organization/actuality
fact. It gives a uniform local constitution account but has not shown that
its constitutive actuality is supplied without merely presupposing it.
That unresolved adequacy question must not be hidden inside the word
“derivative.” Earlier independent semantic reviews and source assessments
remain credited only for their dated scope; this section requires fresh review.

### Exact distinction and connected graph

Fix actual bearer x and r(c,x) := ActualEsseCause p c x:
c ≠ x, both c and x in act as to p.esse, and p.CausesIn c x p.esse.
One respect and one relation are held throughout the source-access portion.
In particular, it is **not** automatically efficient, presently sustaining,
a grounding relation at a particular world, or a relation between *acts*.

~~~mermaid
flowchart TD
  A["One actual esse-bearer: 78cffb8e"] --> R
  CCR["Closed supplier-cone foundation: 20babef7"] --> R
  EM["Explicit excluded middle: ee4ab504"] --> R
  R["Every actual bearer has finite r-access from an r-root: 7637c090"] --> S
  C["Every actual distinct esse has an actual r-cause: 457698e4"] --> S
  S["Any accessible r-root has represented esse = essence: sourceOfAccess"] --> U
  U["Connected identity source"] --> COMMON
  ONE["At most one actual identity bearer: a576300f"] --> COMMON
  COMMON["c6d92415: c35b1a5c common source of esse"] --> B
  B["Same-bearer world-ground interface: ca5403a6 plus its OPEN bridges"] --> N
  N["Actual concrete root; necessity requires c71c068c and compatible scope"] --> G
  G["Later same-source GOD_4/attribute consumer: separate companion premises"]
  PS["Instrumental power needs prior bearer actuality: bearer/act interface"] -. "positive warrant, NOT an implication" .-> CCR
  JR["Local joint supply vs inductive supply: DerivativeJointPower"] -. "conditional interpretation" .-> PS
  HI["Past actual bearer + persistence law: #1616/#1800"] -. "distinct relation/moment" .-> CCR
~~~

The crucial quantifier is **every** nonempty supplier-closed set of actual
bearers. For a fixed x, the set of *all* its finitely reachable predecessors
is closed even if it has infinitely many members. The condition rules out a
rootless predecessor *component*, not all infinite descending chains.
The certified ConcreteRootAccess.accessOfClosed (7637c090) and
ClosedEsseSource.sourceOfAccess yield a finite path from an uncaused actual
identity bearer to x (zero length only when x is itself that root).
ClosedEsseSource.commonSourceOfClosed (c6d92415) identifies all these roots
with the **same** n using the separate uniqueness premise. The existing
same-witness downstream results (#1729/#1731) preserve n through the
grounding-root and God-existence bundles only with their explicit bridges and
other open inputs. Represented esse/essence identity is not modal necessity;
an r-root is not automatically a world-ground root, necessary being, pure act,
sustainer, efficient creator, or God.

**Why global root existence is too weak.** WholeRosterRootEquivalenceAt
establishes, at a fixed world and selected grounding relation, that the
whole-roster not-trapped principle gives *some* root (with population and
excluded middle). ClosedEsseSource.RosterOnlyControl instead contains one
root plus a disconnected infinite rootless component. The source must belong
to the appropriate **local supplier cone**; the relation at the destination
must not be swapped during integration. ConcreteRootAccess.borrowedDecomposition
makes the general CCR burden exact: no wholly borrowed supplier-closed concrete
set plus the additional localized bridge for nonconcrete suppliers (under EM).
The full concrete-supplier bridge yields a stronger blanket equivalence.
None of these formal equivalences establishes a metaphysical adequacy norm.

### What counts as completed explanation?

The positive reconstruction, not a deduction from a label, has four steps:

1. **Actual exercise has a bearer.** An exercised instrumental capacity
   obtains only while the bearer is actual in the respect in which it acts.
   The mixed-token BearerPrior/ProductPrior proof of no existential
   self-actualization shows the contradiction for *productive self-origin*
   when one transitive irreflexive ontological priority governs both links.
   It does not exclude intrinsic necessity, self-maintenance or all
   constitutive loops.
2. **Borrowed efficacy really contributes.** Derivative powers can preserve
   conditions, shape a subject, and cooperate; their acts are not nothing.
   Yet a causal procedure whose productive operation presupposes already
   available bearers does not, merely through iteration or coordination,
   create that presupposed availability. This is a substantive standard of
   **complete existential supply**, not a theorem about arbitrary arrows.
3. **Completeness is local and relation-specific.** If the chosen r lists
   *all relevant existent productive suppliers* and the complete r-cone
   contains no non-received source, the arrangement offers only conditioned
   contributions. CCR rejects taking their totality as a full existential
   producer unless the whole/structure supplies independently actual being.
   That restriction on a complete cone is the decisive primitive. It
   need not forbid temporal infinity, nonproductive physical feedback,
   rooted cycles, or root-backed infinite paths.
4. **The basis must be an actual bearer in r.** A primitive mathematical
   configuration, law, abstract totality or group-level explanation does
   not imply an actual bearer with no incoming r-edge, nor a finite r-path
   from it to x. A concrete underived whole may satisfy the foundation
   claim but needs the same *r-connection* to the members. This is the
   principal gap in transferring the instrumental rationale to the
   mode-unspecified profile.

Aquinas, *De ente et essentia* c.3 [69874] (Leonine c.4) supplies
the distinction between received esse and esse per se; ST I q.45 a.5
distinguishes absolute being-giving from an instrument's disposition of
a presupposed subject. ST I q.104 a.2 explicitly permits creaturely
preservation, even per se: **not every causal contribution is creation**.
ST I q.46 a.2 ad 7 distinguishes accidentally from essentially ordered
causal regress: **infinite chronological succession is not thereby banned**.
These already examined passages support a per-se, being-giving reading,
not automatic closure over every tenseless causal mode. Cameron,
*Turtles All the Way Down*, §§4–5 (physical pp.4–5, 11–12), provides
defeasible comparative reasons for common foundations; Bevan,
*Metaphysical foundationalism*, §§1, 3–3.1, distinguishes a full joint
ground from binary finite-path access. Both source assessments were already
recorded in #1724; neither is a new premise-discharge claim here.

### Matched rivals and checked discrimination

| Rival mechanism, with its positive explanandum | What the available evidence tests | What still must be supplied |
| --- | --- | --- |
| Infinite **temporal** genealogy or accidental causes | A current bearer may persist after a producer disappears (SustainingDependence.Control.Certificate); ST I q.46 a.2 ad 7 allows per accidens infinity | A reason for current actuality if the thesis demands one; do **not** rewrite temporal origination as simultaneous existential giving |
| Genuinely infinite **existential** ancestry n+1 → n (every n actual) | EsseSource.InfiniteRegressControl and ClosedGroundingRoots.Control.pureRegress have no source; local causal assignments remain coherent | A productive interpretation of each same-respect edge and a full account of their joint obtaining; a brute global order is a positive stopping proposal, not a contradiction |
| Finite mutually supporting **esse causes**, each with distinct esse | New SourceFreeFiniteCircleControl: both r-edges, coverage, population and at-most-one identity hold; neither CCR nor common-source follows | An actual productive-priority/realization law; an uninterpreted pair of reciprocal causes proves no productive self-creation |
| Actual **joint powers**, including all-borrowed productive groups | DerivativeJointPower.SourceFreeControl shows simultaneous two-contributor local power equations and coherent scenarios while inductive Supply gives no powered result; rooted examples distinguish intrinsically supplied from locally admitted | Either defend a coinductive productive notion of supply, or give an actual intrinsic contribution; fixed-point selection alone is not exercise of a power |
| **Holistic constitution**: real members, arrangement and whole jointly make each member actual | UniqueFeedback.Controls admits a unique global Boolean solution; the old owner reply distinguishes relational constitution from merely drawn arrows | Say whether the totality is a concrete independently actual whole (potentially an underived source), an abstract rule, or a primitive obtaining fact; show its identity and causal role at the selected r, not simply global solution uniqueness |
| **Circular grounding** without productive causal loops | RootedCycleControl demonstrates that some cycles coexist with a genuine root; an unrooted circuit violates CCR but not every conceivable grounding policy | A joint full-ground account under a defended nonproductive/constitutive standard; mixed-token self-production refutes only its stronger productive interpretation |
| **Existential inertia**: the very same existing bearer, earlier actual existence, and a persistence law | SustainingDependence.Control.Certificate isolates onset-without-parity and originating-without-sustaining; #1785/#1800 leave actual-past-plus-law alive | A law explaining the *later existence of the same bearer*, not merely change of an already existing subject. The opposite thesis must defend nontransferable received esse or parity independently |

Finite assignments do not refute infinite accounts, and the existence of a
formal model does not show its interpretation can instantiate actual
productive, grounding or constitutive relations. Conversely, no evidence
above proves that holistic constitution or persistence laws are metaphysically
impossible. The two-bearer r-circle newly checks a *missing-premise boundary*
in the exact cause-of-being dictionary; it does not replace the richer
infinite or joint-exercise models.

### Primitive stopping points, cumulative judgment, and reopening conditions

**Defensible primitive candidates, held apart:** (i) actual exercise cannot
supply the actuality of the very bearer on which that exercise depends,
**for the same productive-priority relation**; (ii) a complete supplier cone
of received esse must have nonreceived actual supply (CCR, the principal
foundation primitive); (iii) complete existential-supply relevance of r,
including constituents/wholes and the same moments/respects; (iv) the
inertialist's positive past-actuality-plus-law principle. These have different
content, explanatory costs and possible truth conditions. A foundation
can take an underived bearer as intrinsic actual being without asserting
efficient self-production; the rival can take the whole's obtaining as
primitive without being accused of an explicit logical contradiction.
Apply the *same adequacy standard* to both primitive stopping points.

**Provisional conclusion.** The received-actuality/instrumental case gives
real conditional comparative support to local foundation: a list of conditioned
powers does not alone explain their available existence, and an inductive
production account demands some non-borrowed supply. It is stronger than
“no infinite series” and avoids treating the rival's efficacy as null.
But unrestricted 20babef7 remains open: the selected r still includes
mode-unspecified causes, the global-to-every-local-cone scope principle
needs defense, and a complete, actually instantiated constitutive account
might bypass *productive* supply without secretly being just an arrow graph.
This result supports the existing **direct assumption option** for CCR; it
does not establish a new proof route or disprove naturalism. Independently
actual concrete nature could occupy the underived slot even if God
identification later fails.

**Reopen only for discriminating change:** (a) a fully specified actual
source-free constitutive model with constituent identities, joint sufficiency
and an independently justified actuality/grounding direction; (b) evidence
that every relevant r-edge is currently productive per se, or a narrower
source theorem on a truly typed subset with a proved coverage bridge;
(c) a constructive supplier-complete local cone that defeats the
collection-level sufficiency norm under the same explanandum; (d) a
substantive law-and-earlier-actuality account for received persistence
(#1800/#1801/#1802) or a defended nontransferability argument against it;
(e) a new same-bearer/same-relation counterexample to the world-ground
bridge. Mere rewording of a regress, extra arrows or repetition of
the same stopping-premise demand calls for reuse, not a new campaign.

**Reuse checks for the research loop.** An all-borrowed source
invokes DerivativeJointPower only when its events denote exercises of the
required powers; an all-borrowed actual-esse *bearer* cone invokes CCR
only with supplier-complete r; a global unique-solution claim invokes
UniqueFeedback rather than source-access; and an origin/persistence claim
invokes SustainingDependence with histories. ClosedGroundingRoots and
ConcreteRootAccess decide the local-vs-whole distinction on their
own grounding profile. The historically generated (past-law) boundary
does **not** inherit a sustaining-source rebuttal. The existing
context/dossier/brief/novelty tools should retrieve this single
canonical account through its linked De ente attempt/issue;
do not register equivalent arguments or change existing definitions.
This changes warrant/reuse, not the computed God-root frontier.
A comparison produced without the repository CLI is not represented as
a computed frontier-diff.

**Self-sweep and review handoff.** The added two-bearer control uses one
p.esse and r, no world/temporal claims, all-actual guards, two nonidentical
essences/esse values and no witness of represented identity. The
finite control is explicitly an interpretation, not a metaphysical
nonentailment theorem about actual causal powers. No source-attribution
record, existing Challenge, argument/status or premise binding is
changed. Required before integration: independently challenge the
exact wording of the new conclusion against q3a4, the group exercise
model, the source passages already recorded in #1724, #1616's
history semantics, and the existing root-identity interface; review
whether the control proves precisely its stated conjuncts. Validate
the Lean file and normal delivered-head checks. No independent review
or new proof certification is asserted in this draft.

