# Unique feedback and whole-chain explanation (#311)

The state equations `a = !b`, `b = a && b` have one satisfying
Boolean pair, `(true,false)`. Their gates are nonconstant: negation
changes across its two inputs; conjunction changes when either input varies
with the other held true. These are logical constraints. They are not
world-local causal edges, temporal evolution, pure copying of plans, or
borrowed instrumental powers. Sensitivity is a truth-table property, not
an assertion that each single-bit perturbation at the solution changes
both outputs. [Research record](../../corpus/attempts/unique-feedback-explanation.json)

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
fact. It gives a uniform local constitution account, and it owes the same
burden as the foundation: each side takes a primitive actuality (the rival's
global obtaining fact, the foundation's underived act) and must show that
primitive adequate under one standard (see "Primitive stopping points" below).
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

### A fixed actual-bearer test for the holistic rival

Take two actual distinct-esse bearers u and v at the selected respect, a
constitutive arrangement A, and the actual fact F that u, v, and A obtain
together. The strongest proposed **source-free holistic reply** does not
consist of two bare arrows. It says (1) u and v are real constituents
with their own exercised capacities; (2) their configuration A is an
actual organizing condition and not merely a diagram; (3) a *complete*
constitution rule derives both existence facts from the obtaining of
the configured whole W; and (4) W's obtaining may be a primitive
actuality fact F instead of the effect of an external productive act.

On that reconstruction the constitution rule explains **why the
constituents co-obtain given F**, including their interdependence and
arrangement. But if F is itself indispensable and primitive, the
constitutive rule does not yet explain **why F obtains** (as opposed to
no such whole). That is a real remainder under a total-existence
explanation norm, not a proof of inconsistency. A foundation account
also ends with primitive actual being: it must defend why a source with
unreceived esse is a better stopping point than the whole's primitive
obtaining. The proposed asymmetry is that an actual independent
source does not need to borrow what its productive capacity gives,
whereas all received member powers together retain that dependence.
This asymmetry addresses an aggregate of received member powers; it does
not discriminate against a rival that takes a primitive obtaining fact F
instead (see the equal-standard rule below).
This is a reasoned comparison of explanatory roles, not a reduction
of the rival to a tautology.

If W is independently actual and an efficient/current source of u and
v, it may satisfy a narrowed foundation principle, but only a proven
bridge W → u/v in **ActualEsseCause** lets the existing CCR route
consume it. If W is the mereological fusion identical in content to its
members and A, its grounding relation is not automatically a productive
esse cause; translating it by name would change the question. If
F is an abstract structural truth, specifying its constraint does
not by itself provide an actual bearer or production act; a defender
may instead make the truth itself metaphysically fundamental,
requiring a separate explanatory-adequacy comparison.

The user-facing test must compare the *same* explanandum: either
the constituents' existence conditional on F (where the holistic
account has a substantive answer) **or** the actual obtaining of the
entire configured order (where both camps choose a stopping point).
It is invalid to demand an external explanation of the rival's
ultimate while exempting the foundational primitive from every
applicability challenge. No formal impossibility of a primitive F
is claimed.

### Exactly where the originating/sustaining and non-efficient forks matter (#1616)

The relevant root-interface inference is the **open** cause-to-concrete-
ground bridge `cb1cdea9` (STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND, an
open statement): when `CausesIn c x esse` is tenseless and
mode-unspecified, its use to infer `ActualConcreteGround m w c x`
requires `concrete c`, `ExistsAt w c` and `m.grounds w c x` at the
selected **world** w. Here w is a world of a Kripke frame
(`BruteFoundationBoundary.Profile`) and "present at w" is world-relative
existence, not temporal concurrence (DEF-PRESENT-ESSE-SUPPORT). None of
these conditions is in the type of `CausesIn`, and even its actual-esse
guard is world-free. The origin-versus-sustaining question (#1616) bears
on `cb1cdea9` only through an explicit, OPEN bridge reading worlds as
moments: in a history, a dead parent or vanished maker can be a real
*originator* without presently sustaining the product, and
`SustainingDependence.Control.Certificate` (in its separate
`History W B T` frame) checks origin-at-onset plus later existence
without same-time giving. That is an existing finite counterinterpretation
for the stronger automatic origin→sustain reading, not a denial of
historical causal efficacy, and it does not carry over to the world-indexed
bridge by name.

The F2 restriction is distinct: even **co-present** exemplar or
final causes may explain a thing's *form*, action, intelligibility
or end without productively grounding its bare existence. Suppose a
present design serves as exemplar of an artisan's actual product;
identifying “is an exemplar for its production” with “supplies its
esse at this same moment” is an additional causation-mode premise.
Likewise a purpose can explain why an agent makes a thing without
itself being a concrete productive giver of the product's actuality.
The bare `CausesIn` field has no mode tag, so any **application** of
the open `cb1cdea9` statement must either narrow it to
genuine esse-giving causes, or introduce a defended exemplar/final-
to-productive-esse bridge. It must not be advertised as true of
every causal role just because it mentions `esse`. This is a scope
caution, not a demonstrated failure mode: the artisan example shows
exemplar causation of form or production, and no instance satisfying
`CausesIn c x esse` under DEF-CAUSE-OF-PERFECTION with a merely exemplar or
final cause has been identified. The separation would require a genuinely
typed causal-mode fork for formal registration; the current note does not
manufacture one.

The strongest positive per-se application says that an actual
instrument only supplies derivative efficacy **while** its
actuality is received from its source; its dependence is not just
a biographical fact. If source and recipient are co-present
at the relevant time, and the source's actual existential power
is genuinely transmitted to the recipient under an asymmetric
priority of giving, one can defend a specific productive relation
and test supplier completeness locally. The inference still needs
a bridge from *this exercised power* to `ActualEsseCause` on
bearers and to `ActualConcreteGround` at w, rather than
equating three distinct relations.

The historical inertialist's strongest option retains the same
bearer's earlier actuality plus a principled law of persistence.
It denies the **present** productive transfer, not necessarily
an originating cause or an earlier received existence. Its
continuation is owned by #1800/#1801/#1802. Since a surviving
origin-only cause can fail the presently sustaining reading (in histories,
reaching `cb1cdea9` only through the OPEN world-as-moment bridge) and a
co-present non-efficient cause is a scope caution, no new proof of `cb1cdea9`
or rejection of inertia is claimed; the existing positive case
is strongest for **specified essentially ordered,
currently productive powers**, not an unrestricted tenseless
cause-of-esse dictionary.

### Matched rivals and checked discrimination

| Rival mechanism, with its positive explanandum | What the available evidence tests | What still must be supplied |
| --- | --- | --- |
| Infinite **temporal** genealogy or accidental causes | A current bearer may persist after a producer disappears (SustainingDependence.Control.Certificate); ST I q.46 a.2 ad 7 allows per accidens infinity | A reason for current actuality if the thesis demands one; do **not** rewrite temporal origination as simultaneous existential giving |
| Genuinely infinite **existential** ancestry n+1 → n (every n actual) | EsseSource.InfiniteRegressControl and ClosedGroundingRoots.Control.pureRegress have no source; local causal assignments remain coherent | A productive interpretation of each same-respect edge and a full account of their joint obtaining; a brute global order is a positive stopping proposal, not a contradiction |
| Finite mutually supporting **esse causes**, each with distinct esse | New SourceFreeFiniteCircleControl: both r-edges, coverage and population hold, and at-most-one identity holds **vacuously** (no bearer has esse equal to essence); neither CCR nor common-source follows. `RosterOnlyControl` already showed coverage plus at-most-one plus two actual bearers do not give CCR; what is new is a finite domain with no identity bearer at all and reciprocal edges of the same relation | A bridge from `ActualEsseCause` to the efficient/per se priority reading: given priority of cause over effect, transitivity and irreflexivity, the existing `noPerSeCausalLoop` (PER-SE-CAUSAL-LOOP-IMPOSSIBLE) already excludes such loops of any finite length, so this is a rival in the table that existing verified work excludes conditionally; an uninterpreted pair of reciprocal causes proves no productive self-creation |
| Actual **joint powers**, including all-borrowed productive groups | DerivativeJointPower.SourceFreeControl shows simultaneous two-contributor local power equations and coherent scenarios while inductive Supply gives no powered result; rooted examples distinguish intrinsically supplied from locally admitted | Either defend a coinductive productive notion of supply, or give an actual intrinsic contribution; fixed-point selection alone is not exercise of a power |
| **Holistic constitution**: real members, arrangement and whole jointly make each member actual | UniqueFeedback.Controls admits a unique global Boolean solution; the old owner reply distinguishes relational constitution from merely drawn arrows | Say whether the totality is a concrete independently actual whole (potentially an underived source), an abstract rule, or a primitive obtaining fact; show its identity and causal role at the selected r, not simply global solution uniqueness |
| **Circular grounding** without productive causal loops | RootedCycleControl demonstrates that some cycles coexist with a genuine root; an unrooted circuit violates CCR but not every conceivable grounding policy | A joint full-ground account under a defended nonproductive/constitutive standard; mixed-token self-production refutes only its stronger productive interpretation |
| **Existential inertia**: the very same existing bearer, earlier actual existence, and a persistence law | SustainingDependence.Control.Certificate isolates onset-without-parity and originating-without-sustaining; #1785/#1800 leave actual-past-plus-law alive | A law explaining the *later existence of the same bearer*, not merely change of an already existing subject. The opposite thesis must defend nontransferable received esse or parity independently |

Finite assignments do not refute infinite accounts, and the existence of a
formal model does not show its interpretation can instantiate actual
productive, grounding or constitutive relations. Conversely, no evidence
above proves that holistic constitution or persistence laws are metaphysically
impossible. The two-bearer r-circle checks a *missing-premise boundary*
in the exact cause-of-being dictionary (new relative to `RosterOnlyControl`
in having a finite domain, no identity bearer and reciprocal same-relation edges); it is
a kernel-checked, unregistered helper theorem, not a Comparator-audited
result, and it does not replace the richer infinite or joint-exercise models.

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
powers does not alone explain their available existence. The inductive
`DerivativeJointPower.Supply` standard *formalizes* the foundation primitive
(its derivations bottom out in the `intrinsic` constructor) rather than
supporting it, since inductive versus coinductive supply is the contested
choice; the remaining warrant rests on that primitive and on the
instrumental argument. It offers better-targeted warrant for a logically
weaker principle than "no infinite series" (CCR is the weaker side of the
registered strength order 044974e5) and avoids treating the rival's
efficacy as null.
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
p.esse and r, no world/temporal claims, all-actual guards, and for both
bearers `esseOf = true` and `essenceOf = false`, so no bearer witnesses
represented identity and the at-most-one premise holds vacuously. The
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

## Supplier-rule selection test: unique feedback versus underived actual input (#1724, #1616; 2026-11-23)

**Question and fixed semantics.** Can an all-received *actual-esse-cause* network
supply its own actual obtaining merely because the whole has a unique global
fixed-point solution? This test refines the prior [complete existential-supply
comparison](#complete-existential-supply-comparison-supplier-cones-and-actual-constitution-1724-1616-2026-11-23);
it does **not** repeat its finite circle or infinite chain proofs. The selected
`p : Question3.Article4.Profile B P R` and
`ActualEsseCause p c x` retain their world-free, mode-unspecified, same-respect
guards. A proposed `state : B → Prop` and
`rule : (B → Prop) → B → Prop` describe a *mathematical assignment and
constraint*, not automatically the actual bearers, exercises or worlds of `p`.
The condition `SupplierStateFixed rule state` says precisely
`∀ x, rule state x ↔ state x`.

**New typed discriminator (Lean helper theorems, not registered argument
results):**

- `EntirelyBorrowedRule p rule` means that in **every candidate state**, if
  the rule activates x, some *active* c satisfies **this** `ActualEsseCause p c x`.
  `ClosedEsseSource.emptyFixedOfEntirelyBorrowed` proves that the all-absent
  assignment is a solution. `populatedBorrowedStateNotUnique` proves that
  **any** populated fixed solution has a distinct empty fixed solution.
  This holds for *any carrier* and imposes **no** well-foundedness, finiteness,
  acyclicity, transitivity or conservation-law assumption.
- `SeedOrBorrowedRule p seed rule` allows a **seed-labelled
  activation exception** to borrowing in the rule's disjunction. The seed
  predicate is not required to denote an underived or even actual bearer;
  this is a one-way constraint, not a sufficiency or instantiation claim. `uniquePopulatedStateNeedsSeed` says that a populated
  fixed solution **unique among all solutions, including empty**, entails
  `∃ x, seed x`. The proof is by excluding the all-absent solution, not by
  stipulating induction/least-fixed-point semantics.
- `uniquePopulatedStateHasActualRoot` adds two explicit, **OPEN application**
  commitments: any seed is a genuinely actual r-uncaused bearer
  (`SeedIsActualEsseRoot`), and a seed activates in the selected solution.
  It then yields an **active actual underived r-root**. The latter two bridges
  are precisely where an *independently existent producer* differs from an
  abstract law or bare positive bias. Neither bridge follows from uniqueness,
  `ActualEsseCause`, population or Lean's empty-state proof.

**Essential adequacy warning.** The profile `p` fixes `InAct` and
therefore fixes which `ActualEsseCause` arrows pass their actuality guards;
the candidate state **does not vary the actual profile**. In particular,
the empty assignment is *not* a counter-world in which no bearer of `p`
exists. It is a second mathematical assignment to an abstract activation
constraint built over the fixed r. Applying this no-input result to existential
production requires a further **OPEN** bridge that the candidate assignments
are the relevant admissible total-existence alternatives, with a consistent
variation of `InAct` and productive `CausesIn` if reality varies. A global
rule that requires some existent, or a domain with a necessarily actual
substrate, need not admit the empty state. The theorem does not contradict
the stronger world-indexed holistic account without that application.

**Novelty boundary.** The zero/positive fixed-point split is structurally
anticipated by `Logic.Regress.Graph.transmission` (lfp versus gfp) and
`ContractiveBorrowedPower.ZeroExercise` (under contraction and zero
preservation). The new theorem does **not** discover that fixed points
generally have this property. Its increment is the expressly quantified
all-candidate `ActualEsseCause` activation condition, the converse
unique-populated/seed inference **without contraction or WF**, and the
explicit, separately named *same-r actual-root* bridge. No additional
independent evidential warrant is claimed from reusing the same mathematical
zero-solution reasoning.

**Independent semantic challenge and repaired countermodel (PR #1878,
2026-11-23).** The theorem establishes the existence of a *seed-labelled
exception* to the all-borrowed activation rule, **not** source independence.
This is not merely a terminological objection: use the already verified
`sourceFreeFiniteCircle` profile, take `seed := fun _ => True`,
`rule := fun _ _ => True` and the all-true state. The seed-or-borrowed
condition holds, the state is populated and uniquely fixed (pointwise, under
the constant-true rule), but every bearer still has an actual incoming
`ActualEsseCause`, so there is no r-root. The independent reviewer
identified this counterexample at the previous head; it is a reuse of
the existing circle's relation assignments and the present definitions,
**not** a newly registered or checked joint metaphysical model. The root
conclusion remains conditional on `SeedIsActualEsseRoot` **and** seed
activation. The diagram now marks the r-to-rule application OPEN and
relabels the exception before those bridges. This is one targeted P1
repair of the review's actual final-synthesis claim, not new support
for a primitive source.

The first result is a discriminating *conditional incompatibility*: jointly
claiming (i) no activation without some already active supplier, (ii) a
populated fixed solution and (iii) **uniqueness among all fixed solutions**
is inconsistent. There is no such contradiction if the uniqueness quantifier
ranges only over *populated* states, if the law rejects the empty state by an
independently defended global actuality constraint, if non-supplier inputs are
permitted, or if `rule` is not an existential production rule. Nor does the
mere presence of a mathematical nonempty solution establish that it obtains.

~~~mermaid
flowchart TD
  R["Same-r ActualEsseCause: existing q3a4 dictionary"] -. "OPEN productive rule application" .-> N["No activation without active r-input"]
  F["Populated fixed solution"] --> D{"Distinct empty solution?"}
  N --> E["All-absent state fixed"]
  E --> D
  D --> C["Therefore not unique among ALL solutions"]
  U["Unique populated state among ALL solutions"] --> S["Some seed / activation exception required"]
  F --> S
  SEED["Activation requires seed OR active r-input"] --> S
  S --> V["OPEN: seed activates; is actual underived r-root"]
  V --> ROOT["One actual r-uncaused bearer in selected state"]
  ROOT -. "Does not establish supplier access" .-> CCR["CCR / 20babef7: every local supplier cone rooted"]
  CCR --> COMMON["Existing c6d92415 / c35b1a5c (plus coverage, uniqueness, population, EM)"]
  COMMON --> GOD["Existing same-witness necessity/GOD_4 only through separate OPEN bridges"]
~~~

**Reused discrimination rather than re-created models.** In #311,
`UniqueFeedback.Controls` already gives a unique nonempty Boolean state with
a negating gate and a conjunction gate. Its first gate is **not** a
purely borrowed, no-spontaneous-activation rule: at the empty assignment it
can produce a true output. The present theorem therefore does **not** refute
that structural model; a proponent must say whether the negating/selection
rule is a productive actuality input, an independently necessary structure,
a global constraint on admissibility, or only a mathematical description.
The unique Int-history result in the existing
[explanatory-selection note](explanatory-selection-736.md#unique-global-solution-with-no-first-stage)
likewise has an additional global restriction. Neither model certifies
metaphysical production. #1871's `SourceFreeFiniteCircleControl`,
`EssentialPowerUnderdetermined`, `DerivativeJointPower.SourceFreeControl`
and `EsseSource.InfiniteRegressControl` already witness coherent local
source-free assignments; their proofs are not repeated. Their positive
actuality claim needs an *additional* selection/obtaining account if
all-absent states satisfy their exact proposed activation law.

### Comparative result at matching explanatory scope

| Account | Positive explanatory success | Consequence of the new discriminator and live commitment |
| --- | --- | --- |
| Only borrowed positive production, finite circle or infinite actual-esse chain | Explains transmission from already actual suppliers, whether finitely or infinitely many | If **all** activation needs previously active suppliers in each admissible state, an empty solution remains: a *uniquely forced nonempty* whole is unavailable under this law alone. A primitive actual selection remains coherent. |
| Actual constitutive whole with a unique global configuration | Explains relative arrangement and member co-obtaining *given* the real whole and its rule | Global uniqueness **under a global constraint** can survive, especially with non-positive gates or nonempty-only admissibility. The obtaining of the constraint/whole remains a distinct question, not logically inconsistent. If the whole is itself an underived actual r-supplier, an explicit whole→member productive bridge could connect it to CCR. |
| Genuine mutual constitutive or explanatory feedback | Can give nonproductive reciprocal determination without temporally preceding or creating oneself | The theorem applies only if this is further read as *positive existential activation solely by active r-suppliers*. That bridge must be defended; a mutual full-ground mechanism may instead take actual organization as primitive. |
| Existential inertia with past bearer plus law | Explains later continuation conditional on earlier actual presence and absence of a destroyer | Not a same-time r-activation equation. An infinite earlier history may fix a profile only with a global boundary/instantiation condition; `#1616`'s temporal-to-world and origin→sustain bridges remain OPEN. The positive diachronic explanation stands at its proper explanandum. |
| Underived concrete source with genuine productive ability | Explains derivative recipients from an independently actual producer, while accepting nonproductive secondary causes | If an input really is active and r-uncaused, the source theorem yields *some* root without WF. Unique solution is a separate assumption; common supplier-cone access, source uniqueness, modal necessity, pure actuality and simplicity **do not** follow from this proof. |
| Necessary or brute whole actuality as primitive | Gives a legitimate stopping proposal for actual instantiation rather than a merely conditional member explanation | A necessary-global-structure account must defend its modal and realization interpretation; a brute obtaining account openly declines further existential explanation. Apply the same adequacy test to the source's primitive act, rather than declaring either primitive inexplicable by fiat. |

**Cumulative provisional assessment (2026-11-23, base
`f3e13e5f6ab2970c34351e7ef294dccbf276815a`).**
This test adds *conditional positive leverage*, not a new unconditional
foundation proof. The strongest inference from unique nonempty rule selection is a
**labelled activation exception**, not the actual production or independence
of that exception. The constant-true seeded source-free profile described
above is an explicit structural counterinterpretation to the stronger
automatic seed→source reading.  Purely input-borrowing positive laws do not uniquely select
an actually populated global assignment; the source-backed account can
supply the missing input **if** it provides independently actual productive
being. The holist can retain a real, source-free and self-organizing whole
by defending its own primitive obtaining or a richer rule, so there is no
general refutation of holistic actuality or source-free infinite causation.
Against the same entire-order explanandum, the foundation case remains
**modestly favorable on an exhaustively productive per-se reading**, while
the global primitive versus unreceived-act contest is **not decided**.
This finding strengthens precision of the existing warrant, not the truth
status of `20babef7`. The connection to `c6d92415` remains exactly
as in #1871; an isolated root theorem cannot be substituted for supplier-cone
closure or same-source reachability. The downstream necessary-being,
pure-actuality and simplicity bundles retain all their independent open
bridges and no new computed premise is discharged.

**Semantic self-sweep, boundaries and next test.** The new theorem's
all-states quantifier matters: restricting uniqueness to nonempty states
would invalidate the conclusion. A fixed state is an abstract solution,
not an instantiated world; `ActualEsseCause` here has no temporal index,
efficient-causing tag or actual-exercise witness. `SeedIsActualEsseRoot` is
an explicitly strong application bridge, not a derived source fact, and
the last theorem shows **one root**, not global CCR. These are
unregistered helpers awaiting delivered-head Lean CI (not Comparator
certificates); no corpus statement, source attribution, argument or
existing semantic sense is changed. **Independent semantic challenge** is
required on the final note and formal types before using the sharpened
ranking as reviewed support. A useful next test is a *positive*, actually
instantiated holistic rule with genuine member/exercise identity and
productive supply, and an explicit reason the no-input state is not an
admissible rival, compared against an underived bearer under the **same**
adequacy criterion. A distinct #1616 test must preserve the *same bearer*
over time rather than importing the world-free r as a sustaining cause.

## C1: can an entirely derivative reality account for its own actuality? (#1724, #1616; 2026-11-23)

**Commitment C1 (owner statement).** Every complete, nonempty system of actually
existing, existentially derivative beings must ultimately depend on something
underived. This section fixes its meaning, tests C1 and ¬C1 at matching scope,
adds a verified alternative support bundle, and records the current
provisional judgment. It reuses, and does not repeat, the
[complete existential-supply comparison](#complete-existential-supply-comparison-supplier-cones-and-actual-constitution-1724-1616-2026-11-23)
above, the #1871 finite circle, the infinite and rooted controls of
`ClosedEsseSource`, `DerivativeJointPower`, `UniqueFeedback`, the
lfp/gfp regress models of `TruthCore/Logic/RegressDomains.lean`, the #751
actual-world-gap results and the #1109 whole-to-parts work. The
supplier-rule selection theorems of #1878 (merged; section above) are cited,
not re-derived.

### Fixed meaning: two readings of "something underived"

Hold one q3a4 profile and r(c,x) := `ActualEsseCause p c x` (distinct, both in
act as to esse, `CausesIn c x esse`, tenseless, mode unspecified).
"Complete" means closed under every actual r-supplier of every member;
"existentially derivative" means received in r (`ReceivedActual`, definition
e7aa4529). Then:

- **C1-bearer** says the underived item is an actual bearer of the same
  profile, reached through r. Because a complete system contains its suppliers,
  this is exactly CCR (20babef7): no nonempty complete system is wholly
  received. It forbids no infinite series as such: root-backed infinite
  descents and rooted cycles satisfy it (`RootedInfiniteControl`,
  `RootedCycleControl`, and control 1 below).
- **C1-anything** lets the underived item be a fact, law, configuration or
  whole outside the bearer domain. It is not formalized, it leaves its
  dependence relation undefined, and no root route consumes it: an underived
  *fact* gives no actual source, no r-path and no same-bearer identity for the
  later bridges. There is no sibling corpus statement for it.

The distinction sorts the listed alternatives before any argument. An
autonomous necessary impersonal totality, a universe whose actuality is
primitive **and which is itself an unreceived bearer**, and priority monism
with an unreceived cosmos **accept** C1-bearer, provided their whole r-causes
the members' esse (control 1 has this shape, with `none` as the whole). Their
disagreement with the theistic case lies later, at necessity, unity,
simplicity, intellect and naming. C1-bearer is **denied** by a complete
system with no underived bearer at all, a regress or a loop, whose total
actuality is either not a further fact (Hume–Edwards) or a primitive fact with
no bearer. Whether the second version satisfies C1-anything depends on
whether a system "depends on" a primitive fact about its own obtaining, which
C1-anything does not settle; it is classified here as denying C1-bearer while
accepting a primitive.

### Distinguished structures and where C1 bites

| Structure | Relation to C1-bearer |
| --- | --- |
| Temporal ancestry (parents, past states) | Not r unless each ancestor presently gives esse; an infinite past is compatible with C1 (ST I q.46 a.2 ad 7; `SustainingDependence.Control.Certificate`). #1616's persistence-law rival lives here |
| Per se ordered present supply | The intended application of r. `noPerSeCausalLoop` excludes loops in its own vocabulary (`EfficientlyCausesIn`, priority, transitivity, irreflexivity) and needs a bridge to r; nothing in the per se vocabulary excludes infinite descent without the groundedness premise (step 4 below) |
| Complete existential dependence | Exactly the closure clause of CCR; a root anywhere in the inventory does not help an unrelated cone (`RosterOnlyControl`, control 4) |
| Circular grounding | Unrooted circuits violate CCR (#1871 circle, control 3); rooted circuits satisfy it |
| Infinite regress | Rootless infinite components violate CCR (control 2, a bare successor relation); root-backed infinite descents satisfy it (control 1) |
| Holistic constitution | Accepts C1 when the whole is an unreceived bearer supplying the parts; denies it only if the whole's actuality is itself received from the parts (then it is a member of a rootless loop, control 3) or is a bearerless fact |

### The strongest positive argument, reconstructed

1. *Reception.* x's actuality is received when a distinct actual bearer is a
   cause of its esse (definition e7aa4529; q3a4 first proof: essential
   principles alone do not suffice for a distinct esse).
2. *Instrumental transmission.* A received bearer contributes to another's
   esse only by exercising the actuality it has received; its operation
   presupposes that actuality (ST I q.45 a.5: instruments dispose a presupposed
   subject; q.104 a.2 grants real, even per se, creaturely preservation).
   Derivative contributions are real, but each passes on actuality it has.
3. *Completeness.* In a complete wholly received system every contribution to
   any member's esse is such a transmission, since every supplier is inside.
4. *Groundedness of received actuality.* Transmission alone does not account
   for actuality: an attribution "has actuality by reception" is satisfied only
   if the givings reach a giver whose actuality is not received.
5. Hence a complete system with actuality contains an unreceived member (CCR).

Steps 1–3 are well supported and are accepted by the strongest rival, which
keeps real derivative efficacy; for that reason they give C1 no advantage over
¬C1. Step 4 carries the whole weight, and it is C1 in other words. It is the
same primitive as the inductive `DerivativeJointPower.Supply` standard of the
earlier section. The argument's work is to **motivate** step 4, not to derive
it. Three motivations, each with its recorded objection:

- **Mode of having.** A received act is had *from another*; if every having in
  a complete system is from another, no having in it is a having *of itself*,
  so the system contains transmitted actuality with no origin. The usual
  illustration is an endless chain of borrowers, which accounts for every loan
  and for no money. *Objection:* loans transfer a conserved stock and giving
  esse need not deplete the giver, so the analogy fails. *Reply:* the
  disanalogy defeats a conservation reading, which the argument does not need;
  what it needs is that each giving presupposes the giver's having. Whether a
  having can be wholly constituted by an endless series of such presupposed
  havings is then step 4 again. This motivation is a direct conceptual
  judgment, not a theorem, and it is the main ground of the judgment below.
- **Selection.** Within the activation-law model of `Logic.RegressDomains`, a
  purely transmitting law is also satisfied by the all-absent assignment (lfp
  empty, gfp full; #1878's `emptyFixedOfEntirelyBorrowed`, merged). So the
  regress's own law fits the actual and the empty pattern alike. *Parity:* a
  foundation with a merely contingent source has the same gap, since its law is
  satisfied with the source inactive. The point discriminates only for a source
  active in every admissible state, a C2 commitment (below).
- **Explanatory unity** (Cameron §4, recorded in #1724): one basis explains
  all members, against an endless supply of separate explanations. Defeasible,
  and also available to a plural foundationalist.

### Does C1 follow from more basic commitments? (direction 8)

Two derivations were tried; the outcome is precise.

**(a) Plural non-circularity is C1 re-presented.** "No wholly received
complete plurality is the complete joint cause of its own esse", with joint
causation read distributively (each member caused by a member). Restricted to
complete (closed) pluralities, it says that no such plurality is nonempty,
which is CCR itself. Dropping completeness ("no plurality each of whose members
is caused by a member") excludes rooted cycles and root-backed infinite
descents. Classically that is the minimal-element form of well-foundedness, a
standard characterization not formalized here; well-foundedness implies CCR
(`closedOfWF`, 044974e5) and is strictly stronger, and CCR rightly does not
require it. Local anti-self-causation does not supply the restricted
principle: the Hume–Edwards control satisfies no self-causation **and** loop
freedom while being a complete wholly received system. So the plural principle
adds no evidence beyond CCR. The collective self-causation analogy behind it
("the plurality would give itself what it has only by receiving") is a
legitimate motivation for C1, but as an illustration of step 4, not as a
separate premise.

**(b) The totality-cause route is a stronger, verified alternative.** New
vocabulary `TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause`, results in
`TruthCore/Results/Aquinas/DeEnte/AggregateEsseCause/`, all zero-axiom,
Comparator- and NanoDa-checked:

- **A** (05b15c98): if anything is received, the *totality* of received actual
  bearers has an actual cause of its esse (`TotalityCause`, an explicit
  primitive, definition a95ed85b, collective sense TOTALITY_CAUSE_1 of
  disambiguation 197f0097).
- **B** (6c0282c0): a cause of that totality causes the esse of each received
  member, including members it reaches only through intermediaries (whole to
  members; the #1109 spacetime analogue is `CausingWholeCausesParts`, a
  different vocabulary, not identified with it).
- **No self-causation of esse** (b62a64ab, sourced: De ente c.3, claim
  85857e47).
- `commonOfAggregate` (result a89fd4df): A, B and no self-causation give
  **one uncaused actual bearer that is a distinct actual cause of every
  received bearer** (9ff2814e). Proof: the totality cause would cause itself if
  it were received.
- `closedOfCommon` (result 50dda707): 9ff2814e gives CCR. Relation 37885377
  registers the strength order.
- `maximalCausesOfCommon` (result 0773fa6c): 9ff2814e with coverage 457698e4,
  identity uniqueness a576300f, causal ascent cffad050 and excluded middle gives
  the fixed-esse maximum principle **da09703b** consumed by the GOD_4 existence
  bundle, without CCR, population or the open composition premise b4987085 that
  the existing route f4df2153 needs. The composition-type content is moved,
  not removed: B already requires the totality cause to cause members it reaches
  only through intermediaries.
- `controls` (result 69ed38fb, statement 7b9bac8e): seven exact
  interpretations. (1) A, B, no self-causation, coverage, uniqueness and the
  common cause hold with an infinite descending chain: the bundle is
  satisfiable without well-foundedness. (2) Hume–Edwards regress on a bare
  successor relation: no predicate whatever satisfies both A and B; the
  distributive reading TOTALITY_CAUSE_2 (`DistributiveTotalityCause`)
  satisfies A and fails B; no self-causation, coverage, uniqueness and loop
  freedom hold; CCR fails. (3) Internal totality causes in a loop: B fails.
  (4) An actual uncaused totality cause that supplies no member: B fails, CCR
  fails. (5) A self-causing totality cause: no self-causation fails. (6) and
  (7) CCR without a common cause; (7) has two independent identity roots, no
  self-causation and a transitively closed relation, so its failure does not
  depend on reading `CausesIn` as immediate.
- Helper `jointIffCommonCause` (unregistered): some predicate satisfies A and B
  exactly when, if anything is received, one actual bearer causes every
  received bearer's esse.

~~~mermaid
flowchart TD
  A["A: received totality has an actual cause, 05b15c98"] --> C
  B["B: totality cause causes each received member, 6c0282c0"] --> C
  S["No self-causation of esse, b62a64ab (De ente c.3)"] --> C
  C["One uncaused cause of every received bearer, 9ff2814e"] --> CCR["CCR / C1-bearer, 20babef7"]
  C --> M["Maximal esse causality, da09703b"]
  COV["Coverage 457698e4"] --> M
  ONE["Identity uniqueness a576300f"] --> M
  ASC["Causal ascent cffad050, EM ee4ab504"] --> M
  CCR --> CS["Existing common source c35b1a5c via c6d92415"]
  CS --> M2["Existing f4df2153 also needs composition b4987085"]
  M2 --> M
  M --> G["GOD_4 existence bundle: eleven further inputs, unchanged"]
~~~

**What (b) shows.** Because `TotalityCause` is constrained only by A and B,
the primitive is eliminable: the substantive content is the **joint** claim
that one actual bearer causes every received bearer's esse. Which premise
carries it depends on the reading (disambiguation 197f0097). On the
collective reading TOTALITY_CAUSE_1, B follows if the totality's being consists of
its members' being (causing it is causing them, perhaps through intermediaries),
and A carries the
claim; the Hume–Edwards view denies A, holding that a totality whose members
are all caused needs no cause beyond its members' causes. On the distributive
reading TOTALITY_CAUSE_2, A is classically trivial and B carries the claim; control 2
shows A true and B false there. Either way the joint claim, together with no
self-causation, is **strictly stronger than C1**: control 7 is a plural
foundationalism (several independent underived sources) that keeps C1,
coverage and no self-causation and rejects the joint claim. The route is
therefore a support option with its own premises, which adds unity of the
cause of received being; it is not independent evidence for CCR beyond the
warrant of that joint claim. The Hume–Edwards denial is ¬C1's core defence, but
it is also available to a plural foundationalist who accepts C1.

**Verdict on direction 8.** C1 does not follow from more basic accepted
commitments about explanation, potency or sustaining without a premise at
least as strong. The plural principle restates it; the totality principle
strengthens it. For sustaining and per se order the key premise of the
instrumental argument (derived power needs a non-derived source) is step 4
again, the inductive-supply primitive of `DerivativeJointPower`. Control 2 and
`DerivativeJointPower.SourceFreeControl` show only that the typed fragments
are consistent with its denial; they carry no per se, present or power
typing and are not evidence that a typed per se order could lack a source.
C1 is therefore kept as a **candidate primitive with recorded warrant** and its
direct-assumption option, with the totality route as a stronger alternative
bundle.

### The strongest account of ¬C1

**Positive account.** Actual bearers b₀, b₁, …; each bₙ's esse is presently
and per se given by bₙ₊₁. Giving is irreflexive and loop-free; every member
is actual, has distinct esse and contributes real efficacy. The totality's
actuality is the conjunction of the members' actuality, and its explanation is
the conjunction of their explanations (the Hume–Edwards / `MemberLift` reading
of #751). Control 2 checks the typed part of this account (actuality,
distinct esse, coverage, identity uniqueness, no self-causation, loop freedom)
jointly with the failure of CCR and of every A-and-B predicate. "Presently",
"per se" and "real efficacy" are the intended reading only.

**What it explains.** Each member's actuality, given another member's; all
relations of supply; the pattern. **What it does not.** Why the pattern is
filled rather than empty; its own law is also satisfied with nothing active.
It answers either that this is not a further explanandum (Hume–Edwards) or
that the obtaining is a primitive fact. A foundation with a merely contingent
source owes the same answer (see Selection above); only a source active in
every admissible state escapes it.

**Strongest warrant for ¬C1.** Structural consistency of infinite orders of
supply (control 2; the existing infinite controls); parsimony (no further
being); no need for a step from members to the totality; the accepted
coherence of infinite accidental series; and the general legitimacy of
primitive stopping points.

**The disputed point, not an independent cost.** On ¬C1, attributions of
received actuality never reach an unreceived giver: received actuality is
satisfied coinductively (gfp) rather than inductively (lfp). This is the
denial of step 4 restated, so it is recorded as the point at issue, not as a
cost. Likewise the question whether "received" applies to the complete
totality turns on the sense: in TOTALITY_CAUSE_2 the Hume–Edwards theorist
grants that the totality is caused (by its members' causes); in
TOTALITY_CAUSE_1 he denies it. No argument is given here that the collective
sense applies; the mode-of-having motivation is the proponent's reason for
thinking it does.

**Circular variant.** In the per se vocabulary loops are excluded by
`noPerSeCausalLoop`, which needs a bridge to r; on the bare relation they are
coherent (#1871 circle, control 3). A loop explains mutual dependence of
members whose actuality is presupposed, not the actuality of the loop.

### C1 with C2 and C3 (direction 9)

C2 and C3 are not defined in the repository or in the request. They are
read here as the next two commitments the request names: **C2**, the
underived source exists necessarily; **C3**, the source is one.

- **C1 does not give C2.** CCR, the common cause and every control above are
  modality-free; an actual root is not an all-world underived being. The
  existing necessity steps (45988f36; c66eead8 and 8e3b89c9 via attempt
  [a1b799fe](../../corpus/attempts/a1b799fe-f75c-4e3e-994a-f4bb834f3ac7.json)) and the open root-to-ground bridge cb1cdea9 of #1616 remain
  separate.
- **C2 strengthens one warrant for C1, not the other.** Within the
  `RegressDomains` activation-law model, the selection point discriminates
  foundation from regress only if the source is active in every admissible
  state; a merely contingent root admits the empty assignment with the root
  inactive, which restores parity (#751 table: `ground` answers the
  total-history question without necessitating it). So the contrastive warrant
  supports C1 and C2 **as a package**. The mode-of-having warrant supports C1
  alone. Neither counts twice.
- **C3 has two distinct routes.** CCR with coverage 457698e4, identity
  uniqueness a576300f, population 78cffb8e and excluded middle gives the
  finite-path common source c35b1a5c (existing). The A-and-B route gives a
  direct common cause of all received being without a576300f (9ff2814e), but
  places unity in the joint claim. Neither restates the other: control 6 has
  a576300f and the finite-path source without the direct common cause; control
  7 lacks both. Uniqueness of underived bearers is still not derived by the
  totality route: a further idle uncaused bearer is not excluded by A, B or no
  self-causation.
- **Redundancy check.** Of the routes checked: the Scott/Gödel modal route
  (13be7bbd) reaches a necessary being with no premise about actual derivative
  beings, so it does not connect that being to them; the underived
  necessary-concretum routes (8337b13f, bb9fdc32) do connect, through their own
  support-coverage premises in a grounding vocabulary, which play C1's role in
  a different relation and are not reductions of CCR. C1 (or the totality
  route) is what makes the De ente necessity, unity and naming bridges concern
  the source of *these* beings.

### Underived source to necessary existence, unity and GOD_4: exposed dependencies

From C1-bearer: CCR 20babef7 + coverage 457698e4 + excluded middle ee4ab504
give an identity source (109e22e1); + uniqueness a576300f + population
78cffb8e give the common source c35b1a5c (c6d92415); + composition b4987085 +
ascent cffad050 give da09703b (f4df2153). Alternatively A + B + b62a64ab +
457698e4 + a576300f + cffad050 + ee4ab504 give da09703b (0773fa6c). The
GOD_4 consumer then needs eleven further inputs (de-ente note, "Carrying n into
the God consumer"), including the open cause-to-concrete-ground bridge
cb1cdea9 that #1616 tests. Necessity needs the same-witness modal steps
(45988f36; c66eead8 and 8e3b89c9 via attempt a1b799fe). None of these
bridges is assumed or discharged here.

### Provisional assessment

- **C1-bearer, scope: complete systems under one fixed actual-esse-cause
  relation, read as exhaustive per se productive supply.** *Accept
  provisionally as a candidate primitive with recorded warrant; modestly
  favored.* The favourable judgment rests mainly on the mode-of-having
  judgment (step 4's motivation). The selection asymmetry adds weight only
  together with C2; explanatory unity is defeasible and shared with plural
  foundations; the instrumental premises are accepted by both sides and add
  nothing comparative. C1-bearer is logically weaker than well-foundedness and
  than the A-and-B claim with no self-causation, and permits infinite series
  and rooted cycles.
- **C1-bearer, unrestricted tenseless mode-unspecified reading.**
  *Underdetermined*: temporal-origin and non-efficient readings of r are not
  shown to be supply (#1616 inertia, F2), and the cause-to-ground bridge
  remains open.
- **¬C1.** Coherent and not refuted. It survives by denying that a complete
  totality of received actuality is caused in the collective sense, or by
  taking a bearerless obtaining fact as primitive.
- **A-and-B with no self-causation (totality route).** A distinct, stronger
  option that adds unity of
  the cause of received being; its warrant is no greater than C1's and plural
  foundationalism rejects it. Useful because it supports da09703b without CCR
  or the composition premise (whose content moves into B).
- **Formal establishment: none.** No premise is discharged; the computed
  frontier delta adds three verified support alternatives and lists A and B as
  bare premises.

**The remaining disagreement, stated exactly.** Is "has actuality by
reception" a grounded property, whose attributions must reach an unreceived
giver (least fixed point), or can it be satisfied coinductively by an endless
or circular system of givers (greatest fixed point)? Equivalently: is a
complete totality of received actuality caused in the collective sense, or
only distributively? The structural tests performed (coverage, no
self-causation, loop freedom, whole to members, identity uniqueness,
satisfiability without well-foundedness) leave both answers consistent. What
remains is explanatory: whether transmission without origin accounts for
actuality, and whether a bearerless primitive fact is as good a stopping point
as an unreceived act.

**Reopen for either side on:** (i) a positive argument that the collective
sense applies to a complete totality of received actuality, or a positive
argument that it does not, beyond the bare Hume–Edwards denial; (ii) a positive
account of how a bearerless fact makes bearers actual rather than describing
their pattern, or a demonstration that an unreceived act faces the same
objection; (iii) a same-relation counterexample to B or to no self-causation;
(iv) a defended per se productive reading of every r-edge, or a typed per se
model without a source that does not simply deny step 4 (either would change
the underdetermined scope); (v) a typed mode-specific variant that changes
control 2's interpretation. Another presentation of a regress, a loop or a
non-circularity principle restricted to complete pluralities is a reuse case,
not a reopening.

**Self-sweep (claim against type).** `ReceivedActual` is double negated, so
"has a cause" in prose means "is not uncaused" without excluded middle.
`TotalityCause` is a parameter constrained only by A and B: no externality,
uniqueness or irreflexivity is assumed, controls 3–5 use that freedom, and
`jointIffCommonCause` shows it is eliminable. `CommonUncausedCauseOfReceived` is
conditional on some received bearer and asserts no uniqueness of uncaused
bearers or esse-essence identity; it neither implies nor is implied by
c35b1a5c. `maximalCausesOfCommon` lists every hypothesis as a premise,
including excluded middle; the other three results use no excluded middle.
Control 6's failure is relative to the given edges, as its docstring states;
control 7's is not. "Per se" and "present" in prose describe the intended
reading only; no Lean type carries time, mode or world. No source claim is
added; Aquinas, Cameron and Bevan are cited through existing #1724 records.

**Review.** Independent semantic challenge and re-check (2026-11-23): formal
core confirmed (types, proofs, control conjuncts, cited IDs, no transcription,
no sense mixing); all prose and disambiguation findings repaired in this PR.

## State-indexed actual holism: what global selection buys (#1724, #1616; 2026-11-23)

**Scope and novelty.** This test follows merged #1871 and the fixed-profile
selection results of merged #1878. It retains the q.3 a.4 `ActualEsseCause`
direction and guards and lets **`InAct` covary with a candidate Boolean
assignment**. It is one structural instance of #1878's borrowing framework
(see below), not a new kind of selection result. It does not re-prove the
Hume–Edwards/aggregate A-and-B results of PR #1882. The question actually
encoded is narrow: for a fixed Boolean assignment of two bearers, the
state-indexed reciprocal-support equation and an added **nonemptiness**
condition, does uniqueness among the admitted assignments force an r-root?
No whole, organization, law or modality is encoded. For the mode-unspecified
r the answer is **no**, and the nonemptiness condition does the selection
work. The motivating question, whether a necessary or globally admitted
actual whole can be source-free in r and still be uniquely selected, is not
answered by this model and remains **OPEN**. At the per se productive scope
the two-cycle is excluded once the priority bridge is supplied, and the
holist's admission there must be stronger than nonemptiness (see "Scope of
the control" below).

### The six things that must not be identified

For a fixed pair of bearer identities, say `u = false` and `v = true`,
the new `circleAtState state` retains the existing
`sourceFreeFiniteCircle` cause matrix and essence/esse assignments but
sets `InAct x esse := state x`. The same `ActualEsseCause` guards now
recognize **only** suppliers and recipients actually present *in that
candidate state*. No profile-to-world interpretation is assumed.

| Level | Meaning in this test | What supplies it, if anything |
| --- | --- | --- |
| Formal consistency | A Boolean state and its guarded r-edges satisfy an equation | Exact Lean control; no ontic conclusion |
| Global uniqueness | Every **admitted populated** state has both bearers | Reciprocal r-constraint **plus** population admission |
| Metaphysical admissibility | The whole and its law are genuinely possible or necessary, rather than stipulatively admitted | **OPEN** modal/constitution interpretation and sufficient warrant |
| Actual instantiation | A real configured whole `W` and its members `u,v` obtain | In a strong holism, `W` obtains necessarily or primitively; this is **not** proved by Lean |
| Productive existential giving | An exercised real power brings about or preserves a recipient's esse | Requires bearer, exercise, causal priority and exact-r interpretation, none encoded by the Boolean edges |
| Complete existential explanation | Why `W` (not merely its members conditional on `W`) actually obtains | Necessity/constitutive sufficiency or a primitive obtaining fact must be defended against a source-based stopping point |

The new, **unregistered Lean helper** `StateIndexedHolisticCircleControl`
has four consequential parts. (1) The all-absent configuration is a fixed
point with no actual suppliers or recipients. (2) The all-present
configuration is fixed and satisfies `HolisticCircleAdmissible`, which is
*defined for the structural test* as fixedness **and nonemptiness**.
(3) Every admitted state has both bearers: uniqueness is pointwise, **only
within that restricted class**. (4) In the all-present profile each bearer
has an actual incoming r-cause and there exists **no r-uncaused bearer**.
The result is constructive on a two-element carrier and makes no appeal to
well-foundedness, global intuition or a hidden positive seed. The prior
control already showed that a fixed profile may contain a rootless two-cycle.

**Relation to #1878.** The control is one structural instance of #1878's
borrowing framework. With `p := sourceFreeFiniteCircle` and
`circleRule s x := ∃ c, ActualEsseCause (circleAtState s) c x`,
`circleRule` is an `EntirelyBorrowedRule p`, and `CircleStateFixed s` is
`SupplierStateFixed circleRule s` with the biconditional flipped
(`circleRuleEntirelyBorrowed`, `circleStateFixedIff`). Part (1) is therefore
an instance of `emptyFixedOfEntirelyBorrowed`
(`emptyCircleStateFixedOfBorrowing`): varying `InAct` with the state
**preserves** the empty fixed point. Only the populated-uniqueness
restriction defeats a root, and #1878's self-sweep already named that
restriction. Here a state is not a world and `CausesIn` is not varied, so
#1878's open bridge (reading states as admissible total-existence
alternatives, with `CausesIn` varied as well) remains **open**.

**What the theorem does NOT say.** The formal `state` is still not a
metaphysically accessible world. `HolisticCircleAdmissible` introduces
nonemptiness as a stipulated global admission condition; its constructor
does not produce or explain an actual bearer. The `CausesIn` edge remains
tenseless and mode-unspecified, with no real power exercise or constitutive
identity fact. The empty state is a fixed mathematical alternative, but
**not an admitted alternative** to the holist's strong modal law. Therefore
this is a **structural counterinterpretation** to the inference
“unique globally admitted populated configuration entails an r-root,”
**not** a realization of genuinely mutual existential production.
Restoring exercised powers, a concrete organizing whole, full-ground
sufficiency and cross-world identity is the live semantic challenge.

**Scope of the control: mode-unspecified r only.** The witness is a
two-element cycle. The row "Genuine mutual productive esse-causation" in the
table below, and `noPerSeCausalLoop`, exclude it at the per se productive
scope once the bridge from `ActualEsseCause` to strict productive priority is
supplied. The acyclic analogue does not keep the nonempty-admission price.
The unregistered, zero-axiom helper `StateIndexedTailControl` checks this: on
`Nat` with `CausesIn c x := c = x + 1` and `InAct` set by the state, every
tail `{n | k ≤ n}` satisfies the same reciprocal-support equation, is
nonempty and has no r-root, and the tails from `0` and from `1` differ
(two distinct admitted states suffice). Nonemptiness
therefore does not select a unique admitted state there. A holist who wants
uniqueness needs a stronger admission, such as maximality (the greatest fixed
point, all of `Nat`) or a named member. At the per se productive scope the
holist's admission price is **OPEN and stronger than nonemptiness**. The tail
control is still mode-unspecified: it shows the selection logic, not that a
per se productive infinite order is possible.

### The strongest source-free holistic proposal

Specify real constituents `u,v`, real capacities `P_u,P_v`, actual
exercises `E_u,E_v`, a concrete organization `A`, and the obtaining of
their whole `W`. A respectable holist need not claim that `E_u` makes
`u` exist *before* `u` exists. Instead the proposed order is:

1. `W` obtains as a metaphysically **necessary concrete whole**, or as
   an ontically primitive contingent fact; its internal articulation
   determines `u,v,A`, their powers and their exercised roles.
2. The organization is **constitutive** of the member configuration;
   `u,v` are derivative with respect to `W` or to the whole-fact, not
   necessarily mutually **efficiently producing** one another.
3. The global law selects exactly this joint configuration. A derived
   member's dependence need not trace a temporally first event. Local
   feedback can be causal, functional or nonproductive; explanatory
   priority is from `W` to members on a priority-monist account.
4. If `W` is unreceived and its relevant whole-to-member relation is
   genuine productive `ActualEsseCause`, this is no longer an
   **entirely r-derivative** world: it offers an underived concrete
   candidate, although its connection to every supplier cone, necessity
   and God attributes remain separate. If `W` is **not** an actual
   member or supplier in the r-domain, the holist contests exactly the
   bearer/r-relevance bridge, not a proved r-theorem.

This is a **reconstructed rival**, not a claim that the finite Lean model
implements `W,A,P_u,P_v,E_u,E_v`. It is stronger than a cycle of two arrows:
there is an ontic whole, organizing constraints, constituent powers and a
positive explanation of co-obtaining. [Schaffer's priority monism](https://doi.org/10.1215/00318108-2009-025)
is an important *different* comparison: it regards the cosmos as basic and
the parts as derivative, so it **accepts a basic concrete whole** in its
grounding order; it is not evidence for a world with no underived
ground at all. The [Stanford Encyclopedia's grounding survey](https://plato.stanford.edu/entries/grounding/#WellFoun)
documents the actual disagreement over grounding well-foundedness.
Neither a literature label nor structural consistency is a metaphysical
warrant for actual non-well-founded **existential production**.

**Law types and their explanatory yield.** A *descriptive* law classifies
a configuration already obtained; a *constitutive* law specifies
what it is for this whole to have its members; a *governing* law
purports to restrict genuinely possible reality; a *productive* law
must be instantiated in actual powers and their exercises. A unique
mathematical solution under a descriptive law need not obtain. A law
understood as **metaphysically necessary and existentially
instantiating** is a much stronger claim: it may indeed explain why
the whole must obtain, but its modal force and existential import
are precisely the substantive posit, not consequences of numerical
uniqueness. A nonnecessitating global explanation can instead select
this actual state by a primitive, law-permitted obtaining fact. That is
a legitimate positive *stopping proposal*, albeit not a complete
further explanation of the selecting fact under a total-existence norm.

### Productive priority and the weaker-than-WF target

The strongest positive source argument begins with the **operation
presupposition**: an exercised productive power requires its already
actual bearer. A thing's operation cannot be the earlier ontological
producer of the existence required for that very operation **under
the same asymmetric, transitive productive-priority relation**.
Existing `ExistentialSelfActualization` and
`noPerSeCausalLoop` results capture the contradiction of circular
*productive* priority on those explicit premises. They do not show
that all constitutive feedback is impossible. The operation presupposition
is shared with the strongest rival, which keeps real derivative efficacy
(#1882's C1 step 2). Given the bridge to strict productive priority it
excludes only finite productive loops, so it does not by itself favor the
source. Conversely, strict
asymmetry and irreflexivity can exclude finite reciprocal production
while leaving an infinite `n+1 → n` order: neither gives a root
without a further actual-supply sufficiency condition.

The more promising, **narrow** principle to assess is not unrestricted
well-foundedness of every cause. It is:

> A complete cone of *genuinely exercised existential givers* cannot
> furnish as its entire productive input only the already actual
> bearers whose actuality the cone is supposed to produce.

Its positive support is the groundedness, or mode-of-having, judgment on
received actuality (#1882's C1 step 4): an attribution "has actuality by
reception" is satisfied only if the givings reach a giver whose actuality
is not received. This is the complete-cone principle itself, held as a
direct conceptual judgment rather than derived from a further premise. The
instrument-versus-absolute-being distinction in *ST* I q.45 a.5 supports
only the operation presupposition (C1 step 2: an instrument's operation
presupposes its own received actuality), with the restriction in *ST* I
q.104 a.2 that created causes can really preserve. The rival accepts both,
so they do not discriminate. The De ente received/unreceived esse
distinction supplies the candidate mode-of-having explanation for the
source. Applying the principle collectively to **every** supplier-closed
`ActualEsseCause` cone is still OPEN: it must include every relevant productive supplier,
exclude merely exemplary/final causal roles, and justify the
collective inference, not merely each member's presupposition.
PR #1882's A/B totality-cause route makes a stronger *collective
cause to member* premise explicit; it is not borrowed into the present
model. The untyped q3a4 r by itself does not carry exercises,
metaphysical priority, temporal concurrence or completeness.

### Positive underived-source account, held to the same standard

The source-based alternative posits an **actual** bearer `n` whose
esse is unreceived *in the relevant respect*, whose productive
activity does not require an upstream grant of its own actuality,
and whose genuine giving supplies derivative bearers. This is not
self-creation. Its positive explanatory work, if the metaphysical
picture is correct, is that the source **possesses the actuality
used by its power without borrowing that actuality from its effects**.
Received powers can remain genuine contributing causes. The
claim that `n` has no further esse-source is supported by an
act/participation/essence–esse account, not by labeling `n`
“uncaused.” If bare r-rootedness alone is the description, a brute
r-root is no more self-explanatory than a brute actual whole.

In the existing certified graph the further route is:
`20babef7` (each local supplier cone reaches an r-root) with
`457698e4`, `a576300f`, `78cffb8e`, `ee4ab504` →
`c6d92415` → `c35b1a5c` (same actual source).
Necessity, pure actuality, actual concrete grounding, subsistent
esse, simplicity and GOD_4 require **separate bridges and identical
witness/sense checks**. A priority-monist concrete cosmos may accept
the local-bearer foundation and reject those later identifications;
a brute law without an actual concrete bearer does not satisfy
the bearer interface merely by being necessary.

The comparison is symmetric: **Why is this primitive admissible,
and what explains the target?** A necessary, intrinsically sufficient
source offers a mode-of-having explanation; a necessarily
instantiated, constitutively fundamental whole may offer the **same
kind** of modal stopping explanation, while disputing a separate
productive giver. A brute source and a brute whole both stop without
further necessitating explanation. Calling the whole abstract,
or the source “necessary,” without defending those descriptions is
not a discriminating victory.

### Inertia, same-bearer identity and explanatory scope

The serious historical alternative has one persisting bearer `x`,
actual earlier existence `E(x,t_0)`, a persistence law and absence
of relevant destroyers. It can explain `E(x,t_1)` without a
simultaneously giving distinct bearer at `t_1`. The positive
law-based and transtemporal inertia options are analyst formulations here.
The existential-inertia rival is articulated in Schmid's pinned reply
(passage `SCHMID-INERTIA-REPLY-3-ARTICLE`) and analysed in
[sustaining-vs-existential-inertia.md](sustaining-vs-existential-inertia.md);
this section does not attribute those specific variants to that passage.
No theorem here converts `t_0,t_1` to the Kripke-world parameter of
`cb1cdea9`; `ActualEsseCause` remains world-free. In a
beginningless history, the past-law explanation may have no first
dated anchor while the obtaining of the **entire** actual history is
taken as primitive, necessary or explained by some distinct
global basis. That is a coherent rival explanatory shape, not a
checked instance of the full #1614 bundle. The remaining #1616
acceptance obligations (full-bundle inertia countermodel, sense
3→5, non-efficient F2 interpretation) remain open.

### Connected comparative argument graph

~~~mermaid
flowchart TD
  O["Actual whole W with u, v, A and exercised powers"] --> T{"What explains W obtaining?"}
  T --> HN["Necessary constitutive/governing whole"]
  T --> HB["Primitive global obtaining fact"]
  T --> S["Unreceived actual productive source n"]
  HN --> HL["OPEN: necessary modal admissibility + existential import"]
  HB --> HE["Local constitution; ultimate W fact remains primitive"]
  S --> SP["OPEN: intrinsic sufficiency + real productive source-to-member bridge"]
  FIX["State-indexed r circle (instance of #1878 borrowing): empty and full fixed"] --> POP["Add nonempty admission"]
  POP --> UNIQUE["Only one admitted state, all members r-caused"]
  UNIQUE --> LIMIT["Mode-unspecified r only; NOT metaphysical production"]
  TAIL["Acyclic Nat tail analogue"] --> NOSEL["Nonemptiness does not select; stronger admission OPEN"]
  PER["Exercise presupposes actual bearer (shared with rival) + priority bridge"] --> NOLOOP["No finite productive self-cycle (existing)"]
  NOLOOP --> OPEN["Infinite source-free ancestry still open"]
  NOLOOP --> LIMIT
  GRD["Groundedness / mode-of-having judgment (C1 step 4)"] --> CCR
  SP --> CCR["OPEN: every complete local r supplier cone has a root / 20babef7"]
  CCR --> COMMON["Existing c6d92415 / c35b1a5c plus coverage, uniqueness, population, EM"]
  COMMON --> ATTR["Separate SAME-witness necessary/pure-act/simplicity/GOD_4 bridges"]
  HI["Actual same-bearer past + law"] --> HP["Later persistence; whole-history existence remains separate"]
~~~

| Proposed account | Actuality primitive | Explains members? | Explains the whole? | Status against the same challenge |
| --- | --- | --- | --- | --- |
| Purely borrowed r-activation, no global admission | None beyond conditioned supplier activations | Conditionally, by inputs | Cannot uniquely force a populated solution among all states | **Conditional incompatibility** of unique population with empty-state admission (#1878); no metaphysical impossibility |
| State-indexed, rootless globally selected circle | The populated-order admission itself | Formal reciprocal support only; productive exercise **not** checked | Only if admission has defended modal/ontic force | **Structurally consistent** control for the mode-unspecified r; excluded at the per se productive scope given the priority bridge |
| State-indexed, rootless acyclic tail (`StateIndexedTailControl`) | An admission stronger than nonemptiness (maximality or a named member) | Formal reciprocal support only | Only if that stronger admission has defended force | Nonemptiness **does not select**; the per se holist's admission price is **OPEN** |
| Necessary whole / priority monism | Necessarily or fundamentally obtaining concrete W | Constitutive whole-to-part explanation | Potentially by necessary W, if existential import defensible | **Live**; if W is underived in the selected relation it may satisfy narrowed foundation |
| Brute actual whole and collective constitution | Primitive whole-fact F | Yes, conditional on F and true full-ground sufficiency | F explicitly left primitive | **Coherent under proposal**, explanatorily incomplete under a demand to explain F; not thereby false |
| Genuine mutual productive esse-causation | None, or global actuality fact | Conditional on forbidden/contested productive circle | Needs a theory of exercised reciprocal production | **Inconsistent under shared strict productive priority**, not under arbitrary r assignment |
| Source-backed complete productive order | Intrinsically unreceived actuality of n | Yes, if true productive giving connects n to actual recipients | Offered via n's intrinsic sufficiency | **Modestly favored** on the narrow per se/productive reading, mainly on the groundedness (mode-of-having) judgment; its collective CCR application still open |
| Existential inertia / beginningless law history | Earlier same-bearer actuality and law; possibly whole-history F | Yes for later persistence | Beginningless whole-history obtaining remains a distinct question | **Live** in its own temporal explanandum, not refuted by r-activation |

**Cumulative provisional assessment and revision conditions.** The
increment over #1878 is modest. The control is one structural instance
of #1878's borrowing framework in which the empty candidate also removes
the modelled bearers' actuality guards. That variation preserves the
empty fixed point, and only the populated-uniqueness restriction, already
named in #1878's self-sweep, defeats a root. For the mode-unspecified r,
the price of the rootless two-cycle is an **explicit nonempty global
admission**. At the per se productive scope the cycle is excluded once the
priority bridge is restored, and on the acyclic analogue nonemptiness does
not select uniquely (`StateIndexedTailControl`). There the holist's
admission price is **OPEN and stronger than nonemptiness** (maximality or a
named member). A defender must still explain whether that admission is a
brute actual fact, a necessary concrete whole or a law with existential
import; nothing here shows that it is productive.

**Matched source-side commitment.** Selection is not free for the source
theorist either. Under #1878, a seed-or-borrowed rule has a populated state
unique among *all* states only if it activates some seed in the empty
candidate state; otherwise nothing is active there and the empty state is
fixed (a pencil reading of `SeedOrBorrowedRule`, whose borrowed disjunct
needs an active supplier, and of `uniquePopulatedStateNeedsSeed`). So the
source theorist needs a source active even where no supplier is active,
together with the OPEN `hSeedActive` and `SeedIsActualEsseRoot` bridges.
This is the "Selection" parity recorded in the
[C1 section](#c1-can-an-entirely-derivative-reality-account-for-its-own-actuality-1724-1616-2026-11-23)
above (#1882): the
selection point discriminates foundation from regress only for a source
active in every admissible state, a C2 commitment, and a merely contingent
root restores parity. The holist pays a global admission; the source
theorist pays an every-state-active source.

The comparative case for an underived source remains **modestly favorable
under exhaustive, genuinely productive per se existential supply**. The
rationale is the groundedness, or mode-of-having, judgment on received
actuality: a having that is wholly from another is satisfied only if the
givings reach an unreceived giver (#1882's C1 step 4, the complete-cone
principle). That judgment is a direct conceptual commitment, and its
collective application to every supplier-complete cone is OPEN. The
operation presupposition (an exercised power presupposes its actual
bearer) is shared with the rival. Given the priority bridge it excludes
only finite productive loops, so it does not by itself favor the source.

**Where the whole and the source compete.** That depends on the holist
variant. An unreceived whole `W` that r-supplies the members' esse is itself
an underived r-bearer, so it satisfies CCR (`20babef7`; #1882's C1-bearer,
which priority monism with an unreceived cosmos accepts). Its disagreement
with the source theorist lies later in the graph: at source identification
(`c6d92415` → `c35b1a5c`, with coverage, uniqueness and same-witness checks)
and at necessity, pure actuality and the GOD_4 bridges. Two holist variants
deny CCR, matching #1882's C1 table: a `W` outside the r-bearer domain,
#1882's bearerless variant (at most a C1-anything commitment), and a `W`
whose own actuality is received from the parts, which joins a rootless loop
(#1882 control 3). There the competition is at `20babef7` itself,
between a bearerless primitive obtaining fact and an unreceived act. So **a
necessary or constitutively fundamental whole is not excluded merely by its
lack of r-uncaused *members***, but if it is itself an unreceived r-bearer it
already concedes CCR. The unqualified, mode-unspecified `20babef7` remains
**underdetermined**, and the bearerless holistic alternative is **not
refuted**.

Reopen specifically on: (i) a semantics and evidence for `W,A,P,E`
that realizes full existential constitution while proving no
underived r-bearer is present; (ii) an independent positive warrant
that a global necessary constraint has existential import, rather
than merely selecting an abstract solution; (iii) a real priority/
exercise-to-r bridge that excludes purely derivative production
in **each** supplier-complete cone, including an infinity case
without simply asserting CCR; (iv) a fair comparison of the
necessary whole's and subsistent esse's sufficiency; (v) the
same-bearer #1616 full-bundle inertia test. Reuse #1882's totality
cause, #1878's all-state selection, #1871's exact-r circle, and
the earlier derivative-power, infinite and temporal controls;
repeat no identical proof under a new label.

**Self-sweep and verification boundary.** The new two-bearer
control carries explicit state-varying `InAct`, the same
`CausesIn` and essence/esse fields, nonempty admission,
pointwise uniqueness only among admitted states, all-member
r-coverage and no r-root; its scope is the mode-unspecified r. The
instance lemmas `circleRuleEntirelyBorrowed`, `circleStateFixedIff` and
`emptyCircleStateFixedOfBorrowing` tie it to #1878's framework, and
`StateIndexedTailControl` states the acyclic tail case. No source claim,
statement, inference, registered result, definition, modal frame,
evidence locator or ordinary result binding changes. It asserts no
actual world, exercise, necessary structure or GOD_4 witness. Its Lean
proofs are **unregistered helpers** (no axioms reported by `#print axioms`
on `stateIndexedTail`, `emptyCircleStateFixedOfBorrowing` and
`stateIndexedHolisticCircle`, run locally after a full `lake build` of
`ff6cacc8`),
checked by the kernel build and NanoDa, not audited by Comparator.
Formal root premise effects are intended **none**; the computed
frontier delta must be taken from the PR's actual CI, not inferred
from this prose.


**Computed PR #1883 frontier-diff:** In [corpus-and-lean CI
45141521947](https://github.com/moritzbrantner/formal-logos/actions/runs/45141521947)
on `4baf9ad54f5862b7886090caedeafe51501da3ae`,
`truth frontier-diff --base HEAD^1` reports root-reaching open premises
**550 → 550** (400 bare, 92 supported, 58 stated), verified support
alternatives **578 → 578** (0 added) and lowest expanded-route diagnostic
cost **16 → 16**. This is a computed *no formal premise change*, not an
inference of new warrant from counts. Both Comparator shards, corpus-and-lean
and explorer completed successfully at that revision; Comparator audits only
registered results, not these unregistered helpers. Full-library
verification is separately tracked by PR CI. PR #1878 has meanwhile merged
at `68619469fb7aba91f0818b3f69e52fdb7eb18624`.

**Current scoped assessment:** [`corpus/attempts/6eb9024b-2310-42b1-bc4e-e75031ca2a54.json`](../../corpus/attempts/6eb9024b-2310-42b1-bc4e-e75031ca2a54.json)
owns the #1724 state-indexed holistic-selection interpretation and its
explicit remaining test; it does **not** displace the #1729 source-identity
assessment in attempt [`9f771edb`](../../corpus/attempts/9f771edb-fb20-4426-9ae2-82de322bbe5f.json). This is a standard corpus attempt,
not a duplicate statement, graph path or tracker.

**Independent semantic challenge (2026-11-23, head `e967a177f`).** Two P1
and eight P2 findings, all repaired in this section and the two attempts:
F1, the finite surrogate is scoped to the mode-unspecified r and the per se
admission price is marked OPEN with the acyclic tail control; F2, the
"modestly favored" rationale is the groundedness (mode-of-having) judgment,
with the operation presupposition and *ST* I q.45 a.5 reassigned to the
shared step; F3, the control is described as one instance of #1878's
borrowing framework; F4, the matched source-side selection commitment;
F5, where whole and source compete; F6, the encoded question; F7, the
inertia citation; F8, a code span; F9, the frontier-diff record; F10, the
countermodel's target. The scoped assessment records the review as
`changes_requested` on that head, with repairs pending the coordinator's
re-check; it remains `unpublished`.


## Closed-cone selection without a quantitative transfer ledger (2026-11-25)

**Scope and baseline.** Continue #1724, #1616, #1882, #1964, #1965 and the
still-open #1966, from main `e7073368fcd87fb5be224b6bb7971a55f5316f40`.
This is an analyst reconstruction, not a source attribution or a registered
Lean result. Targets: `20babef7` (all nonempty actual-esse-cause-closed
collections rooted), `5c898d24` (whole actual-concrete roster nontrapping),
`dc397705` (some actual-concrete ground-relative root). These are not
interchangeable: the first fixes q3a4's tenseless `ActualEsseCause`; the
latter two fix `m.grounds w` with actual-concrete endpoint guards.
`ClosedEsseSource.esseCauseGraph` is an exact adapter on its own singleton
index, not a bridge to an independently supplied world-relative profile.
The selected relation must be exhaustive for the productive respect in
question before a relation-relative root is called existentially underived.

### Checkpoint A: delete a whole closed cone rather than the whole roster

The all-state selection result of #1878 shows that an entirely borrowed
activation rule admits the empty state. #1883 already shows why a global
nonemptiness restriction changes that test, and #1964 distinguishes
whole-roster nontrapping from actual-root existence and the stronger
all-collections cut. Do not repeat these results. The new candidate test
asks whether **a particular actual member** is forced by the productive
rules when an unrelated, independently supplied component remains present.
It avoids requiring uniqueness of the whole configuration, finiteness,
strict descent, additive throughput or exclusive receipt use.

Fix a nonempty actual roster A, and the selected actual supplier relation
R on A. For the structural test let F : P(A) -> P(A) be a monotone
activation operator (inclusion order). A is the designated fixed
assignment. Other assignments are mathematical substates, not automatically
possible worlds. Require this **uniform positive-input guard**:

    for every U subset of A and every x in A with an incoming R-edge,
    x in F(U) implies there is c in U with R(c,x).

The guard is one-way, allowing real joint contributions, duplication and
additional enabling conditions. It is stronger than coverage at the
designated actual assignment: it freezes the potential supplier menu to
actual R-edges and constrains every candidate assignment. A genuinely
different producer in another state, or a change in the identity of the
bearer, is not silently excluded in a metaphysical application.

Let C be nonempty, closed under every incoming R-edge, and have no R-root.
Put U = A minus C. If x in C were in F(U), the guard gives a predecessor in
U, but closure puts that predecessor in C. Hence F(U) is a subset of U.

There is a fixed assignment contained in U, including when A and C are
infinite and R has cycles:

1. Let V be the union of all S subset of U with S subset of F(S).
2. Every such S is included in F(V) by monotonicity; therefore V is
   included in F(V).
3. F(V) is included in F(U), hence in U. By monotonicity it is itself
   postfixed, so F(V) is included in V.
4. Thus F(V) = V, and every x in C is absent from V.

This is the greatest fixed substate contained in U. The union is legitimate
on the stipulated powerset; the empty set is postfixed, so this argument
does not presuppose an inhabited survivor. If there is a nonempty postfixed
S0 contained in U, the very same V contains S0 and is populated. One
independently activated outside bearer suffices (its singleton is postfixed).
Neither a relative R-root by itself nor an independently named law entails
this activation condition.

**Consequences to check in Lean.** If an actual x is present in every fixed
assignment in this test (or in every populated fixed assignment when an
outside postfixed witness is given for the tested cone), no R-closed
rootless C containing x is compatible with those assumptions. If that
invariance holds for every actual x against all fixed assignments, every
nonempty closed collection contains a root, classically. With the exact
q3a4 R-adapter this is the proposed conditional application to 20babef7;
with the actual-concrete relation and C=A it gives the whole-roster
nontrapping conclusion, and population plus the appropriate stability/EM
gives dc397705. C=A admits no nonempty outside witness; the populated-only
version does not prove whole-roster nontrapping. These are proposed
deductions, not verified corpus arrows. The direct premise options remain.

The proof is a localized fixed-point bound, related to
`Logic.Regress.Graph` and #1878, not an independent discovery of
fixed-point existence. Its increment is the exact combination of
**closed-cone deletion, monotone greatest survivor, and targeted invariance
among even populated alternatives**. It can diagnose a rootless component
beside an unrelated source, where whole-roster root existence and global
nonemptiness cannot. The candidate invariance is weaker than uniqueness
when other components may vary; it is not furnished by a local causal
explanation or by the mere fact that x actually exists.

**Claim/type self-sweep (informal).** The conclusion is existence of a
fixed mathematical substate omitting C, not possible nonexistence, temporal
destruction, a physically realizable intervention or an actuality-producing
operation. If one asserts only uniqueness among a restricted admissibility
class, the constructed substate must be independently admitted before
using the contradiction. Monotonicity, actual relation closure, uniform
input guard, and invariance are all explicit; the proof does not infer
uniform guards from actual edges. Full collection rootedness needs
invariance for all selected members, not merely one. Independent semantic
challenge and Lean/Comparator/NanoDa/corpus verification are pending;
no new corpus argument or philosophical establishment is claimed.


### Checkpoint B: populated alternatives, guard boundaries and matched accounts

**Strength refinement.** The argument actually needs only monotonicity of
F restricted to subsets of U, once F(U) is included in U and the restricted
operator maps these subsets into U. More generally it suffices to warrant
existence of a fixed substate inside U by an independent method. It does not
need full configuration uniqueness: for a particular C it is enough that
every admissible fixed assignment **intersects C**, even if different members
are present. This is a non-deletion rather than an all-member necessity
standard. Requiring every individual in A to be invariant would amount to
uniqueness on P(A); the weaker per-cone intersection standard need not do so.
Neither standard is automatically true of a contingent actual order.
An independent reason that a relevant cone cannot be entirely absent would
be needed. This route provides a conditional discriminator, not a substitute
for supplier completeness by fiat.

**Controls on identical carriers (analyst models, not metaphysical
interpretations).**

- Independent root plus rootless regress: take A = {s} disjoint union Nat,
  R(n+1,n), with no R-input to s and no edges between s and the chain.
  Let F(U) contain s unconditionally, and n exactly when n+1 belongs to U.
  This is monotone, obeys the uniform guard, and its only fixed states
  are {s} and A: equality of membership at each pair of successive
  natural numbers forces either all or none of Nat. The relation is acyclic,
  and the strict transitive closure is irreflexive. Every natural number
  has an incoming supplier at A; nonempty whole-roster roothood holds but
  CCR fails on the closed Nat cone. Restricting to populated fixed states
  does not repair the explanation of the chain's actuality. The greatest
  fixed point selects A; whether that maximality is ontologically warranted
  is an additional question. This extends the earlier #1883 whole-roster
  tail control by preserving an independently activated outside bearer.
- Root access with optional members: take A={s,a,b}; R contains s->a,
  a->b, b->a. Let s be unconditional, a activated exactly when both s and
  b are active, and b exactly when a is active. The two fixed assignments
  are {s} and A; every nonempty R-closed subset contains s, hence every
  fixed assignment intersects every such subset. This separates cone
  intersection from unique fixedness. The model is not strict productive
  priority, because the a/b edges cycle. Moreover, a has two necessary
  inputs; finding a root path does not certify conjunctive inductive
  supply of a or b. CCR is weaker than the all-input inductive standard.
- Monotonicity cannot be dropped merely because the positive guard
  survives. Let A={s,a,b}, R consist only of a->b and b->a. Define F(A)=A,
  and for every other U let s be activated exactly when s is absent,
  a exactly when b is present, and b exactly when a is present. F obeys
  the uniform guard (s has no incoming edge); A is the unique fixed
  assignment. The complement of C={a,b} contains s, and the restricted
  map swaps empty and {s}; there is no fixed substate there. This is a
  concrete failure of the unqualified no-deletion inference, not a
  counterexample to the monotone theorem. It has a cycle and an
  inhibitory rule, so it does not certify a productive strict-priority
  metaphysics. A necessary global law could select by a different,
  nonmonotone rule, but its existential import would need defense.

**Bounded diagnostic performed here.** Enumerated all 20 monotone Boolean
truth tables on three input bits, combined into 6,859 operators with the
all-present state fixed; paired them with all distinct-edge three-node
supplier menus, retaining the uniform guard. Across 74,088 eligible
operator/relation pairs there were 15,317 nonempty closed rootless-cone
cases. In each case there was a fixed assignment within the cone complement
and the union of all such fixed assignments was itself fixed. In each of
450 cases with a nonempty outside postfixed witness, that union was
populated and contained every such witness. The finite two-cycle with
unconditional s has fixed masks 1 and 7; the nonmonotone control has only
7. These are Python exhaustive diagnostics on finite sets, not a Lean
verification, a model-registry certificate or evidence for modal
admissibility.

Reproduction (bit masks; supplier menus exclude identity edges):
```python
from itertools import product
sub = range(8)
le = lambda a, b: a & b == a
mono = [tuple((m >> u) & 1 for u in sub) for m in range(256)
        if all(not ((m >> u) & 1) or ((m >> v) & 1)
               for u in sub for v in sub if le(u, v))]
menus = [[m for m in sub if not (m & (1 << i))] for i in range(3)]
valid = cases = pop = 0
for fs in product(mono, repeat=3):
    if not all(f[7] for f in fs):
        continue
    f = tuple(sum(g[u] << i for i, g in enumerate(fs)) for u in sub)
    for r in product(*menus):
        if any(r[i] and f[u] & (1 << i) and not u & r[i]
               for u in sub for i in range(3)):
            continue
        valid += 1
        for c in range(1, 8):
            if any(not r[i] or r[i] & ~c
                   for i in range(3) if c & (1 << i)):
                continue
            u = 7 ^ c
            cases += 1
            assert le(f[u], u)
            fixed = [v for v in sub if le(v, u) and f[v] == v]
            assert fixed
            greatest = 0
            for v in fixed:
                greatest |= v
            assert f[greatest] == greatest
            seeds = [v for v in sub if v and le(v, u) and le(v, f[v])]
            if seeds:
                pop += 1
                assert greatest and all(le(v, greatest) for v in seeds)
assert (valid, cases, pop) == (74088, 15317, 450)
```

**Why the guard may deserve positive warrant.** Distinguish (i) the
existential condition on a producer actually exercising a power,
(ii) its specific productive contribution to the recipient, and (iii)
its role in selecting an entire configuration. If x receives esse in
the strict per se productive sense, its real receipt requires at least
one exercised productive input; the input is not just a description of
x. Absence of all such inputs defeats that receipt as such. The
existential guard is thus motivated by what receipt claims to be, rather
than by conservation of a stuff called esse. However, to move from that
local condition to the uniform guard needs a stable recipient identity,
an exhaustive supplier menu across the selected alternatives and no
activation of that recipient by a different mode. In particular the
guard does not say every received contributor is intrinsically inert:
one received power can make a proper contribution. The no-producer
case must not be inferred from having no *recorded* producer.

For monotonicity, adding true antecedents to a sufficient explanation
preserves the entailment, with the same law, conditions and sense of
sufficiency fixed. This is reason to examine a positive-input operator,
not proof that the actual production law is monotone. Adding actual
entities can introduce inhibiting conditions, competing production,
or change what composite is being explained. Constitutive holistic
constraints may also be nonmonotone. Establishing a monotone restricted
operator therefore requires a fixed account of the relevant positive
conditions, not just the assertion that existence is good or that
causation is strict. The nonmonotone control isolates this cost.

**Comparison at the same explanandum:** why the actual obtaining of
the entire selected supplier-complete order is productive or otherwise
adequately grounded, not just which cause accompanies each member.
All accounts get credit for real local contributions if their proposed
relation is independently warranted. None receives credit for actuality
merely because it fits a mathematical configuration.

| Account | Positive account of the same order | Residual obligation under the closed-cone test |
| --- | --- | --- |
| Hume–Edwards/distributive | Each actual member has its own sufficient actual cause; the obtaining of all members is no additional bearer needing a further cause | Explain why conjunction of mutually conditional local explanations is sufficient for actuality at this scope. A law permitting both the populated and unpopulated cone does not distinguish them. Denying a further explanandum is coherent but rejects this broader demand. |
| Beginningless strict regress | Distinct upstream productive contributor for each member; no circular priority | Acyclicity and every local link are compatible with the Nat control. A populated cone needs a global selection/existence account or a justified non-deletion condition; an unrelated root does not help. Infinite descent itself is not the defect. |
| Coinductive/holistic | Actuality belongs to the greatest fixed configuration, or a globally constituted fact whose parts are simultaneous | Greatestness provides a real mathematical selection rule, not yet existential import. Need warrant that maximal admissibility entails actual instantiation, and that the global fact is constitutively sufficient. The gfp account need not be inconsistent, especially if it rejects the independently proposed deletion alternatives. |
| Priority monism / necessary composite whole | A necessarily actual concrete whole grounds its parts; necessary actuality of W may be offered as stopping point | If W is in the exhaustive selected relation as an underived supplier, it is not a counterexample to C1-bearer. Necessity alone does not entail roothood, simplicity, causal production or uniqueness; if W receives its actuality from its parts in the same productive respect, the strict-priority bridge would prohibit reciprocal dependence. Different respects require distinct evidence. |
| Existential inertia | The same actual bearer persists without a new sustaining producer under a law, conditional on earlier actuality | This can be an adequate local persistence explanation; a beginningless actual history still needs its own actuality account at the expanded scope, unless the rival denies that demand or supplies a necessary history/whole. The model does not establish a contemporaneous sustaining cause or origin-to-sustaining bridge (#1616). |
| Underived productive source | An actual source possesses the relevant act non-receptively, and its exercised power accounts for the derived recipients | Must justify source actuality, intrinsic productive sufficiency, same-respect coverage and the source's connection to the whole order. A contingent source plus its law may itself admit an empty alternative: non-deletion selection does not follow from roothood. A necessary source may warrant non-deletion only if its necessity and productive connections are established independently. |

**What denial commits the rival to.** Relative to a fully specified
productive R and nonempty closed actual cone, denial of CCR commits to
a rootless closed cone. It does not alone entail modal arbitrariness,
an epistemic collapse or logical contradiction. Under the uniform
input guard and monotone restricted production, it has a cone-deleted
fixed substate. If an independent outside postfixed assignment exists,
even requiring global population cannot exclude that alternative.
To maintain that the selected cone must obtain, the rival must either
reject admissibility of the deletion, reject the uniform productive
guard (e.g. alternative supplier or a constitutive/nonlocal input),
reject restricted monotonicity/fixed substate existence, or give up
the relevant non-deletion claim. This is a concrete disjunction of
commitments under stated background, not an exhaustive taxonomy of
worldviews. Coinductive maximality is a way of rejecting the selection
standard while conceding the mathematical alternative. Underived-source
accounts face the same existential-import test when they posit a
necessary source. The useful burden is to name and warrant the positive
actualizing/constitutive condition, not simply to posit a ban on the
alternative.

**Receipt and throughput interpretation (#1965/#1966).** Reuse #1965's
finite-throughput ledger: finite summed positive edge throughput, a
nonreturning transfer and receipt coverage at every actually grounded
bearer force a relative root. The fitted-ledger equivalence rules out
retrospective accounting as independent warrant. #1966's open PR uses
finite upstream export ancestry plus injective matching to distinct
receipts, avoiding a numerical magnitude but not the exclusive-use
commitment. Individuating acts or recording provenance does not by
itself imply injectivity: a received pattern or exercised ability can
support several distinct contributions without being consumed. Counting
recipient-specific *obligations* might make receipts distinct in a
particular accounting semantics, but an upstream receipt need not be
recipient-specific, and such bookkeeping does not establish existential
exclusivity. No independent reason found for either finite summed esse
throughput or the required existential receipt matching. The closed-cone
proof uses neither a stock nor a conservation/exclusivity principle;
it introduces the separate all-candidate guard and restricted fixed-point
assumptions rather than solving those ledger bridges.

**Connection to existing routes (no new graph arrow).**

- For q3a4, with the exact R adapter, the all-cone conditional conclusion
  is CCR (20babef7); the existing `c6d92415` derives `c35b1a5c` using
  distinct-esse cause coverage `457698e4`, identity-bearer uniqueness
  `a576300f`, actual population `78cffb8e`, and explicit EM `ee4ab504`.
  A common first identity-bearing source here is connected by finite
  directed ancestry, not automatically an immediate efficient giver.
  Relative roothood alone does not establish its identity with esse.
- For the actual-concrete grounding profile, apply the all-state version
  to C=A. The existing #1964 factorization gives `5c898d24` as the
  population-conditional double-negated root proposition and yields
  `dc397705` with population and root-existence stability. Conversely a
  root entails nontrapping. This equivalence is no fresh support when
  used circularly. The populated-alternatives test diagnoses proper cones,
  and is not itself the whole-roster proof.
- With an actual root selected once, the existing contingent-grounding
  commitment `c71c068c` (every contingent actual concretum has an actual
  concrete ground) and the needed modal logical background exclude its
  contingency and give the same necessary actual root, hence
  `b19ffd92`. **Correction at checkpoint D:** this does NOT yield
  `0bdcf366`, whose support exclusion ranges over every carrier world.
  The latter needs a further all-world transport/underivedness argument,
  e.g. the existing standing-ancestry/coverage routes mapped in
  [conceptual-existence-boundary](conceptual-existence-boundary.md).
  Neither result excludes unmodelled or nonconcrete explanations or other
  necessary beings.
- `ef632140` (unique actual root) uses actual population `56f68b40`,
  `5c898d24`, EM, the actual/esse and distinct cause-to-ground
  interfaces `0436de86`, `cb1cdea9`, cause coverage `457698e4`,
  and identity uniqueness `a576300f`. It is not a consequence of bare
  root existence. Reuse the same-witness route in
  [De ente assessment](de-ente-esse-source-1628.md) and #1964's
  unregistered `deriveFromActualRoot` (with its explicit contingent
  grounding and shared classical-attribute premises; its sense mixing
  registration blocker remains). No potency, simplicity, goodness,
  intellect, will or GOD_4 bridge is discharged here.

**Provisional judgment on exhaustive existential supply.** Retain the prior modest
preference for nonreceived productive availability on an exhaustive
per se existential-supply reading. Both accounts grant actual givers. The rival explains their availability
through their jointly obtaining activity. The modest preference depends on
a further judgment about receipt: when actuality is wholly received, the
givings that account for its availability must reach an unreceived giver.
The contrast between exercising borrowed power and supplying that power
gives this judgment some warrant. Its application to every collection
containing all its members’ suppliers remains open. The present discriminator
improves specificity: even a populated rival with an unrelated
underived root must explain how its rootless cone is selected, if
its own activation account meets the test. It does not increase the
strength of the prior judgment on the unrestricted mode-unspecified
20babef7, nor refute coinductive or necessarily obtaining whole accounts.
The strongest genuine denial remains a globally necessitated or
primitive, bearerless constitutive fact with an independently defended
admissibility/instantiation principle. A fundamental concrete whole
that supplies its parts and itself has no incoming cause in the selected
relation satisfies the narrow root conclusion. The positive source account must meet the same scope
and cannot simply declare its own existence exempt while demanding
a further reason from every rival.

**Checkpoint B handoff (historical).** Work is partial; intended formal premise delta
none. To proceed, use the prepared worker's canonical `truth related`,
`dossier`, `brief`, `novelty`, `semantics` and `context` on the
three targets and exact consumers; check existing fixed-point APIs in
`TruthCore/Logic/Regress.lean` and `ClosedEsseSource`. Formalize the
restricted monotone-operator lemma over the actual subtype and the
guard as an explicit hypothesis, reuse existing adapters, distinguish
local rootlessness from all-subsets borrowing Escape, and freeze a
Challenge only after sense preflight. Certify the populated infinite
control and the nonmonotone control with exact conjuncts and compare
the weakest target non-deletion condition against existing strength
records. Run the worker preflight, applicable Lean build, corpus,
binding, Comparator and NanoDa checks and computed frontier-diff.
Obtain a fresh independent semantic challenger for this final
synthesis (particularly admissibility, rooted but noninductive control,
conditional modality and comparative burden). Local clone fails DNS,
there is no local Lean installation or independent worker facility in
this session, and no installed convention checkout could be inspected
beyond repository guidance fetched via GitHub. Hence this draft remains
unreviewed and no Lean/Comparator/NanoDa or corpus success is claimed.
No attribution, statement, definition, Challenge, Solution, result or
argument records changed by this note. The attempt records the bounded
blocked application without changing the current approved assessment.


### Checkpoint C: what constitutive receipt does and does not warrant

**Question.** Does the very nature of existential receipt justify the uniform
positive-input guard and non-deletion principle, independently of assuming
supplier completeness? Continue on the exact prior draft head
`b0c8d2b37105566fad7206cd5c63806a1b278626`. Reuse #1878's all-candidate
activation test, #1883's state-indexed controls, the [chain-instantiation
controls](chain-instantiation-controls.md) (#704), [direct grounding
audit](direct-grounding-warrant.md) (#1553), and the origin/sustaining
distinction of #1616. This is new analyst reasoning, attribution deferred,
not a registered result or a new sense record.

**Baseline verification correction.** Reran the exact Python enumeration
in checkpoint B: 20 monotone three-bit truth tables, 74,088 eligible
operator/relation pairs, 15,317 closed rootless cone cases, and 450
with a nonempty outside postfixed witness. All assertions passed.
[CI run 45509404715](https://github.com/moritzbrantner/formal-logos/actions/runs/45509404715)
on the preceding head succeeded. The corpus-and-lean job passed corpus,
binding and the computed frontier comparison (`truth frontier-diff
--base HEAD^1`: no change); comparator-plan and comparator-library
succeeded, result shards and NanoDa were skipped. This confirms the
unchanged registered corpus, not the new informal arguments. No independent
semantic review is recorded on that head.

#### 1. Warrant for a receipt guard; do not freeze the actual supplier menu

Distinguish these four different claims, holding the productive respect
and recipient identity fixed.

1. A particular occurring receipt of esse from c is an effect of c's
   exercised productive contribution. An unexercised possible cause or
   a description of the effect is not that occurring receipt. Thus that
   receipt presupposes actual exercise and an actual bearer of the
   productive power, in the selected explanatory mode.
2. The bearer's existence in a candidate realization must be constituted
   by such a receipt, rather than merely having been originated by a cause,
   persisting by inertia, or being independently actual while receiving
   some additional perfection. This is a substantive essential-reception
   premise; it is not obtained from the actuality of one received token.
3. In a selected component C, every relevant realization of that
   constitutive receipt uses some producer belonging to C. This is
   **potential supplier closure at the level of the component**, not the
   assertion that the same particular actual edges must be exercised in
   every candidate realization. It is an open restriction for proper
   components. For the whole candidate domain, no external producer is
   available by construction, but exhaustiveness of that domain is
   still an application premise.
4. That component cannot be absent in the admissible alternatives.
   This is a distinct positive existential import premise, not part of
   the meaning of an actual receipt. A receipt is conditional on an
   actual productive input; this does not assert that it occurs.

(1) has strong direct conceptual warrant in the strictly productive
reading: a reception from an exercised giver without any such giver
is not that reception. This is more specific than material implication
or covariance, and does not invoke a conserved stock or exclusive use.
It does not prove that real existence always has that mode. (2) needs
the origin-to-sustaining/existential-mode argument, rather than
assuming the inertia rival false; (3) needs potential, not merely
actual, completeness. Even all of (1)–(3) supply only a conditional
requirement. The difference between (1) and (2) is crucial for the
q3a4 actual-esse-cause graph; neither term alone implies a
world-relative sustaining relation. A constitutive, non-efficient
holist can accept the conditional existence of its relata while
rejecting the productive interpretation in (1).

#### 2. A weaker deletion test with changing suppliers and nonnecessitating production

Instead of the deterministic monotone F of checkpoint A, use a relation
D(S,T) on candidate input and output assignments S,T subset A. It can
have many outputs, including none. Here D is an abstract admissible
activation constraint, not temporal transition, modal accessibility,
or an ontological explanation relation. A stable assignment satisfies
D(S,S). A is actual in the interpretation being tested and D(A,A) holds.
Set U = A minus C.

A **component-level guard** G is enough:

    D(S,T) and S disjoint from C imply T disjoint from C.

The receipt analysis (1)–(3) motivates G when output occurrence means
the constitutively received actuality and input membership indicates
actual available productive relata. The interpretation requires a
same-respect bridge; input and output cannot be silently treated as
different moments. G does not name a particular predecessor and
allows any eligible producer in C, arbitrary inhibiting conditions,
alternative realizations and nonunique outcomes.

A distinct **retained-realization condition** J at U says:

    some T satisfies D(U,T) and U is a subset of T.

Then D(U,U): G puts T inside U and J puts U inside T. In fact given G,
J at U is equivalent to D(U,U). This exact strength is deliberate:
renaming J is not independent warrant. To make J informative, exhibit
a genuinely jointly sufficient realization of the retained entities
whose actual required inputs and enabling conditions survive deletion.
For example, with deterministic local signed rules, a sufficient
actual rule instance for each retained x can survive if its positive
inputs are retained and its negative conditions stay satisfied.
Negative inhibition elsewhere need not be monotone. For a
nondeterministic law the retained realization witnesses must be
**jointly compatible**, not selected separately for each member.

For C=A, U is empty and J reduces to existence of an allowed output
at the empty input. G forces that output empty. No monotonicity,
global well-foundedness, numerical transmission, receipt injection,
fixed supplier identities or deterministic selection is required.
For proper C, an independently functioning outside component witnesses
J if it jointly realizes every retained member of U. A root elsewhere
may keep just part of U active.
Do not claim this proves modal accessibility of U. If a rival
restricts its admissible configurations, it may reject J or the
interpretation of D(U,U) as a metaphysically admissible alternative.
If it says the necessary actual order is simply one of the stable
assignments, the difference between stability and admissibility is
exactly the remaining positive selection problem.

A useful weaker diagnostic on J: fix nonempty U and suppose every
retained member belongs to at least one allowed output at U. Under G
all these outputs lie in U. For finite U, if the family of outputs
is upward-directed **within the family** (for each two there is an
allowed output containing both), finite induction constructs an
allowed output containing all of U. For infinite U, finite joint
realizability alone does not suffice: the family of all finite
subsets of an infinite U is directed and covers U but omits U itself.
A separate closure/compactness condition on the family suffices
(e.g. if closed in the product topology on {0,1}^U, every basic
neighborhood of the full assignment intersects it, by finite joint
realizability, so the full assignment belongs to it). A genuine
retained simultaneous productive exercise can warrant J directly;
there is no reason to assume general compactness of metaphysical
powers. These are candidate set-theoretic deductions, not Lean or
configuration-registry results.

#### 3. Structural separators: change the supplier and keep the component guard

Take A={s,a,b,c,d} and C={a,b,c,d}. The input/output constraint is
deterministic for this illustration. s activates unconditionally.
a activates from c when both c and d are present (d is an enabling
condition), or from b when c is absent. b activates from a; c and d
activate from b. At A, the selected a-supplier is c, not b. In an
input with only b, a activates through b despite c's absence. Adding
c to that input without d prevents activation of a. Thus the fixed
actual-menu positive guard from A and global monotonicity both fail,
but the component guard holds for every input and the outside
realization {s} remains fixed. All actual C members have incoming
selected suppliers in C. This example allows cycles, is purely a
formal activation interpretation, and does not restore a strict
productive-priority premise. It shows why alternative suppliers
inside C and inhibition need not invalidate this deletion test;
it does not certify any metaphysical entity or productive exercise.

For the nondeterministic join test, let U={p,q}; allowed outputs at U
are exactly {p} and {q}. Each member has an individually admissible
realization but neither outcome includes both; no D(U,U).
This is the failure mechanism for an unjustified exchange of
`forall x, exists realization` with `exists realization, forall x`.
It does not claim no other fixed assignment survives. For infinite
U the finite-subsets family makes the stronger finite-join/whole-join
distinction. These are explicitly surrogate output relations.

**New finite diagnostic, actually run in Python.** Exhausted every
nonempty family of subsets of U for sizes 1, 2 and 3, tested individual
coverage, directedness and full-union membership. At size 3, 218 of
255 families cover every member, but 90 of those omit U. Every
directed covering family (128) contains U. At size 2, 10 covering
families include two failures of joint coverage. The following
reproduces the finite test and varying-supplier control:

```python
for n in range(1, 4):
    U = (1 << n) - 1
    subsets = list(range(U + 1))
    total = covered = fail = directed_covered = 0
    for mask in range(1, 1 << len(subsets)):
        T = [s for s in subsets if mask >> s & 1]
        total += 1
        cov = all(any(t & (1 << i) for t in T) for i in range(n))
        directed = all(any(((a | b) & ~t) == 0 for t in T)
                       for a in T for b in T)
        if cov:
            covered += 1
            fail += U not in T
            if directed:
                directed_covered += 1
                assert U in T
    assert (total, covered, fail, directed_covered) == {
        1: (3, 2, 0, 2), 2: (15, 10, 2, 8),
        3: (255, 218, 90, 128)}[n]

# s=1, a=2, b=4, c=8, d=16
A, U = 31, 1
C = A ^ U
def F(S):
    return (1 | (2 if ((S & 8 and S & 16) or
                       (S & 4 and not S & 8)) else 0)
            | (4 if S & 2 else 0) | (8 if S & 4 else 0)
            | (16 if S & 4 else 0))
assert F(A) == A and F(U) == U
assert all(not (F(S) & C) or S & C for S in range(A + 1))
assert F(4) & 2 and not F(4 | 8) & 2
```

#### 4. Why the non-deletion bridge is not a consequence of receipt

Even exact essential-supplier identity, strict priority and local
sufficiency do not supply positive existential import. On the
existing Nat chain, let every n be present exactly when n+1 is
present, with n+1 the fixed selected supplier of n. These two-way
conditions are stronger than the receipt guard alone. They hold
in the all-present and all-absent assignments. Strict reverse Nat
ancestral priority is irreflexive and transitive. This is reuse of
#704's equation and #1883's controls, not an additional independent
regress theorem.

There is a stronger rival reconstruction worth keeping: select
two universally accessible candidate worlds, with all n present
and the same successor causes in each, but differ in an
irrelevant accidental feature of n=0. Each particular n is
accessibility-necessary; it has the same necessary particular
supplier in both worlds, and all actual bearers have a selected
incoming cause. The selected cause relation is acyclic and all
local two-way presence conditions hold. This stipulated frame
admits no absent chain, although the empty assignment remains a
solution of the conditional local equations outside that frame.
Thus even **necessary particular received bearers** and stable
supplier identity are compatible with a rootless graph in this
structural surrogate. This is not new evidence that such a
necessary concrete order really is metaphysically possible;
its necessity is imposed by the accessible domain and it supplies
no intrinsic existence reason, actual exercise or modal import
for the laws. It defeats the attempted inference solely from the
specified modal and relational conditions. The same warning applies
to asserting necessity of a source without its positive nature.

A useful general scope test does not need an activation operator:
on the fixed candidate domain, every receiver-guarded law of the
form 'for all actual x in C, [arbitrary condition about x]' is true
when no C-member is actual. All source-triggered laws with only
C-member actual-exercise triggers are then vacuous too, even if
the consequent is complex, the laws are nonmonotone, or the
suppliers vary between realizations. Thus a background permitting
absence plus *only* these laws cannot entail C-population.
For a proper C the other, outside-triggered or global clauses
must be checked, not simply discarded; a necessary outside recipient
depending essentially on C can exclude its absence, but this is
not an independent positive origin of C's actuality. An
unconditional existential principle or an independently actual
outside input can break the vacuity. This is a logical import
test, not a theorem that all possible metaphysical explanations
must entail their explananda, nor that an actual causal explanation
is just a universal conditional.

#### 5. The discriminating demand at the actual order (not only modal selection)

The strongest non-deletion premise is not generally defensible:
a contingent derivative order may legitimately be absent. A
nonnecessitating productive explanation can still explain why
it actually obtains. Do not attempt to prove CCR by importing
necessity of each actual contingent cone. Instead ask for a
**positive account of the availability of the productive input**,
distinct from its conditional operation given that it is available.

For a Hume–Edwards or infinitist account, grant all actual local
productive facts, not merely their conditional laws. These facts
are stronger than the universal guarded theory, but their factual
inputs already include the obtaining of actuality within C.
They can explain x relative to its supplier without independently
explaining why *any* C-member is actual. The exact unresolved
question is whether the whole conjunction of those local
explanations is adequate at this broader scope. That is a
substantive explanatory standard, not a logical prohibition of
entailment from ground to effect or of jointly grounding a whole
by its parts. There is no proof here that the rival is internally
contradictory. A constitutive holist can explicitly defend the
whole fact's actuality without treating it as a productive bearer;
a coinductivist can defend maximal actuality as a primitive
principle. Both owe an explanation of existential import if they
claim this broader explanatory scope.

The positive source account has a concrete comparative advantage
when explaining a **particular received cone of effects**: it
offers actual productive input available without receipt from
that cone, rather than beginning with a member whose very
productive availability is conditional on received actuality
within it. No conservation law or finite path length enters this
reason. This advantage is conditional on warrant for nonreceived
availability and an actual exercise relevant to the effect, not
just an R-root or an abstract necessary law. For the enlarged
explanandum of all actuality, which includes the source's own
existence, a brute source incurs the same residual existential
burden. An independently defended intrinsic existence reason,
not bare accessibility-necessity or causal exemption, would
break that parity. This comparison is compatible with a
nonnecessitating sufficient reason; it does not impose deductive
necessitation of every effect.

**Provisional reassessment (not independently reviewed).** The
direct productive-receipt conditional is strongly motivated
within its intended sense. The fixed actual supplier menu and
global monotonicity were unnecessarily demanding sufficient
conditions for some deletion tests; the component guard plus a
joint retained witness permits the displayed varying-supplier,
nonmonotone control. The sufficient packages are not ordered in
general: the monotone proof can preserve only a subset of U. For
example, with a closed two-cycle C={a,b}, outside s activated
unconditionally and outside t activated exactly by a, the full
assignment is fixed, but deleting C makes t inactive. The earlier
monotone proof finds {s}, while J for the entire U={s,t} fails.
Thus the revised criterion trades a stronger retained-witness
requirement for weaker assumptions about the operator. Nevertheless the essential-reception
application, potential component closure, joint realization
and modal/ontic import remain separate. In the two-world frame every chain member is present
at both accessible worlds, so modal non-deletion holds even though
the chain has no root. The same local receipt equations also admit the
empty assignment when evaluated outside that frame. Which assignments
count as accessible requires a further account. Supplier completeness is still modestly favored only
at exhaustive genuinely productive explanatory scope by the
mode-of-having rationale. No increase in warrant for the
unrestricted mode-unspecified 20babef7 is asserted. A purely
necessary global constitution with positive existential import,
or a primitive whole obtaining fact, remains the strongest
rootless competitor; a genuinely underived concrete whole is
not a denial of the narrow foundation conclusion.

**Checkpoint C handoff (historical).** This superseded the earlier draft's handoff,
not its independently reviewed historical assessments. The next
discriminating target is the intrinsic-existence-reason comparison:
can the necessity of a necessary abstract/structural law or
composite whole supply the actual existence of a concrete
realizer without presupposing that realizer, and can the
nonreceived-source account do better at the same scope?
Reuse the existing necessary-being-five-senses assessment,
`NecessaryRootFork`, and intrinsic-existence-reason work #1595;
do not infer a positive existence reason from modal necessity.
Before attempting registration, run canonical CLI retrieval and
semantic preflight and check the precise same-witness consumer.
Checkpoint C's deductions and controls are proposed proof
obligations, not registered evidence. The local environment
again failed GitHub DNS and has no Lean/lake/cargo; independent
semantic challenge and installed-convention inspection are
unavailable here. Keep this PR draft. Intended formal premise
change remains none; the new head requires its own CI/frontier
evidence. No changes to formal declarations or closure rules.


### Checkpoint D: existential import after excluding posterior grounds

**Question and evidence revision.** Can a necessary abstract structure or a
necessary concrete composite whole provide an independently adequate reason
for its own concrete actuality, without importing the very actuality it
explains? Continue C at `9765c079c3b4d3490bfa31a581f9ab672c1b6b16`.
Keep the identical question for the subsistent-esse proposal. This is an
analyst derivation and comparison, not a new primary-source attribution.
The central claim about intrinsic explanation is
`a7bbd2fd-242c-5097-a9a3-581d25835890` (#1595/#319); its reviewed
[assessment](intrinsic-existence-reason-1595.md#current-reviewed-assessment-2026-11-17)
has **no registered God-root consumer**. The planned connections are the
q3a4 source route and the actual-necessary-root/identity route, not a
proof that an intrinsic reason already supplies a GOD_4 bearer. Reuse
`IntrinsicReasonBoundary.ActualRecord` (one actual, nonempty full
record), `selectedNatureRecord` (classification, not adequacy),
`EssenceReasonSeparation` (necessity/essence/reason separation),
`ExistenceIngredient` (joint records, not the sufficiency of individual
ingredients), and `HistorySelection.characterization` (determination
by a truth vector, not priority). No replacement explanation or ground
registry is introduced.

#### 1. Fix the explanandum and the three readings of a nature or structure

Hold one actual bearer n, the positive existence fact E(n), a proposed
nature-description, and the proposed explanation of derivative effects
fixed. When comparing whole foundations, also include the actual
constitution and exercise on which their proposed explanation relies.
Do not credit an account for the explanatory import of a more restricted
explanandum. Following #1595, mere accessibility-necessity, inclusion
of an existence fact in a nature, equal represented essence/esse maps,
and an adequate intrinsic existence reason are distinct.

- **Abstract specification:** a formal relation, universal law, blueprint,
  or essential conditional, whose truth is independent of whether there
  is a real concrete instantiation. It may explain features conditional
  on a realization; its being necessary is compatible with no concrete
  realization if the independently specified theory admits such an
  interpretation.
- **Instantiated nature/structure:** the concrete whole has the nature,
  organization, or exercise in question in reality. This fact is
  existentially committing. Its truth implies actuality of its bearer,
  but logical implication alone gives no direction of metaphysical
  explanation. The instantiated organization may be explained by the
  constituents or conversely; that is a further question.
- **Unconditional existence-conveying nature:** the positive content
  itself warrants the actuality of this very candidate, not merely a
  conditional about instances, and is not a fact whose obtaining is
  explanatorily posterior to the existence it is invoked to explain.
  This is the live positive proposal of the subsistent-esse account,
  but a rival can equally propose it for a necessary whole or a
  nonproductive global ground. It must be tested, not stipulated as a
  special consequence of the term 'esse'.

The first and second readings make different claims. The common move
from the mathematically necessary organization to a factive, actual
organization changes the antecedent; it does not preserve the
explanatory gain for free. For the third reading, an explicit positive
concrete realization axiom can consistently rule out noninstantiation.
Its semantic/ontological warrant, as distinct from its syntactic
existential import, is the issue.

#### 2. Filter actual candidate grounds by explanatory priority, then test their joint import

The increment over C and #1595 is to apply **both** tests to the
same complete record, without assuming one necessary particular part,
well-foundedness, a numerical measure, or that every reason must be
an efficient cause.

At the selected actual standpoint, use a single strict transitive
explanatory-priority relation P on true facts; a -> b means a is
explanatorily prior to b. This is an OPEN interpretation of an order
on facts, not automatically any of the repository's relations on
bearers, exercise tokens, or causes. Strict priority of each
indispensable full-ground ingredient relative to its effect is a
substantive partial-to-full grounding policy, not a theorem about
nonnecessitating reasons. Redundant ingredients may be removed before
applying this policy; do not demand that irrelevant facts be strict
grounds. It is sufficient that the selected record be nonempty and
all its retained members strict contributors in this policy.

Let e=E(n). Let H be the actually true candidate reason facts, with
a fixed interpretation, in the specified explanatory scope. Define
the excluded region D={e} union {f in H : P(e,f)} (intersection with
H where needed), and the eligible region L=H minus D. A strict
adequate full ground G, using this policy, must satisfy
nonempty G subset L: any f=e would violate irreflexivity, and
P(e,f) together with P(f,e) violates transitivity and
irreflexivity. This necessary eligibility filter does not claim
every f in L actually grounds e.

Independently, choose a background theory/interpretation class
K on which the proposed reason claims existential entailment. Keep
the definitions and independently warranted reason-content fixed.
K is a class of formal interpretations, not necessarily the modal
worlds of the actual profile; an omitted n in this class is not
automatically metaphysically possible. An actual interpretation
satisfies the ground facts and e. For each target-absent
interpretation v in K, let B(v) be the members of H true there.
The sufficient-record condition over K is exactly

    for every v with e false, some f in G is not in B(v).

In other words the **same joint record** must exclude every
target-absent interpretation. This is the elementary truth-vector
test specialized to the eligible region; reuse the existing
selection reasoning, rather than counting this equivalence as a
second independent proof.

**Combined discriminator.** If one target-absent v preserves every
fact in L, no nonempty strict-eligible record from H can be
existentially sufficient over K: every such record is contained in
B(v). Conversely, when at least one target-absent interpretation
exists, if every such interpretation omits at least one fact of L,
then L itself is nonempty and entails e on K. This converse
only exhibits a set of actually true eligible facts with the
truth-entailment property, not an admitted, realizable, finite or
metaphysically adequate full ground; the P(f,e) edges need their
own warrant. For a finite nonempty set of omission interpretations,
one can choose one eliminating eligible fact for each; this finite
record also entails e. For an infinite set of omission interpretations,
no finite record is guaranteed. If no omission interpretation exists,
even empty/irrelevant records entail e, so this test cannot distinguish
them. That is the exact necessity-vacuity boundary already noted in
`IntrinsicReasonBoundary`.

One must use a **common** omission interpretation for the forward
obstruction, not one separately chosen for each ingredient. Two
actually true eligible facts p and q may be jointly determining:
one omission preserves p and omits q, another preserves q and
omits p. Neither singleton determines e; {p,q} does. Thus even
when neither abstract ingredient alone can entail existence, the
whole record may have import. To reject all purely abstract
records by the common-omission test requires an actual
model-construction preserving their joint theory. This restriction
prevents dismissing joint sufficient grounds just because each
ingredient individually seems nonproductive.

The priority exclusion is useful even without modal entailment:
a proposed strict explanatory arrow from a posterior fact to its
own explanatory ancestor contradicts the shared priority policy,
whether or not the effect is necessitated. The second test applies
only to a ground offered as entailing concrete actuality relative
to K, not a universal requirement on all causal or nonnecessitating
explanations. Necessity at accessible worlds does not license an
arbitrary enlargement of K. A separate reason that K captures the
independently warranted content, or a real modal bridge to K, is
required before interpreting the omission as a philosophical
counterexample.

#### 3. Matched application to the necessary whole

Reuse `WorldwiseCompositeGround.ReplacementCertificate` (#1097,
result `e167d4d4-2be0-5820-9cbc-8c6ccb2bf473`): the same necessary
whole with replaced contingent proper atoms in both worlds, actual
fusion and strong supplementation, and whole-to-part grounding.
The model grants concrete whole-first grounding and so concedes
selected concrete roothood rather than denying it. Its worldwise
mereology supplies neither the whole's intrinsic reason nor
unrestricted existential independence. #1966's open PR already
tests deficit of perfection and distinct esse, so no general
composition-implies-reception premise is added here.

For this very whole W at the selected world, suppose it is offered
as existentially prior to all its proper parts. Use E(W), E(p) for
the actual part, and K(W) for the actual instantiated constitution.
The targeted extra assumptions are:

- E(W) P E(p) (whole-to-part existential explanatory priority;
  a bridge from the selected bearer grounding edge to fact priority);
- E(p) P K(W) for at least one actual indispensable constitutive
  input p (a partial fact-ground bridge, not mere essentiality,
  co-existence, or parthood);
- K(W) is a strict contributing ground of E(W) itself, not just of
  its structural properties or of its being a whole of this kind.

Then E(W) P K(W) and K(W) P E(W), impossible on the same strict
transitive P. The proof tolerates arbitrarily many or replaced
parts, indirect finite paths, and infinite derivative orders
elsewhere. Only one actual constituent with the displayed priority
path suffices. It requires neither all-world constancy of particular
parts nor all-part priority in being. The first two arrows concern
explanatory priority of positive facts, not a modal necessity of
co-existence; the third is the specific alleged existential
explanation. No source claim or existing checked theorem is
asserted to supply these three interpretations jointly.

**Positive warrant and limitation.** In ordinary realized assemblies,
part states and their organized arrangement often make a structural
fact obtain: remove a required realizing component without
replacement and that specific organization no longer obtains.
This gives a reason to investigate constituent realization as
partial grounding. It does not prove strict priority of the
particular part's existence over a fundamental whole's
constitution. Whole-first functional integration gives a serious
alternative direction (reuse the priority-monism framework),
and merely requiring some part plurality essentially is a
constraint, not an explanatory arrow. Even if the actual
constitution is posterior, the whole could explain its
actuality by another positive nature fact, not K(W); this is
exactly where the candidate record filter is needed. The
argument excludes a specific explanatory cycle, not all priority
monism, mereological essentialism or necessarily composite wholes.

If instead the whole's proposed explanation is an uninstantiated
structure description B plus abstract laws L, the strict-priority
cycle is absent but we need a separate positive existential
import test. In a guarded interpretation with a fixed abstract
domain and variable actual-concrete extension, preserve L and B
and let W and its dependent parts be absent; any outsider can
remain present. If that interpretation satisfies the independently
specified theory, L and B are jointly insufficient for the target.
This construction is legitimate for abstract-only statements and
laws whose concrete obligations are all guarded by actual
members of the removed order; it is not legitimate for an
unconditionally existential, mixed bridge or independently
warranted necessary-concrete theory. Such a rival must explain
the import of that bridge, not merely demonstrate uniqueness of
an abstract realization up to isomorphism.

The key conditional alternative for a concrete whole is therefore:
a reason using an instantiated constituent configuration that
is posterior to W cannot strictly ground W; a description that
survives a common omission cannot entail W; a genuinely
nonposterior, existence-conveying nature remains a live third
option. These are tests on candidate explanations, not an
exhaustive disjunction of all metaphysical modes or a proof
that the third option is empty. Nonnecessitating and nonstrict
explanatory accounts need comparison on their own standards.

#### 4. Apply the identical filter to subsistent esse

Suppose n is independently actual and a relative root.
`RootEssenceIdentity.identityOfActualRoot` derives the represented
essence/esse equality from exactly: this same root, EM,
`ExistingInActAt`, `EsseCauseIsActualConcreteGround`, the q3
causal dichotomy, and no essential efficient self-causation.
Do not infer the dichotomy from the priority filter above.
In particular, an abstract/constitutive noncausal external reason
can evade the efficient-only dichotomy.

If the proposed intrinsic reason is just the fact 'n is in act as
to esse', and that is identical in content to E(n), the strict
ground reading supplies a self-arrow, not an explanation.
If it describes a factive exercised act whose obtaining is
explanatorily posterior to E(n), the same cycle objection applies.
If it is only an abstract essence-description or equality of
represented principle values, a common omission control in
an independently justified interpretation class blocks entailment.
The existing #1887 assessment already distinguishes these and
records `565ccd6c`, the unconditional existence-in-essence
bridge; do not silently treat that premise as established by the
identity result. The positive alternative is nonreceived actuality
as the independently warranted nature of this very actual source,
with no posterior realizing condition. That is a substantive
metaphysical proposal, not efficient self-production. If identity
is itself proposed as a nonstrict explanatory stopping point,
do not impose an extra strict ground arrow by definition.
Then compare the stopping criterion against a fundamental
composite's analogous proposal.

There is a limited comparative advantage for the subsistent-esse
proposal when the composite rival invokes a separately obtaining
and explanatorily posterior organization while the former has no
such realization requirement. This does not establish that the
whole's nature is posterior, that all composition has an
actualizing source, or that the subsistent act has adequate positive
existential content. Conversely, an arbitrary tag or statement of
necessity for the source cannot do the work it fails to do for
the whole. The positive warrant for preferring a nonreceived act
over wholly received productive input remains the mode-of-having
argument from the preceding checkpoints, not an independent
proof of unconditional intrinsic adequacy. Both accounts owe the
explanation of their own existence, unless they defend a stopping
rule under which no further explanation is apt.

#### 5. Finite audit and same-witness correction

The following Python diagnostic was actually run in this session.
All n=1..3 nonempty families of target-absent rows were checked for
every possible exclusion mask; n=4 checks all pairs of rows with
repetition, not every family. Candidate facts are all actual, a row
is a subset of them true when the target is absent, and masks D are
stipulated priority exclusions. This tests the joint sufficiency/
eligibility characterization only; it does not certify actual
strict explanatory orders or metaphysical adequacy.

```python
from itertools import combinations_with_replacement
for n in range(1, 5):
    A = (1 << n) - 1
    rows_n = 1 << n
    families = ([tuple(v for v in range(rows_n) if mask >> v & 1)
                 for mask in range(1, 1 << rows_n)]
                if n <= 3 else
                list(combinations_with_replacement(range(rows_n), 2)))
    for rows in families:
        for D in range(A + 1):
            L = A ^ D
            feasible = [g for g in range(1, A + 1)
                        if g & D == 0 and all(g & ~r for r in rows)]
            common = any(L & ~r == 0 for r in rows)
            assert bool(feasible) == (not common)
            if feasible:
                assert L in feasible
# Output (n, families, cases): (1,3,6), (2,15,60),
# (3,255,2040), (4,136,2176). Total 4282 cases.
# Candidate reason tokens for a selected necessary whole:
law, blueprint, p, q, actual_shape, positive = [1 << i for i in range(6)]
D = p | q | actual_shape
absent = law | blueprint
for g in range(1, 32):
    assert not (bool(g & ~absent) and not (g & D))
# A stipulated nonposterior positive nature token would pass both tests:
assert positive & ~absent and not positive & D
# Jointly eliminating record: neither singleton suffices, both do.
assert all(not all(g & ~r for r in [1, 2]) for g in [1, 2])
assert all(3 & ~r for r in [1, 2])
```

Self-sweep also caught a genuine previous draft scope error:
roothood at w plus contingent-grounding and the necessary logical
background proves an actual necessary root at w, hence
`b19ffd92`, not the all-world underivedness clause of
`0bdcf366`. The corrected paragraph at checkpoint B now names
the missing transport. A two-world structural control (reuse
the shape of the modal-grounding rotating-root controls) has
two actual necessary concreta everywhere, a->b at world 0 and
b->a at world 1, universal access. Each world has a root, all
actual contingent-grounding obligations hold vacuously, but no
one bearer has no incoming actual concrete ground at every world.
This directly tests the invalid extension. It neither contradicts
the existing all-world transport theorems nor implies that
such rotating actual grounding is metaphysically admissible.
The test executed:

```python
worlds = beings = range(2)
exists = lambda w, x: True
edge = lambda w, y, x: ((w == 0 and y == 0 and x == 1) or
                         (w == 1 and y == 1 and x == 0))
roots = [x for x in beings if exists(0,x) and
         not any(exists(0,y) and edge(0,y,x) for y in beings)]
assert roots == [0]
assert all(all(exists(w,x) for w in worlds) for x in beings)
assert not any(all(not edge(w,y,x) for w in worlds for y in beings)
               for x in beings)
```

Earlier A/B/C finite diagnostics were rerun verbatim: 74,088
eligible operator/relation pairs, 15,317 cone cases, 450 with a
nonempty outside postfixed witness; 218 size-three covering
families, 90 not containing U and 128 directed covering; both
nonmonotone varying-supplier controls passed. This is local
Python reproduction, not a new Lean/Comparator proof. CI run
45512050386 for the preceding checkpoint C was still running
at the baseline inspection; final-head CI remains outstanding.

**Provisional judgment and current handoff.** The abstract-law
account incurs a concrete-import burden when its joint abstract
content survives the omission. The composite-whole account
incurs a strict-priority conflict specifically when it uses an
actual constitution posterior to the whole to explain that
whole's existence. Neither conclusion is a general refutation:
a positively existence-conveying, nonposterior whole-nature or
noncausal global explanation remains live. The same combined
filter excludes a copy or posterior act as an intrinsic reason
for a simple source. The prior modest preference for nonreceived
productive availability and suspension on unconditional intrinsic
adequacy are retained; no new establishment, source attribution
or checked support edge. No general composition-to-reception
claim is made. For the root question, a concrete necessary
whole that supplies its parts and has no incoming cause of its own
in the selected relation qualifies as a relative root; identifying that root with subsistent esse continues to
require the existing q3a4 inputs, including the causal exhaustiveness
premise. An abstract reason would also require an actual productive
bearer bridge to yield the root conclusion. For the necessity
route, use the exact same actual root and the contingency
coverage/EM, then separate modal support transport if all-world
underivedness is the endpoint.

Checkpoint D proposed the following test, taken up in the duet comparison below:
**whether the act of existence
itself can be positively characterized without presupposing an
already actual recipient**, and whether the proposed absence
of a limiting/receiving principle warrants nonposterior,
unconditional existence-content (as opposed to a conditional
identity). Reuse #1887's exercise-in-nature and act-fact analysis,
#1595's intrinsic adequacy, and the #1966 deficit-of-perfection
test on the same bearer. Seek a substantive constraint that
distinguishes the existence-mode of a candidate whole from the
subsistent-act account, rather than repeating necessity or a
fixed-point model. A successful argument would give an explicit
bridge to `565ccd6c` and/or the adequate intrinsic reason
`a7bbd2fd`; it must not infer modal necessity or God naming
from a mere equality of principle labels. Reopen on independently
warranted nature-content/instantiation, or an actual partial
ground link from a constituent to the whole's esse.

The four executable comparisons were reproduced in independent review. These
checkpoints give informal deductions under the stated assumptions. The
merged receipt study and inertia control already cover the corresponding
parts of #1616. Present productive supply, its relation to origin and to
exemplar or final causation, and representative applications under #1724
remain open. [Receipt study](https://github.com/moritzbrantner/formal-logos/pull/1966) · [Inertia control](https://github.com/moritzbrantner/formal-logos/pull/1891)

### Can an individual act be identified without first identifying its recipient? (#1724)

Fix one actual individual n, independently picked out as the candidate source of the selected effects. Both accounts owe an answer to the same question: **what about this individual accounts for its concrete existence?** On the subsistent-act proposal, n is itself a particular actuality in virtue of which the derivative bearers exist. The act is the individual to which the giving is attributed. An act of giving to another is an expression of its actuality. It need not be the act by which n exists. On the whole-first proposal the very same n is a concrete, intrinsically differentiated whole whose ways of acting depend on it. Grant both accounts the effects and grant the whole its claimed necessity for the comparison. Neither grant explains n's existence.

**A test of what an act-description can identify.** Consider two ensembles independently playing the same duet. One recording takes both channels from the first performance. A second takes the upper voice from the first performance and the lower from the second. Grant exactly matching notes and timing. Trace the microphones back to the performers: in the first case the two voices belong to one coordinated playing, in the second the editor has combined voices from two playings. The score and the resulting pair of lines cannot settle which provenance is correct. The performers' actual coordination and the channel connections can. The players bear and exercise musical capacities. The coordinated playing constitutes a performance. Explaining which performance it is requires no independently actual performance to which playing belongs as a feature. The priority at issue is constitutive and applies even when players, playing and performance are simultaneous. This identifies an individual act through what is done together and distinguishes it from a repeatable specification. Its positive content includes a criterion that the second recording fails as evidence of a single joint origin.

The example removes **one** reason for thinking that the subsistent-act proposal is empty. Individuating an actuality need not take the form “first find an already actual individual of this kind, then find the further act it received.” The performance has actual players and conditions of production. The test gives no instance of existentially underived activity. Its sharper lesson concerns the direction of explanation: tracing both channels to one playing can tell us *which* playing explains this recording. What explains *that the playing took place* is the musicians' execution. Counting the execution a second time as the performance's own intrinsic reason would misidentify that ground. The same distinction applies even if inquiry starts with an independently authenticated recording.

**Application to n.** The positive grounding reason for subsistent act is that what actualizes an entire subject cannot operate merely as an acquired feature of a subject already actual in that very respect. Otherwise the proposed account already uses the actuality it was to confer. Identifying the concrete individual with its primary actuality gives a constitutive answer to why there is no further recipient at that level. It also makes sense of tracing genuine giving to this particular individual, if the productive links can be warranted independently. Singling out an act by the effects that manifest it is evidence *for* an actual source under those assumptions. The effects need not thereby be grounds *of* its existence. But asking why the individuated act is exercised still calls for more than citing the actual transaction that identified it.

The concrete whole can meet precisely that challenge to a prior recipient. On its strongest reading, its integral activity constitutes one individual and its differentiated activities belong to that individual. The whole need never first stand ready to acquire its constitution. The duet illustrates how unity can belong to a differentiated activity, while the independently traced contributions in that example also explain its occurrence. A whole-first account cannot borrow the latter explanation if it makes the actuality of every contributor depend on n. It can instead take n's differentiated actuality as primitive. The simple-act account can take its singular actuality as primitive on the same terms. Each then has an intelligible bearer of further predications. An intrinsic reason for why the bearer exists requires a further argument on either reading. A concrete whole that actually supplies its parts without an incoming cause in the selected esse relation already concedes a relative root.

**What discriminates.** Evidence that some constituent's *own actuality* contributes to n's existence independently of having received that actuality from n would discriminate against this whole-first explanation. Merely tracing an effect to one of n's internal operations establishes a contribution to the effect. It leaves the direction of existential support between n and that operation open. The same demand applies to a simple candidate identified through its manifestations. Conversely, the #1966 deficit test would count against own being for n if its constitution actually precluded an independently warranted perfection of being under the relevant possession relation and the fullness premise held. Two distinct ways of acting, or two separately traceable channels, demonstrate no such exclusion. [Same-whole deficit test on main](https://github.com/moritzbrantner/truth-core/blob/ec72649fb/docs/notes/priority-monism-framework.md#can-a-necessary-wholes-essential-differences-identify-a-receiver-of-its-esse-1811)

**Provisional judgment.** A particular act admits a positive characterization without a recipient already actual *as that individual*. This answers a conceptual objection to nonreceived act. It gives neither account a comparative advantage in explaining why n exists. In particular, making exercise constitutive of what counts as **this act** tells us what an occurrence must be to be its exercise. It gives no reason internal to n for there to be such an occurrence. Suppose n’s represented esse equals its represented essence. Under #1887’s act–fact link, warrant for unconditional exercise in n’s nature would support the conclusion for n. A hyperintensional reading also needs grounds for substituting the existence fact within the essence claim. To derive `565ccd6c` this way, those grounds and the warrant for unconditional exercise must extend to every being whose represented esse equals its represented essence. For `a7bbd2fd`, the corresponding open question is what feature of n's real nature adequately explains its individual existence even on a nonproductive reading of explanation. The earlier modest preference for nonborrowed supply concerns received effects. The case for an unconditional intrinsic reason at n remains suspended. [Act–fact result and scope](existence-in-essence-identity.md#4-equivocation-check-esse-as-act-and-existence-as-fact) · [Intrinsic adequacy](intrinsic-existence-reason-1595.md#positive-argument-with-each-premise-defended-and-limited)

This provisional comparison received independent semantic challenge. Reopen on an independently warranted account of the particular source's nature that explains its exercise without importing the obtaining of its manifestations, or on evidence that a particular constituent contributes to the whole's esse in the direction just specified. #1976's archive test discriminates dependencies of a complete history with a known writer. It leaves the actual-world act–essence question open. This continuation adds no premise to the CCR transfer `20babef7` → `c6d92415` → `c35b1a5c`, which also requires distinct-esse causal coverage, identity-bearer uniqueness, an actual bearer and excluded middle. Neither existence target is an input to that transfer. [Scope of the archive result on main](https://github.com/moritzbrantner/truth-core/blob/ec72649fb/docs/notes/foundational-absence-warrant.md#12-can-a-necessary-law-license-omission-of-the-unrestricted-bearer)

Independent review of the duet comparison at 9cd00f0db30a12a3c8aa18fef5d13f95516c1691 accepted the rival comparison and reopening conditions. The targeted recheck accepted the individual-to-universal correction at 9f1bd047eee45694535f9757b61680a9a1b26d1a. This disposition covers the duet continuation only.

### Can the instantiated whole explain why there are actual givings in this series?

Fix one actual recipient and the respect in which its concrete availability is wholly received. Grant the reality of every local giver, its exercise and the adequacy of the local explanations. **What accounts for actual productive input being available at all in this recipient's complete supplier cone?** The cone includes the recipient and every finitely reachable predecessor, however numerous. An unrelated giver elsewhere answers a different question.

The classical denial of `20babef7` is that on one fixed q3a4 profile there is a nonempty collection of actual esse bearers closed under **all** distinct actual causes of its members' esse, every member having such a cause. One such collection suffices. To challenge the philosophical thesis *in its productive sense*, grant in addition that the members' availability is genuinely wholly received. The holist proposes that an instantiated organization accounts for there being actual inputs, while each local giver supplies its particular recipient. No unreceived giver need be in this cone. Requiring actual giving at each receipt is common ground. Requiring an ancestral path to an unreceived giver is the disputed step. [Fixed profile and definition](../../TruthCore/Latin/Aquinas/DeEnte/ClosedEsseSource.lean)

#### What an actual shell forces

A nematic director specifies a local axis without distinguishing its two orientations. A closed spherical interface cannot carry a continuous, everywhere regular tangent line field. For isolated defects the signed indices on **one interface** sum to +2. Consequently some local breakdown of regular tangential order is required. The argument starts from the interface, phase and boundary condition. It presupposes neither a token defect nor a count or location.

Fernández-Nieves et al. explain that the PVA in the surrounding aqueous phases “stabilizes the double emulsion and enforces tangential boundary conditions for the nematic liquid crystal.” Preparation and bright-field views of the inner and outer droplets identify the geometry independently of counting cores. Temperature and optical response away from cores give evidence of the material phase. Fig. 3 reports thin shells with two, three or four outer-surface defects. Cross-polarized textures support the charge assignments. In the thick shell of Fig. 1 the lower inner and outer boojums are unresolved as a pair. Counting two there uses the topological requirement as well as the images. [Fernández-Nieves et al., 2007, pp. 157801-1–3, Figs. 1 and 3](https://doi.org/10.1103/PhysRevLett.99.157801)

Han, Lagerwall and Majumdar study two four-defect 8CB shells. Fig. 1(e) resolves all four near the thinnest point of the asymmetric shell. During cooling, Fig. 5(c) shows an integer and five half-integer defects in focus on that shell. Brush counts give magnitudes. Negative signs are inferred using global balance and the interpretation of merging domains, with other sites out of focus. The authors say, “Throughout the above analysis, we have assumed that the boundary conditions remain tangential at both interfaces as the temperature is changed.” They also use the observed textures to corroborate tangency. The independent preparation evidence is defeasible. The empirical identification in this paper draws partly on the features being explained. [Han et al., 2024, Fig. 1, §V Fig. 5 and discussion on p. 064702-8](https://doi.org/10.1103/PhysRevE.109.064702)

Heating into the isotropic phase removes the order while the sample remains. Normal anchoring would permit a radial director. An escape out of the tangent plane in the shell *interior* can change a bulk line configuration while the tangency requirement on an intact interface still imposes its index constraint. A hole through the ordered shell would change the domain. Han et al. leave the depth of penetration of an isotropic nucleus unresolved. Topology constrains realizations. The ordered material makes the constraint physically applicable, and energetics and history bear on which defects actually form. [2007, pp. 157801-3–4](https://doi.org/10.1103/PhysRevLett.99.157801) · [2024, §§V–VI](https://doi.org/10.1103/PhysRevE.109.064702)

#### Transfer to the closed series

The holist gains a substantive point. Even before locating a particular defect, one has a reason why some defect actually occurs. Predicting the same index balance through changes of inventory gives that reason content beyond the report that the observed defects exist. Inferring a global state partly from its manifestations is compatible with the state explaining why there must be manifestations. The inference used to discover it does not determine the direction of ontic dependence. The index theorem supplies no productive act.

Apply this to a candidate global fact H: the entire history occurs as one integrated activity whose constitution requires local givings. If H has an independently characterizable organization which excludes some distributions of exercise and requires input in the selected cone in every realization, H has an answer to why there are givings there even if their bearers are replaceable. Its constitutive role could be nonposterior to the local acts whose productive roles are granted. The local reasons can then explain why *these* givers supply *these* recipients. This is a genuine division of explanatory work if H obtains independently of borrowing the members' actuality.

Test that possibility against `WorldwiseCompositeGround.ReplacementCertificate`. The same whole exists at both worlds, each actual proper atom is grounded by it, and no particular proper part is a proper part at both. Fusion at each world gives no inference that one fixed atom grounds the whole's actuality. The construction also locates its existential input precisely: `wholeAt w` has its existence witness by construction, and two actual atoms are supplied at each world. This is a compatibility result about replacement and the selected grounding direction. Its grounding edges require a further interpretation to count as actual esse causes. [Replacement certificate and witnesses](../../TruthCore/Causality/WorldwiseCompositeGround.lean)

There is a reason the physical inference stops short at the expanded scope. The prepared shell can be identified across clearing. Its continued material existence and its change of phase distinguish two states of that very sample, one of which requires local defects. For the inclusive existence question, appeal to an instantiated history requires an account of what in its actuality plays the role of the prepared sample. If H is obtained by conjoining all the receipts and existentially generalizing away their names, the proposed ground for H still uses those actual receipts jointly. If H is only a law conditional on realization, its applicability remains open. Neither diagnosis excludes an intrinsically organized, primitively obtaining fact. It could supply existential import for its manifestations without any one of them grounding it. What remains primitive in that explanation is that the integral activity occurs. To explain its own occurrence from its nature requires independently warranted existence-conveying content. This test requires no assumption that an absolutely empty world is possible.

We can test the missing actuality premise with an actual datum. Take the occurrence of this inquiry. Under the existing performed-episode interpretation and bearer-existence bridge it warrants an actual bearer without first naming one. If that bearer is the selected recipient, this is evidence that its cone is populated independent of tracing any giver. It is equally available to the holist and the source account. Why does it fail to decide between them? We can have precisely this evidence on either proposed direction of explanation: the integrated history may explain why this episode can occur, or the bearer's received existence may be furnished by a source. Taking the episode as evidence for actual H is legitimate. Taking it as an ontic ground of H and then invoking H as the strict ground of the episode would require the very return path excluded at checkpoint D. And if the episode belongs to a different cone, the bare existential conclusion cannot be moved across to this one. Thus a real case gives existential warrant beyond a blueprint while isolating the missing premise about *what supplies* the same bearer. [Performed episode and bearer scope](cogito-esse-1113.md#one-episode-one-bearer-one-selected-world)

A stronger holist can identify the global occurrence with the givings *taken together*, without grounding their collective occurrence in a conjunction of facts about each giver. On that reading the whole needs no second act to make its activity actual. This answers the objection from a missing additional realizer, just as the duet comparison allowed for an individual act. Identity alone runs both ways. To explain the members from the whole one needs an asymmetry within that identity: an independently warranted condition on the entire activity that requires local exercises while allowing them to exchange roles. If the only condition supplied is that some giving occurs, holding it fixed rules out an empty cone only when “some” already ranges over that cone. Even then it gives back the very existential fact at issue. The shell meets the stronger test because tangency and topology together also rule out populated, otherwise regular textures whose signed indices sum to zero. Tangency and topology can be specified without defect vocabulary. The corresponding burden is to identify such additional content for the series and justify its priority in accounting for actual input. A primitive jointly obtaining activity remains an intelligible stopping point even if this stronger explanation is unavailable.

| Common question | Instantiated organization H | Actual underived giver n |
| --- | --- | --- |
| What explains availability in this cone? | H's constitution, if H obtains and entails or otherwise adequately accounts for actual exercises here. A mere inventory restates their occurrence. | n's nonreceived actuality and its genuine exercise reaching this recipient. An unconnected root provides no input here. |
| Where may the account stop? | At primitive global obtaining. A bearerless H can serve as a constitutive reason without being a productive giver. | At primitive actuality and any otherwise unexplained exercise needed for the effect. Having a power alone does not establish its exercise. |
| What answers for the inclusive basis? | An intrinsic reason or a defended stopping rule. If a receipt strictly grounds H, H cannot strictly ground that same receipt through a return path in the same priority order. | The same demand. Effects can identify n. A posterior effect cannot strictly ground n's existence. |

The modest preference for an unreceived source concerns **exhaustive productive supply**. Exercising an available power and furnishing the actuality on which that exercise depends are distinguishable contributions. The underived giver can make the latter contribution without itself receiving the very input it supplies. That is a positive rationale for tracing the givings further. It neither impugns any local giver's efficacy nor shows that a constitutive answer must itself be another productive transaction. For the inclusive basis there is no demonstrated superiority between primitive global obtaining and primitive source plus exercise. The open #1968 comparison already grants complete derivative reasons with a brute B. B is an actual member there, whereas the strongest genuinely rootless H here is a bearerless obtaining fact. #1966's same-whole deficit argument would need an independently warranted exclusion from the whole's mode of being. Different ways of realizing a local feature supply none. [Same-B comparison at c4418c4](https://github.com/moritzbrantner/truth-core/blob/c4418c40981bf8f04e41e161580102ddc266d70d/docs/notes/explanatory-adequacy-750.md) · [Same-whole deficit test](priority-monism-framework.md#can-a-necessary-wholes-essential-differences-identify-a-receiver-of-its-esse-1811)

#### Consequence and next test

An actual concrete whole with no incoming cause in the selected relation that supplies these recipients along its paths already concedes a relative giver for them. For `20babef7` the productive rationale must apply to **every** nonempty supplier-closed collection in the fixed mode-unspecified profile. This requires warrant both for the interpretation of the causes and for the ancestral step. With `20babef7`, distinct-esse causal coverage `457698e4`, identity-bearer uniqueness `a576300f`, an actual bearer `78cffb8e` and excluded middle `ee4ab504`, the existing `commonSourceOfClosed` (`c6d92415`) gives `c35b1a5c`: one actual uncaused bearer whose represented esse equals its essence, with a finite nonempty causal path to every *other* actual bearer. Path lengths may vary. The theorem specifies no productive mode. [Frozen common-source theorem](../../TruthCore/Results/Aquinas/DeEnte/ClosedEsseSource/Challenge.lean)

**Reviewed provisional finding.** The shell weakens the objection that a whole must borrow a particular local token's actuality to explain a local existential claim. For the actual series, independence from *which* givers occur leaves open explanatory independence from *their joint occurrence*. Reopen on a specified global condition for this series which survives replacement: which distribution of actual exercises does its character rule out, why does it require an exercise in this cone, and what warrants its obtaining or a primitive stop there? Evidence that a constituent's own received actuality grounds that very condition would bear against a strict whole-first answer. Evidence that its realizer is a concrete underived giver exercising into this cone would support the narrow source conclusion. Apply the same exercise and priority tests to a simple source identified through its effects. Another constraint on already actual material would leave this existential question unchanged. No formal premise change.

## Research attempts citing this note

- [Actual hiddenness scope and explicit stage-one identification](../../corpus/attempts/49e02139-da0f-458a-aae7-374b60309f7c.json)
- [C1: complete derivative systems, totality esse-cause route and the Hume-Edwards rival (#1724)](../../corpus/attempts/1e6ff223-838c-43f8-ab94-6d93c1056cfa.json)
- [Closed a precisely delimited Lean formalization gap, not P2/P3](../../corpus/attempts/existential-self-actualization-priority-20261031.json)
- [De ente nature-or-extrinsic inference: intrinsic-actuality reply and current root connection](../../corpus/attempts/fbc68d10-30e4-44b7-ad15-fa302bbad31e.json)
- [Owner renewed the Agrippa/Münchhausen challenge to explanatory regress](../../corpus/attempts/explanatory-regress-adequacy-311.json)
- [Owner-directed definition comparison, attribution deferred](../../corpus/attempts/evil-emotivism-use-boundary.json)
- [Pinned and materialized the full primary 1979 article with byte-identical Wayback fallback](../../corpus/attempts/rowe-deductive-and-appearance-boundary.json)
- [Re-materialized/read Aristotle Met IV.4, II.2, and Aquinas ST I q104 a1 corpus/ad4, retaining…](../../corpus/attempts/foundation-entitlement-20261031.json)
- [Relative First-Way witness boundary and the common-esse reduction to all-respect unmovedness](../../corpus/attempts/ATTEMPT-PRIMA-VIA-FULL-BUNDLE-WEAKENING-OPEN-1021.json)
- [Scope correction prompted by owner: no-self-justifying whole borrowed structure is no longer…](../../corpus/attempts/whole-roster-foundation-20261031.json)
- [Self-origination assessed through the existing existential-production proof](../../corpus/attempts/no-self-origin-warrant-20261112.json)
