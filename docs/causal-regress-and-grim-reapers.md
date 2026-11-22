# Can Grim Reapers prove the *per se* causal-regress premise?

**Target:** `STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES`, the still-open
Second Way claim interpreted as well-foundedness of `CausesAsCaused`. The current
corpus has a sourced reading but no independent proof of this claim. The result
`AQUINAS-ST-I-Q2-A3-SECUNDA-VIA` uses it as a premise; it does **not** establish
it. Likewise, an infinite chain of temporal causes *per accidens* is not the
same claim as an essentially ordered chain exercising power *per se*.

## 1. The no-first-deadline Grim Reaper test

Consider Reapers with deadlines indexed by `Nat`; a higher index signifies an
earlier deadline. There is no earliest deadline. Give each Reaper the rule:

> Reaper `n` acts **if and only if** no Reaper with a higher index acts.

Formally, `acts n ↔ ∀ m > n, ¬ acts m`.

The axiom-free Lean result
`GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` derives a contradiction:

1. If some Reaper `n` acts, no higher-index Reaper acts.
2. In particular, none higher than `n + 1` acts. The rule then **requires**
   `n + 1` to act, contradicting (1).
3. So no Reaper acts. The rule for index `0` then requires Reaper `0` to act,
   again contradicting the supposition.

This is an inconsistency of **that combined schedule and rule**, not of an
infinite ordered set alone. The companion model
`FINITE-GRIM-REAPER-SCHEDULE-CONSISTENT` verifies that three Reapers with the
same rule are consistent: the maximum-index (earliest-deadline) Reaper acts.

The law already captures the strong assumption that there is an action at a
deadline exactly when none has occurred earlier. A physical story must deliver
that law. `INDEXED-SIGNAL-REAPER` derives it from four local station rules
(positive trigger, emission, forwarding, index admissibility), and its controls
show each rule is needed: delete any one and a consistent assignment exists.
Which conditions a real station must meet is therefore exact; whether stations
meeting them can be placed and assembled is the content of the local-pieces and
patchwork premises (see the audit below), not an unspecified further assumption.

## 2. Why this does not yet establish the target

The per se premise in Aquinas, *Summa theologiae* I q.2 a.3, concerns the
simultaneous dependence of an intermediate efficient cause on another. A
Grim Reaper sequence, by contrast, is an arrangement of stations at moments
ordered **in time**, obeying the four local station rules. Neither the temporal
order nor those rules follow from the definition of `CausesAsCaused`. This is a
missing bridge for the *per se* target only: it names the difference (the
Reaper premises are stated over moments, a per se chain need not be temporal)
and is not evidence that the per se claim is false. For the temporal target
(a beginningless past, modal spine premise A3′) there is no such gap; see the
audit below.

`INFINITE-LOCAL-TRANSMISSION-MODEL` makes the underdetermination explicit:

- There is a predecessor relation `R (n + 1) n` with no first member.
- All nodes are currently active, so each satisfies the **local** condition
  `active n ↔ active (n + 1)`.
- Nevertheless `R` is not well-founded (`¬ Acc R 0`).

This is a consistent mathematical model. It is **not** a demonstrated possible
world containing genuinely derivative efficient causes. In particular, a
defender may insist that "causing only as caused" imposes more than matching
activity: a power must actually be *grounded*, not just locally correlated.
But that stronger meaning must be specified and independently defended.

The exact missing step is a **transfer principle** of roughly this form:

> If a genuinely *per se* cause-chain had no first, its powers and dependencies
> could be arranged into a jointly possible Reaper-type configuration with the
> stated action rule.

This is related to a causal-network *patchwork* or recombination principle.
It is not pure logic. Merely assuming "no first entails no effect" as the
transfer principle would restate the desired conclusion and beg the question.
Formalizing a conditional proof from an explicitly assumed transfer principle
is straightforward, but would close no frontier premise until that principle
itself is justified. No such axiom is included in these verified results.

## 3. The deeper issue: which notion of grounding?

An equation at every link, `power(n) = power(n + 1)`, for binary power has two
uniform solutions (every link powerless or every link powered). These are
**genuine, explicitly defined mathematical objects**, but the *equations*
alone do not specify which one is intended.

The stronger theorem `ESSENTIAL-POWER-UNDERDETERMINED` tests whether making the
link's *essential* nature more precise fixes the problem. Its rule says a node
is active **exactly when an immediately upstream cause is active**. It
establishes all of the following without axioms:

1. The whole infinite chain can be active, while a different assignment
   satisfying the same equations has no active members.
2. For **any** chosen link, we can cut it and give a consistent assignment
   that preserves activity above the cut but leaves the cut node and **every
   downstream node inactive**. This models the counterfactual indispensability
   of its immediate cause to the downstream effects.
3. The uncut chain is still not well-founded.

This answers an objection to the earlier `LocalTransmission` countermodel:
even explicitly modeling the removal of instrumental support does not *by
itself* select a unique global source of power. The intervention result is an
**existence of an admissible response**, not proof that real causal powers
must obey exactly these equations or that every intervention has that response.

The contrasting theorem `FINITE-GROUNDING-HAS-SOURCE` takes a different, more
explanatory reading. A node's power is **inductively grounded** when either it
has intrinsic power, or it receives power along one actual link from another
node whose power is already inductively grounded. Lean constructs a finite
path from every such active node to an intrinsic source. If no source exists,
no act in this *inductive* semantics can be established.

Both mathematical approaches are internally coherent. The choice of
inductive (rather than coinductive, greatest-fixed-point or global) grounding
semantics is **a philosophical premise**, not a theorem about natural numbers
or about the Reapers. It cannot simply be hidden inside the meaning of
`CausesAsCaused` to close the Second Way frontier.

This addresses the worry about endlessly deferred *mathematical definitions*:
mathematicians do insist on unambiguous semantics, but infinity by itself is
not a flaw. Implicit or recursive definitions may work through existence and
uniqueness, or through an explicitly chosen least or greatest fixed point.
Tarski's original [lattice-theoretical fixed-point
theorem](https://people.csail.mit.edu/carroll/probSem/Documents/Tarski.pdf)
shows why a monotone self-reference can have a collection of fixed points
with least and greatest members. Existence need not imply uniqueness. What
our successor-chain equations lack is **a justified selection of the intended
solution**. What a metaphysical causal explanation might additionally lack
is an *independent actualizer*, but that claim requires separate argument.

The result `LOCAL-OBSERVATION-SELECTS-SOLUTION` sharpens this qualification:
**once activity or inactivity at node zero is supplied as a fact**, induction
on the index uniquely fixes the activity of every other link in the local
successor chain. So *non-uniqueness without a boundary condition* is not an
argument that the chain is mathematically impossible; one observed effect can
select a solution. **What explains that effect** is a different question.

### Fixed-point reuse audit for #310 (2026-10-28)

At `49b4589aa6744c91a6bc9adec13215d0e7245c9d`, the proposed
least-versus-greatest activation test is already substantially covered:

- `TruthCore.Logic.Regress.Graph.transmission` takes the original-power
  predicate `O` as independent data and sends `S` to
  `{x | O x ∨ ∃ y, R y x ∧ y ∈ S}`. Its monotonicity is proved.
  `Graph.grounded_eq_lfp` identifies its least fixed point with the existing
  `FinitelyGroundedPower R O`, without assuming well-foundedness of `R`.
- `TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource`
  extracts `∃ s, FiniteCausalPath R x s ∧ O s` from that inductive membership.
  Conversely the constructors `FiniteCausalPath.same/link` and
  `FinitelyGroundedPower.intrinsic/borrowed` give the reverse construction by
  induction on the path. This reverse construction is an inspected structural
  consequence, not a newly registered or separately certified theorem here.
- `TruthCore.Results.Logic.RegressSchema.regressSchemaPackage`, through
  `RegressDomains.CrossDomainBoundary`, already certifies the same successor
  graph with every node active, no graph source, `0` in the greatest fixed
  point and `0` outside the least fixed point for `O = False`.
  Thus the contemplated countermodel is already present, not a missing proof.
- `Graph.fixedPoints_equal_of_wellFounded` supplies a sufficient condition for
  equality. `RegressDomains.CycleAndConverseBoundary` explicitly blocks the
  converse: every node can be intrinsic on a self-loop, giving equal fixed
  points without well-foundedness. Neither equality nor finite grounding at a
  selected node establishes global accessibility.

For a world-local application fix **one** `w`, use its existing-being subtype
as carrier, and restrict `R` and `O` to that carrier. The same polymorphic
schema applies; it does not require a new activation engine, a union of
cross-world edges, or a temporal interpretation. This is an instantiation
recipe, not a newly verified world-local physical model. In particular,
`O` remains an independently interpreted input: it must not mean “whatever
source the desired conclusion requires.” Graph sources (no incoming edge)
and intrinsic-power bearers are different predicates in these theorems.

The decisive missing bridge remains **ACT-GROUND**: an independently
characterized actual exercise, in a specified world and respect, must belong
to this least fixed point (or meet another independently defended condition
which entails finite grounding). That bridge would exclude source-free
active assignments by composition with the existing source theorem. It is
not established by monotonicity, an observed effect, link-cut sensitivity,
or the mathematical existence of least and greatest fixed points. Assuming
accessibility supplies a stronger sufficient background, not a defense of
that background. Conversely, the strongest structural rival can regard the
whole non-well-founded assignment as actual and treat the global structure
as its ground. The existing countermodel establishes consistency of the
encoded constraints; it establishes neither that rival's actuality nor its
metaphysical impossibility.

The merged #625 `UniqueFeedback.Controls` control further rules out using
solution multiplicity as a general objection to global constraints: its
sensitive Boolean equations have a unique solution without observational
selection. Those gates are not the pure borrowed-power transmission law,
so they are not substituted for a causal model. The existing
`CONVERGENT-ZENO-SCHEDULE` and `SUPERTASK-FINITE-PREFIX-NONUNIFORM`
controls concern mathematical scheduling and finite-capacity quantifiers;
neither supplies ACT-GROUND or a bound on real causal transfer. The #588
Night/capacity extension preserves that investigation's finite models and
does not establish this bridge either.

Even a defended bridge would initially give an original power in the chosen
respect. `PowerExistenceBoundary.Boundary` retains controls in which such a
source has external support of its existence, or is necessary and composite.
There is no passage here from an original exercise-source to an uncaused
whole being, simplicity or God. The exact root-premise delta is zero; the
no-infinite-per-se-efficient-cause premise, ACT-POWER, ACT-GROUND, ACT-LIMIT
and any Reaper recombination principle remain open. No source attribution,
new argument, result, Challenge or replacement definition is introduced by
this audit. Existing verification evidence is reused; no Lean checker rerun
can discharge the remaining interpretive bridge.

### A new limit test: the intrinsic source escapes to infinity

The verified finite-grounding theorem alone does not authorize us to take
an infinite limit of finite grounded causal histories and infer that the
limit is grounded. `CAUSAL-GROUNDING-LIMIT-SOURCE-ESCAPE` formalizes an
explicit countermodel to that additional *closure under limits* inference:

1. At truncation `N`, the only intrinsically powered node is `N`. Along
   successor links `N → N-1 → ... → 0`, each lower node has an **actual
   finite inductive grounding certificate** in that truncation.
2. For every fixed node `k`, all sufficiently long truncations power `k`.
   So the pointwise limit of the activity predicates is **all-on**.
3. For every fixed `k`, all sufficiently long truncations locate the
   source **somewhere else**. Indeed the source escapes beyond every fixed
   finite set of candidate nodes. The pointwise intrinsic-source limit is
   **empty**.
4. The limiting all-on state satisfies the unchanged local transmission
   equations. But it is not *inductively finitely grounded* with the
   source-free predicate: the new proof **imports**
   `FINITE-GROUNDING-HAS-SOURCE`, which extracts an intrinsic source from
   any such grounding certificate.

The mathematical lesson is the same one exposed by the infinite urn in
[the supertask study](supertasks.md): **the limit of grounded stages need
not be grounded under the same semantics**. It is a quantifier/witness
issue, not a contradiction in the stage-by-stage certificates:

> Each finite truncation has *some* source; therefore the infinite limit
> has a source.

That inference requires an additional uniformity, compactness or closure
assumption. Its failure is not evidence that the source-free all-on
**mathematical fixed point** is inconsistent. Conversely, the coherent
fixed point is not evidence that it is **actual derivative causal power**.
The repository explicitly keeps those semantics separate.

This exposes a sharper **ACT-LIMIT** obligation for #310: why should
metaphysically real exercise of borrowed power be representable by a
source-grounded derivation that is preserved under the proposed passage to
the infinite causal limit? A finite *uniform grounding-depth bound* would
block this particular escape construction; whether such a bound is true of
real essentially ordered causes needs an independent defense and cannot be
silently inserted as a theorem hypothesis. The countermodel also bears on
#311: distribution of already-actual goods or power along every finite
path does not by itself produce or explain the existence of the distributed
good at the source-free limit.

This suggests a sharper proof task than "all infinities are impossible":

1. Define a *per se* instrumental cause by its **essentially borrowed** power,
   not merely its temporal ancestry or observed activity.
2. Establish, without merely defining the desired conclusion, **why real
   instrumental causation must follow the inductive/finite-source semantics**.
   The finite-grounding theorem then entails that an all-borrowed source-free
   chain cannot ground a present act.
3. Challenge this bridge with the stronger cut-edge and global fixed-point
   models. Explain why their power should not count as genuinely derivative
   efficient power, or concede the limit of the proof.
4. Only then, if helpful, defend a bridge from a hypothetical chain to a
   *possible* Grim Reaper configuration. Distinguish logically consistent
   instructions, physically possible operations, and metaphysically possible
   causal networks; a paradox in the instructions by itself does not settle
   these modalities.

### Which reading of "cannot go on to infinity"?

The target premise is formalized as accessibility (`∀ x, Acc CausesAsCaused x`,
DEF-REGRESS-ACCESSIBILITY-READING). The Latin denies more literally that the
series *proceeds to infinity*: that there is an infinite series of causes each
caused as cause by the next (DEF-NO-INFINITE-DESCENDING-PER-SE-SERIES).
DISAMB-NO-INFINITE-REGRESS-READING keeps the two senses apart, and two results
relate them for every relation:

- `REGRESS-ACCESSIBILITY-EXCLUDES-DESCENDING-SERIES` (axiom-free): the
  accessibility reading implies the literal reading.
- `REGRESS-READINGS-COINCIDE-CLASSICALLY` (Mathlib, classical axioms): the
  converse holds too, so in classical logic the formalization is not stronger
  than the literal reading. The converse builds an infinite series from an
  inaccessible being by choice; it is not available constructively.
- `REGRESS-ACCESSIBILITY-ALLOWS-UNBOUNDED-DEPTH` (axiom-free): accessibility
  is well-foundedness, not finite depth. On the naturals with a top that every
  natural links to, every being is accessible, yet chains below the top have
  every finite length. Neither reading bounds how long a finite per se series
  may be.

These are fidelity checks on the formalization, not progress on the premise:
neither reading is shown true of any actual `CausesAsCaused`, and the
countermodels above refute both readings equally on the successor chain.

### What the grounding route still needs

`FINITE-GROUNDING-HAS-SOURCE` gives every inductively grounded being a source,
but not the accessibility reading. Two axiom-free results locate the gap:

- `GROUNDING-WITH-UNIQUE-CAUSE-YIELDS-REGRESS-READING`: if every being's power
  is inductively grounded, sources receive no per se link
  (DEF-SOURCES-RECEIVE-NO-LINK), and each being has at most one immediate per se
  cause (DEF-AT-MOST-ONE-IMMEDIATE-CAUSE), then every being is accessible.
- `GROUNDING-WITHOUT-UNIQUE-CAUSE-ALLOWS-REGRESS`: without the uniqueness
  condition this fails. One source links directly to every node of an infinite
  descending chain, so every node is grounded and the source is uncaused, yet no
  chain node is accessible.

Both are conditionals or countermodels; none of the three antecedents is
sourced or proved of real per se causes, so the premise stays open.

`KANT-WELL-FOUNDED-CAUSES-BLOCK-ALL-CONTINGENT` places Kant's local-causality
countermodel (`KANT-LOCAL-CAUSALITY-INSUFFICIENT`) in the same picture: in any
Kantian ontic model, local causality plus a well-founded `Causes` relation at a
world where something exists excludes every existent being contingent. The
conclusion is the negation of a universal; reaching a necessary being from it
needs excluded middle, and Kant's generic `Causes` is not `CausesAsCaused`.

## 4. Primary-source boundary and further objections

- **Pinned:** Aquinas, *Summa theologiae* I q.2 a.3, via
  `AQUINAS-ST-I-Q2-A3`, argues that removing the first cause removes the
  middle and the last; this is the very inference under challenge.
- **New pinned witness:** Aristotle, *Metaphysics* II.2 (994a),
  `ARIST-MET-II-2`, from the existing immutable Perseus Greek snapshot. Aristotle
  says that all terms of an infinite series of this kind would be intermediate
  and without a first there is no cause. The chapter treats several kinds of
  cause, so applying that statement specifically to the typed relation
  `CausesAsCaused` requires an interpretive step. The passage is **not** counted
  as a mathematical proof of well-foundedness.
- **Koons reading completed:** Robert C. Koons, *The Grim Reaper Kalam
  Argument* (author-hosted manuscript), §4, printed pp.14–16, with §3 and
  §5 context. The pinned witness and prior reconstruction are in
  [the #367 source audit](notes/causal-finitism-367.md#renewed-defense-audit-the-patchwork-bridge-2026-10-28).
  The ACT-TRANSFER reassessment below reuses that work.
- **Further research leads:** Nicholas Shackel, *The Form of the Benardete Dichotomy* (the unsatisfiable-pair
  diagnosis); Alexander Pruss, *Infinity, Causation, and Paradox* (super-tasks
  and causal finitism), and his 2025 essay *Grim Reapers and Logical
  Impossibility* (the effects of additional rules such as resurrection);
  Schmid and Malpass, *Benardete Paradoxes, Causal Finitism, and the
  Unsatisfiable Pair Diagnosis* (objections and replies). These are reading
  leads only. The corpus records no mechanism or argument from them, so they
  carry no evidential weight here (see the audit below).

**Frontier verdict:** the impossible Reaper schedule, finite schedule, infinite
local-transmission countermodel, cut-edge dependence countermodel, observation
selection lemma and finite inductive-source theorem are constructively proved
in their respective models. The escaping-source limit countermodel
(`CAUSAL-GROUNDING-LIMIT-SOURCE-ESCAPE`) is likewise verified.
`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` remains **open**. The next
research slice is an independent defense of why *per se* efficient power has
the inductive source-grounding semantics and why that semantics survives the
physically relevant limit, not a Lean `sorry` removed by restating the target
as an axiom.

For the separate question whether an **endless temporal task can finish**, see
[supertasks and divergent series](supertasks.md). Its limit-endpoint model,
oscillating-output counterexample and fixed-cost divergence result do not
transfer automatically to simultaneous *per se* causal dependence.

## Objection audit for the temporal Reaper (2026-11-12)

**Formal state.** `TruthCore/Causality/GrimReaperPatchwork.lean` (spec
`specs/modal-spine-grim-reaper-patchwork.toml`) states the Reaper argument
against a beginningless past with stations placed *at the moments* of a
strictly descending sequence of moments of a possible history. Two OPEN
premises carry it: **local pieces** (adjacent stations, each obeying the four
local rules relative to its predecessor, are co-possible) and **patchwork**
(co-possible adjacent pieces along the descent glue into one possible world).
`populatedPastsFoundedOfPatchwork` derives founded populated pasts from the
unrestricted versions; `populatedPastsBegunOfPatchwork` derives begun populated
pasts from the versions restricted to coinitial descents (descents running
below every earlier moment, e.g. one station per past day where the past is
metrically infinite), plus countable coinitiality. Each premise holds without
the other in a beginningless integer history. But since no world realizes a
whole arrangement (a theorem), the typed patchwork premise for a frame is
equivalent to "adjacent pieces are not all co-possible along any populated
descent", and the conclusion is equivalent to the two premises together; the
split is informative through the premises' separate motivations, and the
warrant for patchwork must come from the general recombination principle it
instantiates. The registers carry no existential import (they are not tied to
what exists or is present), and the bridge from recombining concrete stations
to these typed premises is not built. This supersedes the near-transcription
`ReaperAssembly`.

Each objection or non-generalization claim in the Reaper records, checked
against the [Substantive Objection Standard](../AGENTS.md#substantive-objection-standard-owner-direction-2026-11-12):

| Claim | Where | Verdict |
|---|---|---|
| "Dropping or weakening these assumptions may dissolve the contradiction" | §1 | Removed. The needed conditions are exact (the four local rules, each shown necessary by `IndexedSignalReaper.Controls`); whether real stations meet them is the local-pieces premise, stated openly |
| Reaper is "supertask-style … with a specialized inhibition rule" | §2 | Reworded. For the *per se* target the named difference (temporal stations vs a possibly simultaneous chain) is a missing bridge, not evidence against the claim. For a beginningless past the arrangement is not a supertask when the descent has slots of bounded-below length, which the typed premises do not require: a coinitial descent may accumulate metrically, as in `(0, t]` |
| The Reaper is "one special case" we cannot say generalizes | an earlier agent report, not in the records | Withdrawn: no difference was named. See the next row for what a difference would have to be |
| What would have to differ for the Reaper not to reach a beginningless past | new | By the theorem, one of: (a) no coinitial descent exists (uncountable coinitiality of time): a formal escape with no independent support from any model of time known to the corpus, so no objection; (b) local pieces fail along it; (c) gluing fails along it. The next two rows substantiate objections, both bearing on metrically finite pasts |
| FLRW cosmology (open-below finite past) | new | **Kept, substantiated conditional on principle L** (solutions of accepted laws are metaphysically possible; labelled like the metric audit's Einstein-static row, which rests on the same principle). Target: the coinitial premises and their conclusion, begun populated pasts (and a fortiori founded populated pasts). Mechanism: the theorem; standard FLRW Big Bang models have time open below (the initial singularity is not a moment), so a populated FLRW history has no begun moment, while countable coinitiality holds there (`t / 2 ^ n`); so if such a history is accessible, the coinitial local-pieces or patchwork premise fails. Independent support: accepted physical theory treats these models as possible. Relevance: the premises are necessity claims over every accessible history. It does not bear on the possibility premise A3′w (possibly begun), which an FLRW-possible world leaves untouched. Established: the formal entailment; the possibility of FLRW histories is the physical input |
| Benardete parity (dense time) | new | **Substantiated, conditional on a separate commitment C**: populated continuous time with a first moment is possible (some accessible history has such time and contingent things after its first moment). A3′w permits C but does not assert it. Target: the unrestricted premises, and the typed coinitial premises. Because `Coinitial` is order-theoretic and `(0, t]` is order-isomorphic to `(-∞, t]`, the typed coinitial premises cannot tell an open-below finite past from a metrically infinite one, so an objection for the former is an objection to the typed premises themselves. Mechanism: in `[0, t]` the descent `t, t/2, …` carries pieces in shrinking slots; together the unrestricted premises exclude contingent presence after 0 (their theorem with `ComingToBeHorns.controls` 8; a `WithBot ℤ` analogue is `GrimReaperPatchwork.controls` 3). So, given C, local pieces or gluing fail for that arrangement. Relevance: in `(0, t]` (no first moment) the same descent is coinitial and its pieces sit in the very same slots; the arrangements differ only at an instant hosting no piece. Established: the formal facts. Analyst argument, not checked: the parity step. The parity also turns on the admissibility clause, which excludes a code from a source outside the descent, such as one at `0` in `[0, t]`. Consequence, given C: the typed coinitial premises are doubtful for open-below finite pasts and give no support against them independent of the first-moment case. Without C the parity has no force |
| Does the parity reach a metrically infinite past (one station per day)? | new | Not shown. The typed premises above have no metric; the metric version below (slots of at least a fixed length) is now typed, and its premises are silent about every metrically finite past. It transfers only if the first-moment failure is a failure of gluing for every infinite descending arrangement, rather than of pieces in slots shrinking to zero or of gluing for accumulating arrangements. No independent reason for the gluing-general diagnosis is recorded. Unsupported suggestion, no evidential weight |
| Global-compatibility reply to patchwork (#367 audit) | `notes/causal-finitism-367.md` | **Located as a precise fork, not dismissed.** The local premise asks only that each adjacent pair be co-possible, possibly in different worlds. Those witnesses cannot agree on their shared registers: if they did, their values would satisfy every piece at once (`overlapAgreeingWitnessesImpossible`, a checked lemma in the Solution module); the pivot control's witnesses do disagree. So the pieces are duplicated as stations with their rules, not as register contents. (i) If gluing requires overlapping patches to agree on register contents, as recombination of categorical, value-like patches does, the local premise in that coherent form fails along every descent as mathematics: on that reading the Reaper argument does not get started and refutes nothing. (ii) If gluing duplicates stations as bearers of rules whose register contents depend on their context (the intrinsic-powers reading defended in the #367 audit), the compatibility reply must say why such patches fail to glue along a descent. Known local-to-global failures with cycles (a ring of inverting stations) do not apply to a descent, which Koons excludes separately. One acyclic candidate is recorded: given C, by the Benardete row, pieces or gluing fail on the chain `t, t/2, …` in `[0, t]`. It is a candidate gluing failure only if the local pieces there are possible, and it involves metrically accumulating slots. For non-accumulating descents no independently established case is recorded, so under (ii) and a metric restriction the reply is an unsupported suggestion |
| Unsatisfiable-pair diagnosis | §4 leads | No mechanism recorded. That the Reaper conditions are jointly unsatisfiable is common ground (it is `IndexedSignalReaper.impossible`); it does not by itself locate the failure in patchwork rather than in the beginningless past. No evidential weight until its argument is read and recorded |
| Finite tests do not give a global schedule (`GrimReaperFiniteTests`) | #367 attempt | True mathematics about infinitary clauses; not an objection to patchwork, which is a modal premise about pieces of worlds, not a compactness claim |

**Plain verdict.** For the typed premises: two substantive objections are
kept. The FLRW objection shows the coinitial premises, as necessity claims over
every accessible history, exclude a populated open-below finite cosmology that
physical theory treats as possible. The Benardete parity, given C, bears on the
same order-theoretic premises. On the value-agreement reading of gluing the
argument does not get started. The metric reading (descents with slots of
bounded-below length, so a metrically infinite past only) is now typed; its
audit is in the next section. All premises remain OPEN; the support for
patchwork is the defeasible recombination case recorded in the #367 audit. The
pro side must not overclaim either: the theorems show only that whoever accepts
the premises must accept begun (or, unrestricted, founded) populated pasts.

## The metric Reaper (2026-11-12)

**Formal state.** `TruthCore/Causality/MetricGrimReaper.lean` (spec
`specs/modal-spine-metric-grim-reaper.toml`, attempt
[`5f4e157a`](../corpus/attempts/5f4e157a-c495-4cf8-ae58-dcd321a3b5a6.json)) adds a
metric: a `TimeClock` is a real time coordinate strictly increasing along the
order of moments (Mathlib `StrictMono`); the past of `t` is *metrically finite*
when the readings at or before `t` are bounded below (Mathlib `BddBelow`). A
*spaced* descent has every slot at least some fixed `δ > 0` long. The spaced
premises keep the four local rules and the gluing step of the order-theoretic
version and restrict both to spaced descents below populated moments.

**Which clock.** Metric finiteness is not invariant under reparametrization: a
bounded clock (`arctan`) makes every integer past finite and the spaced premises
vacuous there; a logarithmic clock (`ln t` on the positive reals) makes every
open-below finite past infinite, so the spaced premises would target FLRW-shaped
histories again. The disambiguation
[`CLOCK`](../corpus/disambiguations/725f3417-73d0-489f-b8ab-7b2628ff36b7.json)
separates CLOCK_1 (the physically privileged duration: cosmic or proper time;
`PrivilegedClock`, an explicit primitive marker) from CLOCK_2 (any
order-preserving real coordinate; `TimeClock`). The theorems hold for every
CLOCK_2; the statements, the conclusion and every verdict below are read with
CLOCK_1. Why slot duration should matter at all: on the spatiotemporal route of
the #367 audit (a possible isolated Placer, nonoverlapping regions "large enough
for the mechanism" in the alleged infinite past, infinitary spatiotemporal
patchwork, intrinsic powers; Koons pp. 9–13 as recorded there), each station is
a *duplicate* of one possible patch, and a duplicate keeps its intrinsic
duration, which is proper time. Slots of at least `δ` provide the temporal duration for patches lasting at
most `δ`; suitable spatial regions, causal reach and protected interfaces are
additional room requirements (see the concrete application audit below). That is
also the reason for CLOCK_1 rather than an arbitrary coordinate.

**Scope of the clock.** A strictly monotone real clock exists only for time
orders that embed in `ℝ`, so every past then has a countable coinitial subset:
the countable-coinitiality premise of the order-theoretic version is absorbed
into the clock's existence, not eliminated. Times with no real clock (reverse
`ω₁`, the long line, lexicographic `ℝ × ℝ`) are outside the scope of every
result here.

| Result | Content |
|---|---|
| `populatedPastsMetricallyFiniteOfPatchwork` | In linear time, spaced local pieces and spaced patchwork give: in every accessible history, every populated moment has a metrically finite past. The proof extracts a descent with slots of more than one clock unit from a metrically infinite past (`spacedDescentOfUnbounded`, a theorem given the clock, whose existence absorbs countable coinitiality) and composes `GrimReaperPatchwork.arrangementImpossible`, hence `IndexedSignalReaper.impossible` |
| `spacedPiecesOfCoinitial`, `spacedPatchworkOfCoinitial` | In linear time a spaced descent is coinitial, so the coinitial premises strengthen the spaced ones. Control 2 shows the pieces order strict (silent registers) and the two premises jointly strict; strictness of the patchwork order alone is not checked |
| `populatedPastsMetricallyFiniteOfBegun` | In linear time a begun past is metrically finite. Strict: control 2. So founded ⇒ begun ⇒ metrically finite populated pasts, each step strict |
| `controls` | (1) In the beginningless integer history each spaced premise holds without the other and not every populated past is metrically finite. (2) Positive real times (open below, finite; the order and metric shape of FLRW cosmic time): for *every* register frame both spaced premises hold and the coinitial ones do not both hold, and with silent registers coinitial local pieces fail; every populated past is metrically finite and not every one is begun; with the earlier-grounded possibility premise A3′b, begun coming-to-be (A3′w) is not possible. (3) Non-negative real times with nothing present at `0`: for every register frame both spaced premises hold and the unrestricted ones do not both hold; every populated past is begun, not every one founded; begun coming-to-be is possible |

**Exact reach.** The conclusion is that no populated past of an accessible
history is metrically infinite. It is not that populated pasts are begun: an
open-below, metrically finite populated past satisfies the premises and the
conclusion (control 2). Linear time and one clock shared by every world of the
frame are assumptions of the encoding, not premise statements; a frame whose
worlds carry different metrics needs a world-indexed clock, which is not built.

**Objection audit for the spaced premises** (Substantive Objection Standard):

| Claim | Verdict |
|---|---|
| FLRW cosmology (open-below finite past) | **No target, read with CLOCK_1** (cosmic time, under which an FLRW past is finite). A spaced descent exists only below a metrically infinite past (`unboundedOfSpaced`), so the spaced premises hold for every register frame in a populated open-below finite past (control 2). The objection still applies, unchanged, to begun populated pasts and to any bridge from metric finiteness to begun pasts (see the connection below) |
| Benardete parity (dense time) | **No target, read with CLOCK_1.** The parity compared pieces in the shrinking slots of `t, t/2, …` in `[0, t]` and `(0, t]`; no spaced descent exists in either, and the spaced premises hold there for every frame (controls 2, 3). Its transfer to a metrically infinite past remains the unsupported suggestion recorded above |
| Misner-type reparametrization (logarithmic time) | **Kept as an objection to the clock choice, open.** Target: the choice of CLOCK_1 on which the two "no target" rows rest. Mechanism: metric finiteness is not invariant under reparametrization; under `ln t` an FLRW past is infinite, the spaced premises apply there, and the FLRW objection returns. Independent justification: the argument attributed to Misner ("Absolute Zero of Time", 1969) that near the initial singularity the physically meaningful count of time is logarithmic, infinitely many physically distinct epochs preceding any moment. This is a lead recorded from memory, not read, so its content is not established here. Reply: in general relativity proper time is what ideal clocks measure, cosmic time is proper time along comoving worldlines, and the duplication route needs intrinsic duration, which is proper time. Unresolved: whether a station patch near the singularity can keep a fixed proper duration, or whether, as the logarithmic view suggests, the relevant processes scale. If they scale, the duplication route has no room-permitting duplicates there, and its relevance to FLRW-like pasts needs another argument |
| Recombination is blind to durations (undercutting the warrant of spaced patchwork) | **Kept, substantiated conditional on L or C.** Target: the warrant of spaced patchwork, not its truth. Mechanism: the only warrant on file is the recombination case of the #367 audit, and neither the pieces nor the gluing step mention durations. A spaced descent and an accumulating one carry the same pieces in order-isomorphic positions, so duration-blind recombination warrants the coinitial and unrestricted instances exactly as much as the spaced ones. Those instances exclude a populated FLRW past (control 2) and, given C, contingent presence after a first moment (control 3). Independent justification: the possibility of populated FLRW histories under principle L (solutions of accepted laws are metaphysically possible), or commitment C, the same inputs the FLRW and Benardete rows accept. Relevance: restricting the scope of the typed premise does not show that the warrant reaches spaced cases but not the others. Reply available: a duration-sensitive principle, recombination of *duplicates* of one possible patch, room permitting (the spatiotemporal route above). It warrants only arrangements with slots bounded below in proper time, so it does not over-generate into the refuted instances. Its own status: its countable generalization is presented by Koons as plausible, not derived (#367 audit, p. 11); and the bridge from duplicated concrete stations to the typed register premise is not built |
| Accepted physical theories have populated models with a metrically infinite past | **Kept, substantiated conditional on principle L** (solutions of accepted laws are metaphysically possible), labelled like the FLRW row of the order-theoretic audit, which rests on the same principle. Target: the conclusion, hence the spaced local-pieces or patchwork premise. Mechanism: contraposition of the theorem. Independent justification: the Einstein static universe (an exact solution of general relativity with dust and a cosmological constant, cosmic time unbounded in both directions) and eternal free motion in Newtonian mechanics are established solutions of accepted laws; if every solution of accepted laws is a metaphysically possible history, the conclusion is false. Relevance: the premises are necessity claims over every accessible history. Established: these are solutions. Not established: that being a solution suffices for metaphysical possibility, the same principle on which the FLRW row relies. The relevant difference from FLRW: FLRW was excluded as a side effect of order-theoretic blindness, against nothing in the Reaper's motivation; a metrically infinite past is the argument's intended target, so here two general modal principles (law-consistency as a guide to possibility; recombination of possible local pieces) conflict directly. The objection names no piece or gluing step that fails. Its weight is that comparison of principles, not resolved here |
| Global-compatibility reply (value agreement) | Unchanged fork. `overlapAgreeingWitnessesImpossible` holds for every descent, spaced or not: on the value-agreement reading the local premise fails and the argument does not start. On the duplication reading, no acyclic gluing failure along a non-accumulating descent is recorded, so no substantive objection |
| Unsatisfiable-pair diagnosis | Unchanged: no mechanism recorded, no evidential weight |
| One clock, linear time | Scope of the encoding, not an objection: no mechanism is identified by which a world-relative metric or branching time would make the premises true and the conclusion false |

**2026-11-12 verdict (application warrant refined by the #1489 audit below).**
Read with CLOCK_1, the typed premises' scope excludes
metrically finite pasts, so the FLRW and Benardete objections have no target in
them. The warrant is unchanged. Duration-blind recombination, the only warrant
on file, supports the refuted coinitial and unrestricted instances just as much
as the spaced ones; this undercutting objection is kept, conditional on L or C.
It is answered only if the duration-sensitive duplication principle is adopted.
That principle has the room proviso as its motivation, and its countable
generalization is not derived. The clock choice faces the open Misner-type
objection. One rebutting objection is kept, conditional on L (law-consistent
populated models with an infinite past). The premises remain OPEN. The theorem
shows only that whoever accepts them must deny that a populated past is
metrically infinite.

**Connection to the spine.** The A3′w derivation
(`GrimReaperPatchwork.possiblyBegunOfEarlierGrounds`) needs begun populated
pasts, and the metric conclusion does not supply them: control 2 satisfies the
spaced premises, metric finiteness and A3′b while A3′w fails. Two plans, neither
built:

1. A named open bridge: in every possible history, a populated moment with a
   metrically finite past has a begun past. With the metric conclusion it gives
   begun populated pasts by a trivial composition (not registered, as it would
   be a transcription step). The bridge is exactly what the FLRW objection
   denies, so the FLRW cost is not removed but isolated in one premise, separate
   from the Reaper premises.
2. A metric arrival: replace the empty-moment step of arrival A (inert
   emptiness A2 with A3) by a premise about histories whose populated past has
   finite duration. Blocker: an open-below finite populated past has no empty
   moment (control 2 is populated at every moment), so A2/A3 cannot be reused;
   a new arrival premise would be needed and has not been formulated.

Built instead (2026-11-12): a connection to Arrival B, the possible-cause
arrival (`MetricBeginningArrival`, spec
`specs/modal-spine-metric-beginning-arrival.toml`). Its premise B1, "possibly,
contingent concrete reality begins", fixes no sense of beginning as typed (an
uninterpreted Scenario predicate, a schematic placeholder). The disambiguation
BEGINS separates two senses that constrain the time before populated moments,
not when contingent reality began: a first moment of that time (BEGINS_1), and
finite duration of that time on the supplied clock, CLOCK_1 intended
(BEGINS_2). An open-below FLRW past satisfies BEGINS_2. The metric conclusion
with possible population gives B1 in sense BEGINS_2
(`possiblyBeginsFiniteDurationOfMetricallyFinite`). Arrival B in that sense then
gives the stage-one conclusion (`necessaryConcreteOfFiniteDurationBeginning`).
So the metric Reaper reaches the root, with no bridge to begun pasts and no
FLRW cost. B1 in sense BEGINS_2 is the cheap premise: under L (solutions of
accepted laws are possible), the principle the FLRW objection itself uses, a
possible populated FLRW history gives it without the Reaper (not formalized).
The weight is carried by the causal-opportunity premise B2. Its cause relation
is an unconstrained parameter, so with B1 it amounts to "possibly a BEGINS_2
history contains an existing concrete being outside the contingent totality".
That already gives the possibility of a necessary concrete being
(`possiblyNecessaryOfFiniteDurationOpportunity`), and no positive warrant for B2
is on file. See
[the modal spine](notes/modal-spine.md) and attempt
[`9d141c6c`](../corpus/attempts/9d141c6c-7979-4d8b-a1b4-7b35ebc9fb21.json).


### Concrete metric station assignment and application audit (#1489, 2026-11-17)

This is the complete **proposed outcome for independent semantic review**, at
baseline `766c3c08fa0bbf1486b9ff277f5870ecbaa94c95`. It concerns temporal station
recombination only; the accepted CCR findings below are unchanged. Targets are
local pieces `37d4e072-212b-4b99-a4ff-bf10d94d5a52` and patchwork
`bb7b476c-4774-4860-a31f-f068aa362f18`, consumed together by argument
`a8c2ef8c` to metric finiteness `4365c3c5`. No new theorem, definition, source
claim or closure is proposed.

**Read evidence.** The cached primary ranges
`KOONS-GRIM-REAPER-KALAM-6-16` and `KOONS-GRIM-REAPER-KALAM-18-22` were read;
their text, stripping the cache's final newline, matches the existing passage
text hashes. No source was refetched. Koons's PGR (p.9) quantifies over each
positive index with one finite duration d; binary patchwork (pp.10–11) requires
metric/topological embeddings into nonoverlapping regions of a possible host;
PInfSP (p.11) explicitly generalizes this to countably many regions. HIP
(pp.12–13) requires regions large enough for Placers, in the appropriate backward
time cones. Section 5.1 (pp.18–19) defends possession of powers as explanatorily
prior to manifestations; §5.2 (pp.19–20) supplies the active/passive signal
version and adjoining half-open regions; §5.3 (pp.20–21) acknowledges causal
provisos. These are source assertions and philosophical reasons, not independent
certificates of metaphysical possibility. The following port-device assignment
is an analyst reconstruction, not an attribution of a new protocol to Koons.

**One uniform assignment.** Fix one accessible history v, a descending c and a
CLOCK_1 proper-time clock k shared by the frame. Fix d > 0 and require
`k(c n) - k(c(n+1)) ≥ d` for every n. Assign g(n), for arbitrary n, the same
finite-duration port mechanism: during the final d units of slot
`(c(n+1), c n]`, it reads the admitted upstream register, issues iff that input
is absent, writes its own location if it issues, and otherwise relays the input
unchanged. The remainder of a longer slot is a protected, lossless holding
channel. This is ONE assignment of capacities for all n, not a choice of a new
kind of device after seeing a local trace. Its operation time d is fixed;
variable waiting channels are additional infrastructure, not exact duplicates
of the finite-duration device. Both channel preservation and the absence of
extra relevant inputs are explicit application assumptions.

Here `g(n)` emits `c n` by the uniform instruction “emit this output location's
name”, rather than by changing a hard-coded numeric inscription in an alleged
exact duplicate. A local location reference/clock calibration and its faithful
projection to the mathematical moment `c n` remain **OPEN**. If a device instead
has a categorical hard-coded numeral n, differently inscribed devices are not
exact duplicates: one must separately warrant that indexed family (as PGR does),
or defend the location-relative implementation. Time translation in the abstract
order supplies neither that reference nor a physical detector of absence.

Temporal room alone is insufficient. This construction assumes a host world
with the spatial width, topology, causal reach, environmental protection and
proper-time embeddings for each mechanism and holding channel. Strictly
monotone real readings do not encode spacetime regions, intermediate instants
or transmission speeds: even integer time has such readings. On a spacetime
interpretation the indicated half-open regions can be adjoining and disjoint;
the type `TimeClock` alone cannot supply them. No new objection to the abstract
theorem follows from these additional application obligations.

**Same dictionary throughout.** Keep exactly the supplied W, B, T, h, Concrete,
accessibility, k and register frame R. A concrete witness world u must satisfy
`access v u`, contain the specified devices/channel events (with their bearers
existing and present under h), and project their actual outputs at `c n` to
`R.out u (c n)` and actual issuance to `R.issues u (c n)`. Do not replace h or
R after obtaining u, add worlds by definition, assume accessibility is universal,
or infer device existence from `PieceAt`. Accessibility from the original w is
not enough: the inner witness must be accessible from v. All these requirements
are stronger than an unindexed assertion that some device is possible.

| Actual `PieceAt` interface | What the uniform mechanism supplies, conditionally | What duplication alone does not supply |
|---|---|---|
| Absent upstream output implies issuance | The detector's response in its normal operating environment | Faithful absence detection, normal conditions, and receipt of exactly `R.out u (c(n+1))` after the holding interval |
| Issuance implies own-code output | The emitter's response using its local location reference | The identification of that reference with `c n`, and successful writing/persistence at the recorded boundary |
| Every present upstream code is forwarded unchanged | A lossless relay and channel, including through unused slot time | Their joint connection, absence of erasure/recoding/interference, and preservation of these conditions in the assembled world |
| Every output equals `c j` for some `j ≥ n` | Own issuance has j=n; a forwarded input satisfies it if its code is `c j` with `j ≥ n+1` | Input origin/index admissibility, exclusion of alien codes, and the whole infinite arrangement's satisfaction of those constraints |

The last row cannot be repaired by deleting inadmissible input: forwarding
quantifies over **every** present upstream code. Nor is “timestamp no later than
this station” sufficient; in continuous time many earlier timestamps are not
members of c. A sealed channel has to preserve a code already in the correct
upstream family. Intrinsic relay power does not entail that boundary fact.
Admissibility is a restriction on actual outputs relative to the entire selected
c, not just a possible conditional response. This is the exact unmet protocol
obligation, not evidence that any particular admissible local device is impossible.

**Uniform local test, all four rules.** For any n, prepare an empty input at
`c(n+2)` and operate g(n+1), then g(n), with the protected handoff. The resulting
three boundary values are
`out(c(n+2))=none`, `out(c(n+1))=some(c(n+1))`,
`out(c n)=some(c(n+1))`; issuance is true at n+1 and false at n.
For piece n+1 the trigger and emission are realized, forwarding has a false
antecedent, and admissibility uses j=n+1. For piece n the trigger and emission
have false antecedents, forwarding is realized, and admissibility again uses
j=n+1. Thus one arbitrary-index recipe meets both complete local pieces, not
merely three response equations. Its empty prepared boundary is not required
to obey piece n+2. The witness for the next pair uses a different prepared
boundary and different manifestations of the same capacities. These are
explicit symbolic boundary data and a conditional device construction; they
are not a new Lean certificate or a demonstration that the required accessible
concrete witness exists. The existing pivot control already supplies the
mathematical local-possibility pattern; no duplicate control is needed.

Countably gluing those boundary data would change the assignment: the pair
n,n+1 makes n+1 issue, whereas the pair n+1,n+2 makes n+1 forward. Consume the
settled complete-trace obstruction (`overlapAgreeingWitnessesImpossible`);
do not infer station possibility from `arrangementImpossible`, or resurrect a
generic non-generalization objection. Capacity-only duplicates avoid fixing
those conflicting manifestations, but then countable realization must preserve
all four actual interfaces, including admissibility, without stipulating one
of those pair-specific empty seeds at every boundary.

**Positive argument and exact strength.** The strongest available tree is:

1. PGR-like local availability plus protected handoff and faithful location
   projection support the arbitrary-index two-device realization above.
   Ordinary recombination makes this a substantive positive case for local
   availability, rather than an inference from the paradox. Normal-condition
   sufficiency is stipulated; physical engineering of ideal devices is not proved.
2. Intrinsic powers explain why duplicates retain the conditional responses:
   possession need not wait for a particular actual activation. This supports
   the preservation step, conditional on duplicate existence, and leaves direct
   primitive acceptance of such capacities available.
3. A possible host with metrically/topologically suitable regions supplies
   room. PInfSP then supplies countably many duplicate capacity-bearers **if
   accepted**. Koons explicitly motivates the infinitary step by generalizing
   recombination; finite successes do not deduce it.
4. To reach the typed patchwork instance, the assembled world must additionally
   remain accessible from v in this h, preserve the dictionary, connect every
   channel, and satisfy the four actual interfaces for the same R and c.
   Duplication of intrinsic powers alone does not establish step 4. Combining
   steps 3–4 is the outstanding countable **realization** commitment, not a
   consequence of the local test.

There is also a quantifier mismatch with the existing typed local premise.
`SlotsAtLeast` only asserts *some* positive lower bound δ. A mechanism of fixed
duration d fits when δ≥d; it need not fit, for example, slots all of length d/2.
PGR's one fixed d does not warrant arbitrarily fast scaled mechanisms. Even on
a continuous proper-time interpretation with all other room conditions met,
the argument above therefore supports only the sufficiently-long-slot instances,
not yet `SpacedReaperPiecesPossible` over every spaced c. No claim that the
construction directly discharges `37d4e072` is made.

This mismatch need not defeat the metric reductio. In a metrically unbounded
past one can choose `c(n+1)` with reading below `k(c n)-d`, just as the existing
`spacedDescentOfUnbounded` proof chooses a reading below `k(c n)-1`. Alternatively,
rescale that theorem's auxiliary coordinate to k/d to obtain gaps >d in the
original proper time; this does not change which clock interprets the final
claim. This is an inspected proof adaptation, **not a newly certified result**.
It suggests a weaker fixed-d application route, provided the host-room and
countable realization commitments hold on that chosen descent. Merely taking
a subsequence does not transport already chosen registers/devices or prove
the original every-descent premises. The philosophical room burden survives.

**Comparison and proposed provisional judgment.** The duration-sensitive
construction improves the positive rationale: intrinsic proper duration, not
order-isomorphism, explains why shrinking-slot controls are outside this
application. The earlier duration-blind objection therefore does not by itself
undercut this fixed-d route. It does not establish the full typed premises;
local availability has a clearer constructive rationale than the countable
realization bridge. No independently established acyclic failure of capacity
recombination in sufficiently long slots has been supplied here. An unspecified
gluing failure has no evidential weight.

Compatibility-constrained realization offers a different account of the same
capacities: permit collections whose actual connected boundary responses are
jointly satisfiable. It preserves intrinsic possession without asserting that
every possible bearer family coexists. It accounts for the accepted trace
obstruction, but that obstruction alone does not show a non-accumulating host
is metaphysically possible. Its remaining price is a justified rule selecting
admissible histories, without merely naming this paradox as an exception.
The recombination account's price is justification that its room, power and
interface assumptions suffice for countable realization. Neither price is an
independent defeat of its opponent.

The existing principle-L alternative takes populated metrically infinite
cosmological solutions as possible histories, hence rejects the universal metric
conclusion. Its independent warrant is law-consistency as a guide to possibility,
conditional on L; it does not construct these station interfaces in those
solutions. Conversely, infinite duration in a cosmological solution does not
by itself prove that the solution has the required capacity-host geometry or
that station insertion preserves its laws. Compare modal permission for the
same CLOCK_1 histories, not a law-consistent host against a silently assumed
law-preserving station insertion. L and the fully applicable universal
recombination bundle cannot both hold if L supplies a populated infinite past;
this is the recorded conflict to assess, not a new defeat. FLRW's finite proper
past remains outside the metric target. The unread Misner lead remains a lead,
not additional established source evidence against the chosen clock.

Overall proposed assessment: **a substantive positive fixed-duration station
proposal, with exact local boundary witnesses and unresolved countable
realization/application warrant**. This strengthens clarity of the support
option without establishing metric finiteness, causal finitism or necessity.
The test resolves the requested uniform capacity recipe at the symbolic level;
a supported application to the full typed premises is not obtained. Reopen
with an independently warranted realization principle covering these connected
protected ports and input-origin conditions in the same accessible history,
or a concrete reason that principle fails in sufficiently long proper slots.
If pursuing fixed-d premises, first certify that precise weaker variant and its
host-room bridge; do not add another conditional paradox theorem as if it
supplied the missing warrant. An independently supported arbitrary-speed
station family would instead address the every-spaced-descent gap.

**Claim/type self-sweep and root effect.** Actual outputs, conditional powers,
station existence and accessible witnesses have been separated in every row.
The symbolic pair has no existential or metaphysical import; neither the pivot
control nor an inconsistent complete trace is a metaphysical counterexample.
CLOCK_1 is fixed throughout; no arbitrary-coordinate physical result is claimed.
No new claim/type binding, frozen Challenge or Lean input changes. The existing
route remains `a8c2ef8c → 4365c3c5`, `54e332e5 → 951a2235`,
`ea5a729c → b19ffd92`, `9de79a41 → 0bdcf366`, `379399d1 → da3facd6`,
`92ab7c94 → 8626f8a5` (God root), with **every companion premise retained**.
In particular Arrival B's causal-opportunity premise `256b5bab` remains a
separate decisive necessity burden; improved Reaper warrant does not supply it.
No premise change is proposed. Coordinator review must cover this entire
assessment before it is treated as independently reviewed support.

**Initial-audit verification scope (before coordinator cache preparation).**
Offline corpus, source-manifest and attribution checks
pass; the corpus check reports existing closure/lexicon warnings. The prepared
CLI was reused from the warm checkout at this exact baseline, explicitly invoked
through `worker_env.py`, because this isolated checkout then lacked local `target` and
`.lake`. No cold build, cache preparation or preview was performed. No proof
input changes require a new Lean, binding, axiom, Comparator or NanoDa run;
unchanged evidence is retained and final integration CI remains required. Live
conventions were resolved at source revision
`15f348b072188255da837578eaafc8a98f12fdf0`. The coordinator should use the
computed `frontier-diff --base 766c3c08fa0bbf1486b9ff277f5870ecbaa94c95
--frontier-root 8626f8a5-9531-5da7-9ebd-f901e74b1129` for the delivered commit;
no graph or premise input was edited.


### Fixed-duration certification and connected-port follow-up (#1489, 2026-11-17)

**Complete new proposed outcome for coordinator review.** This continues the
accepted construction audit above, including the historical-summary repair
cherry-picked as `22c45a039`. The new scope is application alignment and the
port dictionary, not another paradox or a reopening of the settled complete-trace
obstruction. Batch: `specs/fixed-duration-grim-reaper.toml`; vocabulary and
Solution: `TruthCore.Causality.FixedDurationGrimReaper` and
`TruthCore.Results.Causality.FixedDurationGrimReaper.Solution`.

**Exact conditional advance.** Fix `d : {d : ℝ // 0 < d}` once, across indices,
descents and accessible worlds. `DurationSlots k d c` says every slot is at
least this supplied d. It does not existentially choose a new positive bound
per descent. Keep the original h, Concrete, R, k, W and T. CLOCK_2 remains the
encoded coordinate; the intended application fixes CLOCK_1 proper duration.
The subtype checks positivity only; it does not certify a physical clock.

| Statement | Exact coverage | Verified result |
|---|---|---|
| [5c146257](../corpus/statements/5c146257-8141-4393-940b-e8c19e26d390.json) (`DurationPiecesPossible`) | Every populated descending c with slots ≥d has co-possible adjacent four-interface pieces in worlds accessible from v | `26a972d6`: original spaced local coverage implies this |
| [313105b4](../corpus/statements/313105b4-d9a9-4498-961f-1702661c7110.json) (`DurationPatchwork`) | For such c, adjacent co-possibility implies one world accessible from v realizing all pieces | `9ee3a4d8`: original spaced patchwork implies this |
| [fab16501](../corpus/statements/fab16501-c05a-455d-b880-1a8a9a0dc90a.json) (`DurationDescentPossible`) | Each infinite populated past at t in accessible v supplies **one** c starting at t, with slots ≥d and adjacent co-possibility | `ce2779a9`: fixed-duration local coverage implies this |
| Existing `4365c3c5` (`PopulatedPastsMetricallyFinite`) | Every populated past in the accessible histories is finite on k | `8ceddce9`: selected local descent plus fixed-duration patchwork; `778bda9f`: uniform fixed-duration local coverage plus that patchwork |

The selection helper `durationDescentOfUnbounded` reuses
`MetricGrimReaper.spacedDescentOfUnbounded` to obtain an unbounded seed sequence
and `readingsUnbounded` to choose the next seed moment below the preceding
reading minus d. Recursion starts at the **same t**. Positivity and strict
monotonicity give descent; the selected gaps exceed d. It changes neither the
clock nor the register interpretation, and assumes no arbitrary-speed device.
The endpoint proof applies fixed-duration patchwork to the selected descent
and reuses `GrimReaperPatchwork.arrangementImpossible` in its witness world.
No global impossibility theorem is duplicated.

The exact local coverage consumed by this split proof is `fab16501`: one
qualifying locally feasible descent per alleged infinite populated past.
Universal local coverage even over all ≥d descents is unnecessary. Patchwork
is used only at that selected c. The registered three `strengthens` relations
record original local → fixed-duration local → selected local, and original
patchwork → fixed-duration patchwork, each with its strong statement as the
only premise. **No strictness is claimed**, either for an individual implication
or for the conjunctions. There is no distinct absolute weakest metaphysical
premise established here: permitting arbitrary combined antecedents would make
the metric conclusion itself the trivial sufficient assumption. The useful
weakening retains explicit local feasibility and a separate realization rule;
combining them into an “a suitable realizable arrangement exists if the past is
infinite” flag would hide the very burden under investigation. The original
strong route remains intact, with `strong_version_needed` recording that its
extra scope is unnecessary for this endpoint. The uniform fixed-d route likewise
records that the selected-local sibling suffices.

**A tested connected-port recipe for admissibility.** The new computational
helper `guardedStep n input` is the same algorithm for every finite address n:

- absent input: issue and output address n;
- present address j≥n: do not issue; forward j unchanged;
- present address j<n: do not issue; output none.

`guardedOutputAdmissible` proves that every present output of this algorithm
has address j≥n, for **every** input, including invalid ones. This is a local
range invariant, not a claim that station j actually issued. Define the actual
code projection as `some j ↦ some(c j)`, with absent input mapped to none.
`pieceOfGuardedPort` proves `PieceAt R u c n` from these precise conditions:

1. The actual upstream register `R.out u (c(n+1))` equals that projected input.
2. The actual current output equals the projection of the guarded algorithm's
   output, and actual issuance agrees with its issuance flag.
3. Every present input address j obeys n+1≤j.

If the preceding port actually runs the same guarded recipe at address n+1,
its proved output-range invariant supplies condition 3. Thus the admissibility
step need not assume an independent history of actual originating issuance;
it can follow from local output guards plus a faithful connected-port dictionary.
The existing signal-provenance proof remains the separate way of deriving
named issuance from the full actual protocol. No global-origin premise is
silently introduced here.

The rejecting branch does **not** claim that an alien upstream code is forwarded.
When both actual adjacent endpoints implement the recipe and handoff, the
upstream range guard rules that branch out at the receiver. Without that
boundary invariant, the forwarding interface can fail, and the adapter retains
its input-bound hypothesis. Nor is this merely a timestamp test: abstract
addresses are Nat and the projection is c, so outputs name actual members of
the selected descent. A physical code naming an arbitrary earlier time would
not meet this dictionary. For a preselected R, numeric labels do not automatically
decode to the moments of an arbitrary new c: the candidate world must preserve
the chosen schedule/location interpretation under that same R. A hard-coded
indexed family is another implementation option (PGR quantifies over n, and
PInfSP allows a family of patches), but its members are not all exact duplicates
of one categorically labelled device. Neither implementation gets an actual
location map merely by defining the analyst projection. The adapter is checked
for arbitrary input and c;
it is not a metaphysical witness or a new whole-network realization theorem.

**Positive rationale and what remains missing.** The local positive case is
more explicit now. A mechanism that can compare its calibrated address with a
received finite address and either relay, suppress or issue can enforce the
required range. Lossless storage/relay and normal-condition protection explain
how one endpoint's output becomes precisely the next endpoint's input rather
than a newly guessed register value. These are ordinary operations whose finite
composition supplies a defeasible rationale for local protocols; the formal
adapter proves their exact consequence. Koons's p.9 PGR and pp.19–20 signal
reformulation offer the stronger idealized availability/persistence commitments;
his pp.18–19 explanation-order argument supports preservation of the conditional
powers in duplicates. These arguments are cumulative warrant for the local
proposal, not just absence of an objection. The cached source ranges and exact
locators read in the accepted audit are reused; no new historical attribution
or source acquisition is needed.

There are precise remaining qualifications to this rationale:

- **Calibration and address capacity.** The device must acquire its own n and
  faithfully label/projection-map outputs to c n in every relevant world. The
  algorithm is uniform, but n is a supplied argument; its numeral is not an
  intrinsic inscription automatically preserved by exact duplication. Each
  finite label can be represented with finite resources, but their lengths are
  unbounded over n. The symbolic recipe proves no uniform duration d or fixed
  footprint for all such comparisons, storage and transmissions. PGR-like
  ideal capacities may be accepted primitively, but their full universal
  availability remains an explicit commitment. No physical impossibility is
  inferred from this missing engineering or modal evidence.
- **Protected handoff.** A correct isolated response does not guarantee the
  actual interstage boundary equalities. The room hypothesis must include the
  ports, their protection against extra relevant inputs, and lossless holding
  through unused slot time. Variable holding regions in unequal slots are
  additional patches/infrastructure, not duplicates of the one d-duration
  device. Koons's adjoining-region suggestion addresses topological contact;
  it does not alone construct every protected link in this fixed h, R and k.
- **Same-history realization.** The port equalities, calibrated location map and
  normal operating conditions must hold together in a world accessible from v,
  with actual device bearers existing/present under h. Bare h/TimeClock records
  contain no host geometry or devices. PInfSP permits metric/topological
  recombination of a countable *family* of possible patches when a suitable host
  exists; importing it here still needs those protected patch contents and the
  preservation of this history/accessibility/dictionary. No finite test or
  intrinsic-power preservation argument derives that countable permission.

The new guard therefore discharges a **conditional mathematical interface gap**:
how a local port response could entail actual upstream-code admissibility
without a separate asserted global issuance history. It does not discharge the
modal existence of those actual guarded ports, and it does not certify that
one exact finite-duration physical duplicate handles every address. This is
the concrete missing-evidence obstacle for an unconditional application.

**Comparison and full new provisional judgment.** The positive recombination
account now has two additional discriminating features: a duration aligned with
one supplied device runtime, and an output-guard invariant that derives the
four actual interfaces under a specified dictionary. It need not appeal to
arbitrary clock reparametrization, arbitrary-speed scaling, or assumed actual
signal origins. Its support remains conditional on the availability of the
indexed calibrated capacity family, protected connections and countable
same-history realization. The certification improves the fit between the
application and theorem, rather than itself increasing the independent warrant
of those modal commitments.

Compatibility-constrained realization may accept these local computations and
intrinsic capacities while restricting their joint actual manifestations. The
settled complete-trace obstruction remains relevant to the impossible complete
response assignment; it is not evidence against an independently possible
non-accumulating host. No independently warranted failure of this guarded
capacity construction in sufficiently long proper slots has been identified.
An unspecified gluing restriction has no evidential weight. A compatibility
account still owes a positive account selecting its admissible histories;
the recombination account owes a warranted extension from the protected local
patches to the countable connected realization. This does not assign the two
accounts equal support or manufacture a rival defeat.

The principle-L infinite-cosmology comparison retains the same interpretation
and limits recorded above: permission for an infinite proper-time populated
history competes with universal applicability of the station/realization bundle;
it supplies neither that host's protected ports nor a law-preserving insertion
of the devices. FLRW's finite proper past is still outside the metric target.
Arrival B's causal-opportunity premise `256b5bab` remains separate; this work
cannot supply it. Direct primitive acceptance of the relevant capacities or
recombination principle remains available alongside the explicit support route.
No proof status, floor marking or metaphysical defeat is inferred from this
proposed provisional assessment.

**Reassessment and reopening.** The fixed-d alignment question has its new exact
conditional answer. Further progress on actual application requires independent
support for a calibrated indexed family operating with one positive duration,
protected boundary realization and an applicable countable same-history
recombination principle. Reopen on a concrete positive realization argument or
a substantive failure of those specified conditions. Additional register
contradictions, finite schedules, or complete-trace duplication tests would
repeat settled work. This branch is returned for coordinator reassessment with
the realization commitment explicit, rather than declaring the paradox false
or the broader God-existence investigation complete.

**Claim/type self-sweep.** Every theorem uses one supplied h/R/k/d dictionary;
positivity is part of d's subtype, and the main results require linear time.
Local witnesses have accessibility from v; global patchwork asks for that same
accessibility. `DurationDescentPossible` preserves the first moment t.
`guardedOutputAdmissible` witnesses a numeric range property only;
`pieceOfGuardedPort` requires actual output/issuance equalities and an input
bound. Neither implies device existence, physical feasibility or metaphysical
possibility. No no-assignment result is used to infer those possibilities.
The new strength results are implications, not strictness or establishment.
The existing metric endpoint and all downstream companion premises are retained,
including the Arrival B opportunity burden and attribute bridges to the God
root. No shared CCR, De ente, modal-spine or status/import-cache edit is included.
Independent review of this complete new outcome remains the coordinator's step.


**Focused verification and computed premise effect.** The prepared cache was used
through `worker_env.py` without a repeated preflight or cold build. The two new
modules build; all five new results bind with zero mismatches. Comparator and
result NanoDa pass for `26a972d6`, `9ee3a4d8`, `ce2779a9`, `8ceddce9` and
`778bda9f`; the `ce2779a9` config additionally checks the selection and both
port-adapter theorems. A scoped library export includes all 16 declarations of
the new vocabulary/Solution and their dependency closure: NanoDa checked 7544
declarations with no typechecker errors. It reported one nonfatal pretty-printer
diagnostic, “Unable to print axioms”; separate Lean axiom probes for all eight
named theorems show only subsets of `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorryAx` or custom axiom in the delivered proofs. The new Challenge
contains only the ordinary frozen theorem signatures with generated placeholders;
no previously frozen Challenge was edited.

Offline corpus/source/attribution checks pass (no new or changed stating claim),
both owning specs regenerate unchanged, and whitespace passes. The corpus check
retains the existing closure/lexicon warnings and reports the five new definition
status entries as not yet computed. Shared definition-status/import/docs caches
are left for coordinator generation and final integration CI, as assigned.
Live policy source revision remains `15f348b072188255da837578eaafc8a98f12fdf0`.
The proof checks cover the new modules and results; they do not assert that a
full integrated build or the new semantic review is complete.

Computed `truth frontier-diff --base 22c45a039 --frontier-root
8626f8a5-9531-5da7-9ebd-f901e74b1129` on these graph inputs reports:

```text
open premises reaching the root: 413 (284 bare, 78 supported, 51 stated) -> 413 (284 bare, 78 supported, 51 stated)
distinct verified support alternatives: 423 -> 426
verified support alternatives added: 3
  In every possible history, each moment with a contingent thing present has a metrically finite past [4365c3c5] <- Reaper patchwork along every supplied-duration populated descent [313105b4], Adjacent Reaper pieces along every supplied-duration populated descent [5c146257]
  In every possible history, each moment with a contingent thing present has a metrically finite past [4365c3c5] <- Reaper patchwork along every supplied-duration populated descent [313105b4], One locally feasible supplied-duration descent per infinite populated past [fab16501]
  One locally feasible supplied-duration descent per infinite populated past [fab16501] <- Adjacent Reaper pieces along every supplied-duration populated descent [5c146257]
bare premises added: none
```

These are computed conditional support options, not premise discharges or a
ranking of philosophical warrant. The direct-assumption options and original
strong route remain. All companion premises on the existing Arrival B,
necessary-concretum and God-root route are unchanged.



### Finite-prefix causal station recombination (2026-11-22, proposed)

**Positive construction, with the exact modal prices.** Continue #1489 and
#367 without repeating the already verified signal contradiction or #1722's
guarded-port adapter. The positive basis remains Koons's *Grim Reaper Kalam*
(pp. 9–13: locally possible Placer and non-overlapping host regions; pp. 14–16:
causal network replacement retaining predecessor/successor interfaces; pp.
18–21: intrinsic powers, signaling, persistence and causal qualifications).
The existing pinned and previously read source study is
[`causal-finitism-367.md`](notes/causal-finitism-367.md). Pruss's book-level
causal-finitism formulation remains a bibliographic/source gap, not a new
attribution. The strongest proposed inference is:

1. A **station law** is a causally usable intrinsic conditional power with a
   local guarded input/output protocol. Possession of that power is distinct
   from its actual exercise. For the fixed positive proper duration d, posit
   a suitable separately calibratable station for each finite address n.
2. **Finite causal compatibility** permits one accessible history for *each*
   finite prefix of a selected d-spaced descent in which the SAME indexed
   bearers exist, are present at their assigned moments, the earlier bearer
   actually causes the later station, and the four `PieceAt` interfaces run.
   These worlds can have different register contents: the proven overlap
   disagreement forbids a single shared trace, not intrinsically identical
   operating laws.
3. **Countable causal recombination** is a distinct, substantive modal
   commitment: from all those finite witnesses, one accessible history
   preserves the same station mapping, actual causal edges, temporal presence,
   protected ports and signal protocol for *every* n. Merely copying intrinsic
   powers, binary recombination, finite satisfiability, or a countable set of
   idealized instructions does not entail that commitment.
4. One such locally possible family per infinite populated past suffices.
   The already verified `arrangementImpossible` makes its countable
   realization impossible. Therefore the selected clock's populated pasts
   have bounded-below readings, **conditional on** the positive local
   compatibility and global recombination principles. This is not a
   first-moment theorem and not a per-se causal-ancestry theorem.

**New typed tests.** In `FixedDurationGrimReaper`,
`StationOperationAt` requires the two station bearers' world-relative
existence and presence, an actual `ontic.Causes` edge, and `PieceAt`.
`FiniteStationPrefixCompatibility` quantifies over each finite initial
segment with its own accessible witness. `SelectedFiniteStationCompatibility`
selects one d-spaced schedule and a rigidly indexed station family for each
alleged infinite populated past. `CountableStationRecombination` demands one
world in which *all* these actual conditions hold. The solution's
`finiteStationPrefixesGiveAdjacent` and
`durationDescentOfStationPrefixes` connect finite causal witnesses to
the existing graph premise `fab16501`. The additional conditional theorem
`metricallyFiniteOfCountableStationRecombination` reaches existing metric
conclusion `4365c3c5`, reusing the established contradiction. The
certified separation is `causalFinitePrefixControls`: in the structural
surrogate `causalPivot`, `FiniteStationPrefixCompatibility` holds at
`(v = 1, t = 0)` with no single realizing world, so the *inner* implication
of `CountableStationRecombination` is not a consequence of finite
compatibility. A statement-level non-entailment from `7d1b132f` would need a
model of all of `7d1b132f` and is not certified. `finitePrefixNotCountable` is
only the Nat quantifier-order illustration (`∀N ∃bound` versus
`∃bound ∀n`). Neither is a metaphysical counterexample.

**Dependency audit of `9cb8c0ee` (repair after the semantic challenge).**
Because `arrangementImpossible` excludes the consequent of
`CountableStationRecombination` for every descent, the premise holds for a
frame exactly when no populated fixed-d descent with a station map has
finite-prefix-compatible station operations (`countableStationRecombinationIff`).
Two Lean companions of result `7fe26ec1` follow. The conclusion `4365c3c5`
implies `9cb8c0ee` (`countableStationRecombinationOfMetricallyFinite`, via
`unboundedOfSpaced`), so given `7d1b132f` the countable premise is equivalent
to the conclusion it supports. The existing fixed-duration patchwork
`313105b4` implies `9cb8c0ee` (`countableStationRecombinationOfDurationPatchwork`,
via `finiteStationPrefixesGiveAdjacent` and `arrangementImpossible`). Relative
to the `fab16501 + 313105b4` route, the new route therefore uses a stronger
local premise and a weaker gluing premise, in implication order only (no
strictness is claimed). As for the spaced sibling (definition `0e65cf83`),
the premise's warrant must come from the countable recombination principle it
instantiates, not from this instance.

**Strongest positive rationale for `9cb8c0ee`.** The read #367 study records
Koons's infinitary spatiotemporal patchwork PInfSP (p. 11, a countable
generalization presented as plausible) and Causal Power Network Patchwork
CPNPP (pp. 14–15, one possible world realizing all replacement patches with
the specified causal-power graph) as the source's positive countable
recombination principles. They are the strongest available rationale for a
principle of this shape. The exact differences: CPNPP's edges are powers to
influence events, and PInfSP recombines duplicates with intrinsic powers, not
actual `Ontic.Causes` exercises, so a power-to-exercise bridge is needed.
CPNPP's per-node antecedent is a neighbourhood condition (each patch possible
with duplicates of its predecessor and successor patches), which is weaker
than finite-prefix compatibility, but CPNPP also presupposes the causal-power
graph already realized in one possible world. Neither principle fixes a
positive duration d; that restriction is the analyst's. Granted the
power-to-exercise bridge and CPNPP's graph-realization condition, CPNPP-type
warrant would bear on this principle. No new source claim is made.

**Causal interpretation.** The new efficient-cause edges are actual facts
stipulated in each possible history, not inferred from the label "station".
`StationOperationAt` conjoins the bearer chain with the register protocol
without binding them: `R.out` and `R.issues` are indexed by moment, and nothing
relates `stations n` to them, so the `Causes` edge is not modelled signal
transmission. The bearer, presence and `Causes` conjuncts are idle in both
new theorems; their only formal effect is to strengthen `7d1b132f` and weaken
`9cb8c0ee` relative to register-only versions.
They are deliberately distinct from `CausalityFrame.GivesAt` (concurrent
giving of being), the abstract totality-cause predicate in Arrival B, and
causation of an essentially ordered series. Station identity is fixed across
the selected schedule's finite witnesses; the selected schedule itself and
the family can vary with the alleged past. Current `History` has no host
geometry, intrinsic-power type, physical information bounds, or proof that
the same calibrated finite-runtime device can serve arbitrarily large n.
The positive support for locally operating devices is defeasible and
substantive, not a kernel establishment of their metaphysical possibility.
Proper-time duration must be privileged as CLOCK_1, not arbitrarily rescaled.

**Provisional cumulative assessment.** This adds a stronger local premise
that conjoins concrete, present bearers and stipulated `Ontic.Causes` edges to
the register protocol (without binding them to it), and shows exactly which
new modal premise would yield the same metric conclusion. It does not establish the key
countable recombination commitment. Koons supplies a serious positive
intrinsic-power and recombination rationale; the jump from finite compatible
operations to their complete jointly realized trace is an additional
countable principle, not a mathematical consequence. An unmotivated
"gluing could fail" is not treated as contrary evidence. The fixed-duration
capacity, protected handoffs and countable actual realization remain precise
unmet positive obligations; principle L applied to infinite-past cosmologies
remains a separately conditional competing modal permission. The exact
non-God stages remain: `4365c3c5` + possible population
`faa1ff28` -> BEGINS_2 `951a2235`; Arrival B then still requires
`256b5bab` (external causal opportunity), Euclidean access and actual
reflexivity to reach necessary concrete being `b19ffd92`, followed by the
existing God-existence consumers. Two new *conditional* support
alternatives are registered: `7d1b132f → fab16501` (argument `ea68d581`,
result `33b797cc`) and `7d1b132f ∧ 9cb8c0ee → 4365c3c5` (argument `713dd892`,
result `7fe26ec1`). No premise is discharged; the direct-assumption options
and the original `fab16501 + 313105b4` route remain.

**Verification/review boundary.** The new declarations require Lean and
existing batch checks on the proposed PR head. No frozen Challenge, prior
result, source attribution, computed closure or current first-/second-way
interpretation is altered. The independent semantic challenge on PR #1854
answered the question whether `ontic.Causes` here models upstream causal
transmission: it does not; it is an independent conjunct (see above). The
typed theorems hold either way, but metaphysical application needs a
bearer-register binding. Reopen on such a binding, a defended fixed
runtime/address encoding, a rigorous feasible connected-host construction,
or an independently motivated law/constraint that precisely discriminates
countable from finite compatible operation in a non-accumulating proper past.



**Verification candidates, 2026-11-22.** Proposed argument records from concrete finite-prefix station possibility `7d1b132f` to the existing local selected-descent node `fab16501` (theorem `durationDescentOfStationPrefixes`) and from that stronger local premise plus separate countable operation recombination `9cb8c0ee` directly to the existing metric-finiteness node `4365c3c5` (theorem `metricallyFiniteOfCountableStationRecombination`). An actual station operation now requires each bearer to be `Concrete` as well as existing, present and related by `Ontic.Causes`; the interpretation of that relation as genuine signal-level causal influence, rather than a mere additional relation between bearers, still needs a source/event bridge. The proofs are conditional; the same positive duration, family and schedule are held fixed. The countable modal realization principle remains OPEN. Independent semantic challenge findings on PR #1854 are repaired in this section.


**Actual finite-prefix positive model (2026-11-22).** The stronger
`FiniteStationPrefixCompatibility` premise now has an integer-world
structural surrogate, rather than only a register protocol:
`causalPivot` retains the existing beginningless integer time/existence
profile and stipulates world-independent integer succession
(`Causes := fun _ y x => y + 1 = x`) between successive bearers, with every
integer `Concrete`;
station `n` is the existing, temporally present bearer at moment
`-(n:Int)`. One unit of the existing integer clock bounds each slot.
For every N the world cut off at station N+1 witnesses *all* operations
0..N simultaneously; the four guarded register interfaces are derived from
the earlier `pivotFrame`, and the stipulated edge holds on the selected
station pair. The full countable world is impossible by the **imported**
`arrangementImpossible` theorem. The formal certificate therefore separates
finite joint compatibility from global realization for the inner implication,
with the bearer and edge conjuncts included; it does **not**
give metaphysical/physical possibility to the registered patchwork premise
or show that bearer-to-bearer `Ontic.Causes` is actual signal-event
causation. It witnesses formal satisfiability under a stipulated relation,
not causal coherence of stations, and is not evidence against countable
metaphysical recombination.

## Typed per-se / historical distinction (#1112)

`STMT-INFINITE-REGRESS-IMPOSSIBLE-ONLY-IN-PER-SE-SERIES` keeps its original
source claim and frozen two-`Prop` declaration. That declaration is a
transcription of two assertions (`P ∧ Q`), not a proof that a causal history
is possible. The analyst sibling
`STMT-PER-SE-HISTORICAL-SERIES-DISTINCTION` instead constrains two relations.
Attribution of this new formulation is deferred.

`HistoricalLinksAreEssential H E` explicitly says that every proposed historical
predecessor is an essential-dependence predecessor. Given this dictionary and
`∀ x, Acc E x`, the existing
`RegressAccessibilityExcludesSeries.accessibilityReadingExcludesDescendingSeries`
excludes an infinite `H` descent by mapping each chain edge into `E`. Without
the dictionary there is a concrete same-member witness on `Option Nat`:

- Essential candidate links: `E y x ↔ y = none ∧ ∃ n, x = some n`.
- Historical candidate links: `H y x ↔ ∃ n, y = some (n+1) ∧ x = some n`.
- `E` is nonempty and accessible everywhere. Every historical member `some n`
  has the common essential predecessor `none` and historical predecessor
  `some (n+1)`. The chain `n ↦ some n` is injective and infinite; none of its
  historical edges is an essential edge in this model.

A first essential source exists in this witness, not in the definitions of
series or link. Replacing “each cause after the first” in the definition avoids
assuming that the target series already has a first. No transitivity axiom is
imposed on either primitive relation. Well-foundedness is the separate
hypothesis in the conditional, not part of what a link means. The witness
certifies compatibility of these exact relation constraints only. It does not
show a possible infinite past, actual causal history, or that every
per-accidens series is permitted. Separation of edge extensions alone does not
prove counterfactual independence of the causal powers of their endpoints.

The strongest conflation tested here identifies historical links with essential
links; inclusion alone already suffices to exclude the chain under essential
well-foundedness. No claim is made that these two choices exhaust accounts of
causation. The old exact controls
`SecundaVia.secundaViaNeedsPerSeOrder` and
`SecundaVia.secundaViaNeedsNoRegress` are imported and rechecked, preserving the
Nat successor models with respectively empty and successor essential links.
Thus neither the essential-link premise nor its no-regress premise can be
discarded from that general argument. The new compatibility witness strengthens
the empty-link control by making essential dependence nonempty on the same
historical members; it does not satisfy the omitted strong per-se ordering rule.
`RegressAccessibilityUnboundedDepth.accessibilityAllowsUnboundedDepth` is also
reused: arbitrarily long finite essential descents are compatible with
accessibility, whereas a single infinite descending chain is excluded. The new
historical witness supplies the latter chain for a *different* relation.

The stone/stick/hand and father/son examples motivate the intended distinction;
the first is sustained exercise of power, while the second's generation by a
father does not by itself say that the father sustains the son's present
exercise of power. These are intended readings, not a formal identification of
ordinary examples with the predicates. **OPEN:** interpreting essential links as
here-and-now dependence, their removal as loss of power, and historical links
as temporal succession needs explicit time/intervention vocabulary and an
applicability bridge. The existing `TemporalPrimaVia.Controls.descent` gives a
separate time-indexed control, already in the corpus; it is not silently
identified with this binary witness. Moving-as-moved and causing-as-caused also
remain distinct, connected only under their existing explicit link premise.
No root route, floor, no-regress input, or source-derived Challenge is changed.


## Old #310 attenuation acceptance reconciliation (2026-11-11)

The November 3 issue reconciliation predates [PR #1379](https://github.com/moritzbrantner/truth-core/pull/1379).
Its finite-attenuation mathematical item is now covered by that merged batch;
this audit introduces no duplicate attenuation theorem or changed causal meaning.
Evidence baseline: `8014a6806` (the attenuation files are unchanged from delivered
head `0453441ef869d0c8b9317ca356100b39e98ec8d1`). The complete earlier
[applicability walk](notes/contractive-borrowed-power-1378.md) remains authoritative
for its premises, controls and open interpretation burdens.

**Exact existing proof.** In
`TruthCore.Results.Causality.QuantitativeTransferPaths.finitePath`
(result `082838e6-d83c-4cbd-b3aa-e252d6af946c`), the local proof `decay`
derives `P x ≤ q^n * M` for every natural n at any node with no finite path to
positive input. Its final limit step uses
`Mathlib.tendsto_pow_atTop_nhds_zero_of_lt_one` and `ge_of_tendsto` to obtain
`P x ≤ 0`, contradicting `0 < P x`. This is the requested geometric
attenuation reasoning with the slightly weaker factor condition `0 ≤ q < 1`.
It is an internal step of the registered network theorem, not a separately
registered theorem accepting an arbitrary family of scalar estimates.

The full certificate requires a countable weighted network, nonnegative
weights/input/power, a common nonnegative finite upper bound M, summable weight
and weighted-power rows, a common row-sum bound q < 1, and the local balance
inequality `P ≤ s + weighted transfer`. Its positive conclusion is a finite
path to positive input, including length zero. It proves neither global causal
well-foundedness nor an intrinsically independent bearer. Calling a real chain
an instance still requires the quantitative/causal correspondence and these
premises; the mere word borrowed supplies none of them.

`TruthCore.Results.Causality.QuantitativeTransferPaths.vanishingTail`
(result `54e36212-e4d6-4a94-88a8-648ac39ec128`) separately proves the successor-chain
zero conclusion from exact local balance, a common absolute bound and vanishing
cumulative nonnegative transfer factors. Uniform strict fractional loss is a
sufficient mathematical route to geometric decay, not necessary for that result.
The batch also certifies the whole-assignment omission witnesses:
`halfFixed` (`16f89f72-5999-42d2-a9d8-e578f2183259`) permits uniform half-loss
with unbounded powers `2^n`; `nonuniformFixed`
(`b361eb10-4bc7-4cf8-a42c-28d45bc5d7aa`) permits bounded positive powers with
strict but nonuniform losses, and `nonuniformTail`
(`d1c3835a-f5c9-4acf-8664-aa7720ccbd45`) bounds every cumulative product away
from zero. `binaryFixed` permits bounded positive balance when total gain is
one. These are structural mathematical controls, not actual metaphysical models.
Finite grounded horizons remain available through the existing source-escape
certificate; they are not an infinite uniformly bounded lossy counterexample.

**Verification reused.** The original final-head [CI run](https://github.com/moritzbrantner/truth-core/actions/runs/42912864459)
passed corpus/Lean and all selected Comparator shards plus aggregate checks.
The existing result configs certify each named theorem separately. This
reconciliation changes no theorem, Challenge, binding, result status or premise;
no historical source is fetched and no repeat heavy verification is needed.
Computed context marks the finite-path mathematical statement proved and not
reaching the root. This is acceptance progress for model 4, with **no root
premise discharge**. It does not close the broader #310 issue.

**Remaining question and next discriminating step.** ACT-POWER, ACT-GROUND and
ACT-TRANSFER are independent open burdens. The strongest globally active rival
can retain conservative or asymptotically lossless transfer and a globally
obtaining non-well-founded assignment; this batch supplies no contradiction
with an accepted floor for that account. Finite shared-resource conservation
does not by itself force strict aggregate loss. The follow-up
[productive-store investigation](notes/productive-store-1378.md), merged in
[PR #1386](https://github.com/moritzbrantner/truth-core/pull/1386), already tests
finite resources and depletion: positive output in every natural interval is
compatible with decreasing discharge, while uniform demand requires an explicit
positive lower bound. Repeating finite-budget arithmetic is therefore not the
next test.

The useful remaining #310 task is to take one independently characterized
present exercise and its respect, state whether the relevant quantity is
instantaneous power, interval work, capacity or existential support, identify
the same resource and roster boundary, and defend or reject the abstraction to
a common bound plus vanishing cumulative gain. Test that abstraction against
the conservative/global rival and stored-resource exercise. A source of this
quantity still needs a separate bridge to existential independence; #311's
explanatory adequacy does not supply it. The provisional assessment is unchanged:
the bounded lossy class is conditionally excluded; actual all-borrowed per-se
exercise remains underdetermined. Revise this assessment only with independent
warrant for those applicability premises or a different discriminating argument.


**Remaining actuality branch inspected after reconciliation.** The existing
`BorrowedExercise.Certificate` already separates possession, exercise and
lending: the SAME exercise graph and occurrence assignment has an instrument
profile `capOccurs` and a secondary-cause profile `capAll`. The all-instrument
regress is explicitly certified; `SelectedCollapse` also shows that restricting
allowed scenarios changes this classification. Thus neither occurrence nor
lending, by itself, identifies the intended real borrowed capacity. A fresh
profile-switch model would duplicate those controls.

A materially different test is whether dependence in possession of an essential
power reaches dependence of its bearer. The existing
[essential-power investigation](notes/borrowed-exercise-741.md#does-derivation-of-an-essential-power-reach-the-bearer)
and attempt `8eee1ef4-39f2-4cc8-8e31-e7dde1134c0a` already isolate the exact
unmet node: externally grounded possession must be the SAME constitutive
actuality partly grounding the bearer's existence, with composition of those
grounding links and correspondence to the selected existential-support relation.
Inseparability of power and bearer alone supplies neither explanatory direction
nor that correspondence. A nature-first rival can treat a power as consequent
on the nature instead. This is an existing analyst argument, not a new sourced
reading or certified metaphysical theorem from this audit.

The existing `PowerExistenceBoundary.originalPowerBlocksEsseSupportIfItTransmits`
is the exact alternate conditional: esse-support is excluded if every such
support edge transmits this SAME power to a bearer with no incoming transmission.
It leaves the support-to-transmission bridge open. A mechanical input or an
energy ledger cannot silently provide it. For coordinator reassessment, the
next live node is therefore the constitutive-possession/esse-support bridge for
one selected essential power, rather than another fixed-point, budget or
profile-switch calculation. The repository has no independently warranted
identification of that selected power and those constitutive links in the
inspected records. It would be a separate interpretation/warrant assignment;
this reconciliation does not pretend its absence exhausts the parent question.


## ACT-TRANSFER reassessment for #310 (2026-11-11)

### What is already delivered

The November 3 issue comment's “§4 not pinned or read” item is superseded by
existing work, not a new source discovery here. The author-hosted witness is
[recorded](../corpus/passages/koons-grim-reaper-kalam.json), and the
[existing attempt](../corpus/attempts/pruss-koons-finite-history-reading.json)
and [#367 note](notes/causal-finitism-367.md) preserve its reading, rival and
formal follow-ups. This continuation reread the materialized, hash-checked
pp.6–16 and 18–22. The cached PDF title page identifies Robert C. Koons and the fuller title
*The Grim Reaper Kalam Argument: From Temporal and Causal Finitism to God*;
the corpus uses its short title and identifies it as an author-hosted manuscript.
No new historical claim or proof certificate is introduced.

`INDEXED-SIGNAL-REAPER` already derives the Reaper law from the jointly required
index bound, positive trigger, own-code emission and unchanged forwarding;
`GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` supplies the contradiction. The
omission controls preserve the other three rules when one is removed. These
are verified conditional mathematical results. They neither realize the rules
metaphysically nor derive them from arbitrary borrowed power. Repeating a
conditional with an opaque “possible network” premise would add no evidence.

### Does simultaneity itself defeat the strategy?

No such defeat follows from §4. Its CPNPP preserves a directed causal-power
pattern; unlike §3's spatiotemporal patchwork, its stated antecedent does not
require a metric/topology-preserving embedding of the original times. Thus it
would be too quick to say that a present simultaneous series cannot be used
because the illustrative Placers act successively. A defender can propose that
the original series supplies only the possible causal graph, while replacement
patches supply the Placer response and, where needed, its timing. This is the
strongest positive application to #310; it does not infer an infinite past
from a simultaneous chain.

That proposal still needs three different permissions:

1. **Framework interpretation.** The hypothetical present exercises must yield
   actual event-nodes in one possible world, with each selected upstream link
   having the p.15 meaning: an entity's power relevant to influencing the next
   event. A coherent assignment of activity values alone supplies no such
   event/power interpretation. If actual power exercises are admitted as events
   with these influence relations, that particular objection is answered
   conditionally. A mere relational resemblance is insufficient. The prior
   bearer/esse map remains a separate, already recorded gap.
2. **Uniform replacement.** For every node, not merely three named nodes, the
   chosen replacement and exact duplicates of its adjacent replacements must
   form a possible local event context. The Trio is Koons's positive proposal
   for this step (p.16). Moving from that example to every indexed role must
   preserve the relevant detector/register, the trigger and maintained signal
   content, and any required temporal ordering. Relabeling intrinsic
   index-sensitive positions or response powers is not automatically exact
   duplication. This is an uncompleted applicability argument, not a proof
   that the required local contexts are impossible.
3. **Countable assembly.** CPNPP supplies one world realizing all those patches
   in the selected graph. Intrinsicality preserves a power in an exact
   duplicate *if that duplicate exists*; it does not independently provide
   all duplicates' joint existence. Positive influence edges alone do not
   supply complete channel handoff or exclude relevant bypass inputs. Complete
   protected patches are the strongest proposed answer, but their preservation
   together is precisely what needs independent justification.

There is no additional requirement here to preserve the original chain's
spacetime metric under CPNPP. Conversely, a mathematical assignment of new
successive times would establish only scheduling, not any of the three modal
permissions above. No new scheduling theorem is warranted by this audit.

### A discriminating test: duplicating complete events or only capacities?

The phrase “complete protected patch” needs a precise scope. CPNPP's function
on p.15 selects events g(n), and the neighboring contexts must contain exact
duplicates of those same selected events. It does not merely require that for
each n some mechanism of the same general kind could occur beside some other
mechanisms. This makes a useful further test available without inventing a new
Reaper model.

Suppose the proposed patches include complete realized register traces. Assume
there is a duplicate-invariant projection from each selected g(n) to its output
`signal(n) : Option Nat` and issuance fact `issued(n)`, and that each possible
adjacent context preserves the full four local interfaces for those projected
values, including the same input/output handoff. The selection g then already
fixes ONE assignment on Nat. Local realizability for EVERY n entails the index
bound, trigger, emission and forwarding rules for this assignment. The existing
`IndexedSignalReaper.firingLaw` and `GrimReaperImpossible.grimReaperImpossible`
exclude that bundle. Under these strong trace-projection assumptions, the
uniform local-replacement antecedent fails before CPNPP supplies a world.
This is an explicit conditional reuse argument in prose, not a new certified
theorem or a verified source interpretation. In particular, no such projection
from Koons's event patches is established here.

If instead g(n) fixes only possession of a conditional response capacity,
possible local contexts can leave its eventual manifestation undetermined.
Then the proposed trace projection is unavailable, and that preceding argument
does not apply. This preserves the strongest positive reply: intrinsic devices
can have powers independently of what happens to activate them. But then
intrinsic duplication alone cannot be cited as preservation of a preselected
complete trace; the construction must separately show how the globally assembled
capacities enforce the required actual register interfaces and handoff. It
cannot silently alternate between capacity-only local feasibility and fully
manifested trace duplication.

This test sharpens the next source/application question rather than claiming a
new refutation: what exactly belongs to the selected EVENT, and which of its
actual boundary values are invariant under exact duplication? Koons's Trio
example does not explicitly give this event-to-register dictionary. A completed
dictionary could vindicate a capacity-based construction or reveal failure of
its local-context antecedent. Finite satisfiability does not settle either.

### Warrant comparison and provisional assessment

The positive argument has substance: ordinary recombination supports constructing
unfamiliar arrangements from understood capacities, and requiring local adjacent
contexts plus an already possible causal framework improves on unrestricted
juxtaposition. Koons's §5.1 defense of intrinsic powers addresses the objection
that duplication changes possession of those powers. His §5.2 also explicitly
requires persistent position/content; vanishing or recoding channels do not
refute that complete scenario. Its applicability should not be rejected merely
because the original target concerns present exercise.

The strongest standing rival accepts real intrinsic capacities and their
preservation in duplicates, while admitting only collections whose complete
responses and boundary conditions are jointly compatible. It can allow local
recombination without licensing every countable assembly. Its positive account
is compatibility-constrained realization of powers: dispositions do not license
an impossible global manifestation pattern. This is a proposed metaphysical
constraint, not a demonstrated possible source-free world. Its price is a
substantive nonlocal admissibility condition and an account of which histories
it admits; it cannot establish its own possibility by pointing at local
transmission equations. Koons's competing price is independent support that
his local-interface conditions suffice for countable joint realization. His
§5.3 recognition of causal provisos gives a reason to investigate restrictions
rather than dismiss every restriction as ad hoc; it does not establish this
rival's particular restriction.

**Provisional assessment:** the source-reading acceptance subtask is covered,
and the local-protocol-to-contradiction inference is already certified. The
present-chain transfer remains underdetermined by this evidence: neither its
metaphysical joint realization nor the impossibility of all such present
chains has been established. This retains the #367 judgment and corrects #310's
stale source status. No root premise changes. Mathematical finite compatibility
is inadequate evidence for unrestricted assembly: the existing
`GRIM-REAPER-FINITE-TESTS` even keeps each selected clause's full infinite tail
while showing no global assignment. This is not a modal refutation of CPNPP or
a failure of ordinary finitary compactness.

### Reassessment and next discriminating work

Rejected as duplicates or failed inferences: another finite schedule or
fixed-point model; a “possible Reaper world” flag that stipulates the disputed
transfer; deriving countable joint possibility from intrinsic possession or
finite compatibility; treating persistence as missing from the source; and
rejecting §4 solely because the initial series is simultaneous.

The next useful test is the **uniform local replacement obligation**: specify
one exact event-patch assignment for an arbitrary index, including which
register facts are duplicate-invariant and which remain conditional capacities.
For complete-trace patches, test the local-context antecedent against the
existing four-interface contradiction above. For capacity-only patches, defend
the passage to actual global interfaces and the independently warranted
recombination principle that preserves their handoff. If the
only argument for that principle is “otherwise the Reaper contradiction does
not follow,” it provides no independent discrimination. A warranted general
interface/gluing principle, or a concrete incompatibility among the required
local contexts, would change this assessment. Merely certifying another
conditional contradiction would not. The known event-to-esse abstraction burden
and separate loop exclusion would remain even after a successful assembly
argument. These are substantive reassessment points for the coordinator, not
claims that the whole philosophical question has been exhausted.

## Closed grounding collections: the join's regress demand (2026-11-12)

Batch `specs/closed-grounding-roots.toml` (#310, spine warrant item 5). Analyst
formulations, attribution deferred; nothing here is established.

**Weakest consumed statement.** Every join route that used well-founded actual
grounding (AGWF, `STMT-ACTUAL-GROUNDING-WF`) used it only to find an actual root.
Given ascent in esse, "no infinite ascent along grounding chains" is AGWF itself, so
it is not weaker. What the routes consume is **closed-collection rootedness**
(`ClosedGroundingRoots.ClosedGroundingCollectionsRooted`): no collection of actual
concreta containing every actual *concrete* ground of each member is both nonempty
and rootless. It forbids only rootless closed collections (a pure endless descent,
a pure cycle) and allows descent and cycles directly grounded by a root. An actual
root may still have abstract or unmodelled grounds.

- `closedRootedOfWF`: AGWF implies it, constructively; registered as a strength
  order, strict by `Control.limitGrounder` (despite the name, one root *directly*
  grounds every member of an infinite descending chain).
- Reroutes with the other premises unchanged: `necessaryConcreteOfClosedRooted`,
  `underivedOfCoverageClosed`, `underivedFromNecessityOfCoverageClosed`,
  `underivedFromNecessityOfActualCoverageClosed`, `checksClosed`. The old AGWF
  arguments record `strong_version_needed` as not needed for the endpoint.
  `checksClosed` still takes J2.
- Borrowed reality: `closedRootedOfBorrowed` derives the condition from the
  principle over all modelled actual suppliers (`NoWhollyBorrowedCollection`)
  together with the open bridge that actual concreta are supplied only by concreta
  (`ActualSuppliersOfConcretaConcrete`). `Control.abstractSupplier` shows the bridge
  is needed: an abstract item grounds every member of a concrete regress.
- Per se route: `closedRootedOfAttenuation` composes `QuantitativeTransferPaths.finitePath`
  (the #1379 model-4 library, which reached no root before): per se reception with
  uniform loss, a common bound and own esse only at roots gives the condition.
  Its network analogues (`binaryFixed`, `halfFixed`) show the weighted-network
  theorem fails without uniform loss or without the bound; no Profile-level control.
- Limits (`Control`):
  - The direct root grounder keeps reflexive access and no-novel-edge while J2
    fails. So the condition cannot replace AGWF in `unionWFOfNoNovel`; J2 also
    follows from rigid ascent and no infinite ascent among necessary concreta
    (`unionWFOfAscent`). The same model has ascent along a grade with a top
    element and infinite ascent, so a grade maximum does not give no infinite
    ascent.
  - `mediateFoundation`: a foundation reached only through intermediaries (an
    omega+1 order under direct grounding, no direct edge from the root to the
    chain) violates the condition. A mediate or transitive reading of grounds
    would need its own bridge.
  - `rootedCycle` keeps the condition, reflexive access and no-novel-edge while
    asymmetry fails and two necessary concreta support each other.
  - `pureRegress` is the omission countermodel in both from-necessity coverage
    routes.

**Assessment.** The "borrowed reality" argument (wholly supplied being needs a
supplier not itself supplied) is about collections. It yields the condition under
the concrete-supplier bridge, and it supports the condition rather than AGWF's
surplus. The quantitative per se argument is valid but rests on uniform loss, for
which no independent justification is on file: lossless per se reception is
satisfied by the pure regress. A root that directly grounds a chain is a model of
the condition, not a rival to it. The standing rivals are pure grounding
infinitism, pure coherentism and foundation only through intermediaries (under
direct grounding). Because (A) is offered as a necessary principle, a genuinely
possible wholly borrowed collection would defeat its warrant. None of the rivals is
refuted.

Provisional judgment: support for the join's regress step is modestly higher on
the coverage routes, for direct-foundation views. Rival records, prices and
revision conditions are in attempts
[`14fb7669`](../corpus/attempts/14fb7669-48c1-4d38-b702-7ecdce2565b8.json) and
[`4da08bd8`](../corpus/attempts/4da08bd8-8375-40b7-b635-83012168ed6f.json).
Open: siblings for the remaining root-only AGWF consumers, a cross-world
closed-collection condition for J2, and asymmetry for the direct routes.
