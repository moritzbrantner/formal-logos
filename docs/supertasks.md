# Supertasks: can an endless task finish?

[Original PR #317](https://github.com/moritzbrantner/formal-logos/pull/317)

**Question.** A *supertask* is commonly proposed as a sequence of infinitely
many distinct operations carried out during a finite interval. An objection
is that an **endless task cannot end**. That slogan has at least two meanings:

1. An endless, naturally indexed sequence has **no last operation**.
2. Such a sequence cannot have a **terminal time or well-defined result**.

The first is true of an omega-ordered sequence. The inference to the second
needs a separate premise: for example, **every actually completed task has a
last constitutive operation**. We should investigate and defend or refute
that principle, not conceal it in the definition of *completed*.

## Mathematical controls

| Example | Mathematical outcome | What follows, and what does not |
| --- | --- | --- |
| Geometrically shortening durations, $\sum_{k=1}^{\infty}2^{-k}$ | The ordinary partial sums $s_n=1-2^{-n}$ approach **1**. No stage is last; all stage times are before the endpoint (Lean-verified: `CONVERGENT-ZENO-SCHEDULE`). | A *finite-time schedule* and an abstract limit are mathematically coherent. Physical execution, causal completion and a particular endpoint state are not thereby established. |
| Uniform positive duration, $1+1+1+\cdots$ | Partial sums are $n$ and are unbounded. | With exactly one unit of duration per operation, no natural-number budget covers every prefix (the original Lean result proves only this unit-cost duration case; the separate backward resource constraint below treats a general positive real minimum). **The cost assumption matters.** |
| Alternating unit changes, $1-1+1-1+\cdots$ | Ordinary partial sums alternate between 1 and 0 and have **no ordinary limit**. | An endpoint state need not be defined by the preceding values. Generalized summation methods are separate conventions, not ordinary convergence. |
| A constant or eventually constant Boolean output after each stage | The output has a stable terminal value. | No **last indexed operation** is necessary for a well-defined *abstract* limit value under the specified semantics. |

Mathematicians do not reject divergent series as ill-formed objects; they
reject assigning them a **finite sum in the ordinary sense** when that sum
does not converge. Likewise, the existence of infinitely many terms does not
by itself imply divergence. The decisive properties are the durations,
partial sums and terminal-state rule.

The distinction between an actually performed sequence of discrete operations
and a continuum that is indefinitely *divisible* also matters. Traversing a
distance does not automatically instantiate one separately caused action per
mathematical subinterval. Compare Aristotle's already sourced discussion in
*Physics* VI.2 (`STMT-ZENO-TRAVERSAL-CONFLATES-INFINITY-SENSES`).

## Three formal results

The Lean module `TruthCore.Causality.Supertasks` defines small, explicit
models rather than a physical clock. Each result has a separate Challenge,
Solution, inference application, argument and Comparator record.

1. **`SUPERTASK-STABLE-ENDPOINT`:** All natural-number-indexed stages precede
   a designated endpoint, every stage has a later stage, and a constant
   Boolean output has a stable terminal value. This defeats the *bare logical*
   inference **no last stage => no abstract endpoint with coherent output**.
   It is **not** yet a proof of a realizable finite-time supertask.
2. **`SUPERTASK-OSCILLATION-NO-STABLE-LIMIT`:** A recursively alternating
   Boolean output cannot be eventually stable at any proposed terminal
   value. The endpoint may be adjoined as an order point without solving the
   terminal-output problem. This is a discrete analogue of Thomson's lamp;
   no historical attribution is recorded without a pinned source witness.
3. **`SUPERTASK-UNIT-COST-UNBOUNDED`:** The partial cost of $n$ unit-duration
   stages is exactly $n$, so every finite budget is exceeded by some prefix.
   It establishes a *conditional impossibility* for the unit-cost
   schedule, not an impossibility result for all omega sequences.

The oscillating numerical series above is a mathematical **illustration**,
not a Lean-verified limit theorem. The first Lean model proves
order-plus-stability coherence only; the convergent geometric schedule is
verified separately below. Neither supplies a physical mechanism for
attaining an eventually stable Boolean terminal value.

## The convergent Zeno schedule in real time

**`CONVERGENT-ZENO-SCHEDULE`** (`TruthCore.Causality.ConvergentSchedule`, the
first result built on Mathlib) gives the omega-plus-one order of
`SUPERTASK-STABLE-ENDPOINT` a real-valued clock:

$$t_n = 1-\left(\tfrac12\right)^n,\qquad d_n=\left(\tfrac12\right)^{n+1},\qquad t_{\text{limit}}=1.$$

The Lean theorem proves, with Mathlib's `StrictMono`, `Tendsto` and `HasSum`:

1. the stage times are strictly increasing and all below 1;
2. they converge to the endpoint's time 1 (`Tendsto t atTop (𝓝 1)`), although
   no stage time equals 1;
3. each duration is the gap to the next stage, $d_n = t_{n+1}-t_n$, and the
   durations sum to 1;
4. reading `SupertaskMoment.stage n` at $t_n$ and `SupertaskMoment.limit` at 1
   is an order embedding: `SupertaskPrecedes a b` holds exactly when $a$ is
   read before $b$.

So infinitely many stages, none of them last, fit before a finite endpoint
with finite total duration. This is the convergent counterpart of
`SUPERTASK-UNIT-COST-UNBOUNDED`: what blocks a finite budget there is the
fixed positive cost per stage, not the number of stages. Like the other
controls, it is a **mathematical model**. It does not show that infinitely
many distinct physical operations can be performed in finite time (SU-REAL,
#318 stays open), that the endpoint has a coherent output (the alternating
output can run on this same schedule), or that anything explains the
completion (SU-GROUND). Convergence of clock times
(`DEF-REAL-SEQUENCE-CONVERGENCE`) is a different notion of limit from the
stable Boolean output (`DEF-SUPERTASK-STABLE-LIMIT`); see
`DISAMB-SUPERTASK-LIMIT-NOTION`. Its Comparator config permits Mathlib's
three standard axioms ([axiom policy](axiom-policy.md)).

## Typed Zeno motion, bisection and chase controls (#338, partial)

The modern analyst model in
[`TruthCore.Greek.Aristotle.Physics.Typed.Zeno`](../TruthCore/Greek/Aristotle/Physics/Typed/Zeno.lean)
reuses `ConvergentZenoSchedule` and Mathlib's real trajectory,
`HasDerivAt`, mean-value theorem, `Finset` and `Set.Infinite`. It is
**not** a replacement for Aristotle's historically attributed VI.9 or
III.7 readings. In particular, the original `ZENO-ARROW-STATIONARY` result
remains an opaque-atom transcription with its frozen Challenge.

| Precise question | Lean control | Consequence and boundary |
| --- | --- | --- |
| Definite location in each now vs rest | `positionAtEveryInstant_not_rest` | The continuous arrow `x(t)=t` occupies exactly one position at every real instant but has derivative 1 everywhere and changes position. The existence of `x(t)` alone cannot supply the suppressed premise that it is at rest. |
| Zero velocity now vs stationary for all times | `zeroVelocityAtOneInstant_not_stationary` | `x(t)=t²` has derivative 0 at 0 but differs at 0 and 1. One local derivative fact cannot yield global stationarity. |
| Zero velocity *at every* real time | `everyInstantRest_iff_stationary` | For a real trajectory whose derivative exists and is zero at every time, Mathlib's mean-value theorem proves it is constant. This is a **sound conditional inference** on the selected analytic definition of rest, unlike position-at-an-instant implying rest. It does not by itself vindicate Zeno's antecedent. |
| Dichotomy and finite traversal | `dichotomy_reachesEndpoint` | The continuous trajectory `x(t)=t` passes the infinitely many increasing checkpoints `tₙ=1-2⁻ⁿ<1`; their times and positions tend to 1, and `x(1)=1`. Checkpoint multiplicity does not imply nonarrival. |
| Achilles' comparison points | `achilles_catchesAtLimit` | For `fast(t)=2t` and `slow(t)=1+t`, the slower runner is ahead at every checkpoint `tₙ<1`, but their positions agree at time 1. This rejects the shift from every *listed* pre-catch comparison to every time, not the observation that the slower is ahead before the catch. |
| Potentially unbounded finite division | `firstBisectionCuts_card` | The first `n` distinct cuts `tₙ₊₁` are a `Finset ℝ` of cardinality exactly `n`, for every finite `n`. No infinite roster of performed acts is assumed. |
| Infinite mathematical cut set | `mathematicalBisectionCuts_infinite` | The range of all interior bisection cuts is `Set.Infinite`, in the **same** model with every finite prefix. Thus potential finite prefixes do not contradict a completed *mathematical set*; Aristotle's denial of actually completed physical or separable division is a different, still unformalized claim. |
| Performed operations | `finiteOperationRoster_missesCut`, `infiniteCuts_withoutPerformedOperations` | Every stipulated *finite* roster of operation times misses a cut, and an independent empty operation-event set coexists with the infinite mathematical cut set. A genuinely performed omega sequence is **neither proved possible nor impossible**; forbidding it requires a justified event/operation ontology and a nontrivial resource or local-finiteness constraint. |

**Current assessment (conditional mathematical claims):** the analytic arrow
argument is valid from *zero derivative everywhere* to stationarity but
invalid from *location at every instant* to that antecedent; a single zero
derivative is likewise insufficient. The dichotomy and Achilles nonarrival
inferences fail in ordinary continuous real-time trajectory models.
Arbitrary finite subdivision, an infinite set of ideal cut points and
infinitely many physically executed operations are three non-equivalent
notions. These are **discriminating countermodels**, not historical
attributions or a proof of physical completion.

**Cumulative graph connection and limits.** The proofs reuse the *same*
`ConvergentZenoSchedule` proposition registered as
`CONVERGENT-ZENO-SCHEDULE`; they do not invent another convergence
definition. The controls constrain the validity of interpretations of
`ZENO-ARROW-STATIONARY`, `BisectionInfinityPotentialNotActualReading`,
and VI.9's dichotomy/Achilles implications. No new corpus inference
application discharges a root-route statement. In particular:

- `SU-REAL` (#318) still asks whether **physically distinct causal acts** can
  occur at all the mathematical cut times; a `Set.Infinite` of cuts is not
  an ontological event population.
- `SU-END` and `SU-OUTPUT` still require independent endpoint-operation
  and terminal-state criteria; mere trajectory continuity resolves neither.
- `SU-GROUND`, the causal actuality issue #310 and the explanatory
  adequacy issue #311 remain open. A temporal sequence of positions or
  checkpoints is neither a simultaneous *per se* dependence series nor a
  proof of metaphysical groundlessness. The unbuilt bridge must identify
  actual distinct causal operations and explain why the relevant
  explanatory/causal relation transfers to those real-time indices.
- The beginningless-past/resource result below remains conditional on an
  integer time grid and a uniform positive stock increment. It does not
  transfer to the shrinking positive durations of the Zeno model.

**Remaining #338 scope.** Replace the other relevant opaque readings with
sibling typed statements and corpus-bound results where the interpretations
are defensible; investigate zero-derivative rest on restricted time domains,
local finiteness and physical event identity, the general positive lower-bound
duration series and Thomson-lamp *analytic* nonconvergence, and the exact
König/well-foundedness regress hypotheses. The present proof batch does not
settle Aristotle's potentially infinite *physical process* or establish that
any infinity-related causal or God-existence premise is true.

## Indexed physical operations and compact local finiteness (#1859)

The analyst module
[`OperationLocalFiniteness`](../TruthCore/Causality/OperationLocalFiniteness.lean)
refines SU-REAL using Mathlib's **indexed-family**
`LocallyFinite` and `LocallyFinite.finite_nonempty_inter_compact`.
An `Operation` is an occurrence ID and `time : Operation → ℝ` is its
assigned clock reading. Operations with identical timestamps remain distinct.

**Conditional theorem:** For any two real times `a,b`, if the singleton
families `({time op} : Set ℝ)` are locally finite at *every real instant*,
then `{op | time op ∈ Set.Icc a b}` is finite. A closed bounded real
interval is compact, and Mathlib counts the **indices** whose sets meet
it. A uniform positive minimum operation duration is **not** assumed.
The new registered corpus conclusion `CompactOperationCountCertificate`
(formal result: `CompactOperationCount.compactOperationCount`) states this
conditional mathematical consequence; it does **not** assert that any physical
system satisfies local finiteness.

The companion Lean controls test the exact scope.

| Control | Mathematical finding | Philosophical limit |
| --- | --- | --- |
| `zeno_not_locallyFinite_at_endpoint` | Every neighborhood of clock time 1 intersects infinitely many distinct geometric stage indices, because the stage times converge to 1. | The terminal instant need not itself be an operation. Omitting it from the event *population* is insufficient when local finiteness applies to all times in the **ambient** clock interval. |
| `zeno_locallyFinite_below_endpoint` | Around every real time strictly below 1, some neighborhood meets only finitely many geometric stage indices. | Local finiteness **away** from 1 does not imply local finiteness at 1; choosing a time domain that excludes 1 changes the claim. Endpoint *admission* is not the same as an endpoint event (compare #486). |
| `finite_timestamps_infinite_operation_multiplicity` | Countably many operation indices can all have timestamp 0: the *range of timestamps* is finite, but the indexed singleton family is not locally finite. | A set-of-instants reading loses simultaneous occurrences. Event identity and multiplicity cannot be silently reduced to positions on a clock. |
| `smooth_motion_with_nonlocal_checkpoint_indices` | The identity trajectory `x(t)=t` crosses each mathematical bisecting checkpoint with velocity 1; declaring each crossing a new counted operation produces a non-locally-finite family. | Ordinary continuous motion does not by itself provide the ontology of distinct *constitutive causal acts*. To make local finiteness plausible, specify which changes count as separate physical operations. |
| `locallyFiniteTimes_with_infiniteCausalAncestry` | Assign natural-number predecessor-chain nodes the times `-n`. The *same* `FiniteBranching.successorPredecessor` relation is non-well-founded, each upstream node lies earlier, and operation-time singletons are locally finite throughout ℝ. | Local finiteness excludes an infinite event population in a **compact** interval, not an infinite predecessor chain across an unbounded past. It cannot by itself eliminate per se regress. |

**Current scoped assessment.** Local finiteness is a sufficient mathematical
condition for a finite number of identified operation occurrences during a
compact clock interval. Applying the theorem to physical completion would
require an explicit **applicability premise**: why must *genuinely distinct
causally performed acts* have this indexed event-time property, at the endpoint
as well as in the interior? Finite distinguishability cost, finite energy,
bounded transition rate and independently identifiable constitutive acts are
potential warrants to investigate, not properties derived from real-time
continuity. The strongest surviving rival describes unboundedly many ideal
crossings as one continuous process, or proposes genuinely separate shrinking
acts and rejects endpoint-local finiteness. The theorem alone does not exclude
the latter's metaphysical possibility.

**Connection to cumulative arguments.** The positive theorem uses the
exact Mathlib `LocallyFinite` sense, and the Zeno controls reuse
`ConvergentZenoSchedule` and #1853's `bisectionCut`.
The surviving unbounded-past model explicitly reuses the non-well-founded
`FiniteBranching.successorPredecessor`; no distinct causal relation is
introduced to make the result vacuous. The new registered argument is an
additional **mathematical conditional**, not a discharge of the root's
`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` premise.
For Grim Reapers, this argument could restrict the possibility of completing
a compact-time assembled station schedule **if** its stations count as
distinct operations obeying the same local-finiteness condition. It is not
a proof that the original causal-recombination premise is false or that
a necessary concrete being follows. SU-END, SU-OUTPUT, SU-GROUND and the
same-relation applicability bridges in #310/#311 remain **OPEN**.

**Next discriminating test.** Find a defensible physical criterion of
operation identity and an associated local temporal regularity or resource
principle strong enough to imply indexed local finiteness, and test it
against both a continuous trajectory and a realizable discrete operation
system. A bounded clock coordinate is not automatically a physically
privileged proper-time duration (`MetricGrimReaper.TimeClock`, CLOCK_1/2).

## A beginningless past with bounded resource spread

`BOUNDED-PAST-RESOURCE-CONTRADICTION` adds a conditional argument about a
neutral real stock, rather than declaring that an infinite past is impossible.
The profile is `S : Int → Real`, with selected integer `now`. All integer
indices at or before now are in the past; arbitrarily earlier indices are
available. This is a discrete time profile, not a new temporal framework or a
claim about every possible order of time.

The three explicit hypotheses are:

- one fixed `epsilon > 0`;
- one real lower bound `L ≤ S(t)` throughout the past;
- `S(t) + epsilon ≤ S(t+1)` at every unit step with `t < now`.

Backward induction gives

`S(now - n) + n * epsilon ≤ S(now)`

for every natural n. The lower bound therefore yields
`n * epsilon ≤ S(now) - L` for every n, contradicting the Archimedean property
of the real numbers. The available **resource spread** is finite because
`S(now)` and `L` are real values. No finite elapsed-time budget, first event,
finite event count, or traversal initiated at a first event is assumed. The
argument excludes the joint resource profile over a beginningless integer
past; it does not itself prove a first-time theorem for arbitrary temporal
orders. Unlike a forward omega supertask with a first stage and limit endpoint,
this proof only examines longer finite stretches backward from now. A
sufficiently long finite stretch already exceeds the resource spread; no
completed infinite process is used as an extra premise.

The companion `PAST-RESOURCE-OMISSION-CONTROLS` fixes two assignments on the
same integer grid. Exponential stock `exp(t)` has lower bound zero and a
strictly positive increase at every past step, but no uniform positive minimum
increment. Linear stock `t` has uniform unit growth but no past lower bound.
These controls compose the main constraint with independently proved positive
properties of each assignment; no limit-of-increments theorem or physical
realization is claimed. Thus positivity or monotonicity alone cannot replace
the uniform-rate hypothesis, and uniform growth alone cannot replace the
resource bound. The controls do not establish minimality of every formal
premise, or prefer rejecting one particular condition.

`Stock` is neutral terminology. Interpreting it as entropy or accumulated
expenditure requires separate justification of the whole-past lower bound,
common unit grid, and uniform strictly positive rate. None follows merely from
a finite period of observed positive changes, a name such as second law, or
causal well-foundedness. This result makes no empirical closed-universe,
cosmological-age or entropy-production claim. Extended/non-Archimedean resource
values and different temporal orders are outside the encoded profile.

The proof uses ordinary Mathlib integer/real order, backward natural induction
and Archimedean `exists_nat_gt`. The old exact natural-number unit-cost theorem
is orientation, not a consumed lemma. Relative to that discussion, there is
no finite **time** budget here; a finite **resource** spread and uniform
positive growth are the substantive restrictions instead. Their truth for a
physical application remains open. No causal-eventcoverage bridge was added.
Intended and actual root-premise delta: none.

## Strongest objection and strongest reply

**Objection (completion principle).** To *finish* a genuine task is to perform
its final constitutive act. But an omega-sequence of discrete acts has no
final indexed act. Therefore an omega-sequence cannot be *actually finished*.
The apparent limit at time 1 is at most a mathematical idealization; calling
it *completion* would assume exactly what the argument contests. If physical
operations require nonzero lower-bounded time, energy or causal resources,
the divergent-series case provides a further conditional barrier.

**Reply (limit completion).** A process can be specified through all of its
stages and an additional endpoint without any last stage. Convergent partial
sums show that the mere absence of a final term is not a mathematical
contradiction, and a stable observable output can have a coherent limiting
value. The objection must justify why *actual* completion requires a final
constitutive act, or why the necessary acceleration/resource demands are
impossible. Neither is established by the natural-number order alone.

**Surviving dispute.** Is this a sequence of genuinely separate performed
causal operations, or only a mathematical subdivision or description of one
continuous process? Can an endpoint state be actual without a last producing
event? Does an adequate explanation require a source beyond local operations?
Those are philosophical and potentially empirical premises. Keep an objection
alive when its strongest coherent opponent model survives.

## Connection to the causal-regress frontier

- [Grim Reaper analysis](causal-regress-and-grim-reapers.md) establishes an
  inconsistency from a **special firing rule** plus an unbounded deadline
  order. The inconsistent rule is not supplied by every supertask.
- **#310 (actuality)** asks whether simultaneous *per se*, essentially
  borrowed causal power can be active without an intrinsic source. That is not
  the same question as whether an omega sequence of *temporal* operations can
  have a limit endpoint.
- **#311 (explanation)** asks whether an infinite set of local transfers can
  be explanatorily sufficient. A convergent temporal series neither provides
  an explanatory source nor refutes one; mathematical convergence and
  metaphysical grounding must not be conflated.

The open bridges are: **SU-END** (must a completed causal task have a last
operation?), **SU-REAL** (can an omega sequence of distinct physical acts fit
in finite actual time?), **SU-OUTPUT** (which terminal-state semantics are
defensible?), and **SU-GROUND** (if such a sequence is coherent, what causes
or explains its actual completion?). None is closed by these mathematical
controls, and none presupposes Thomism.

## Three further formal countermodels

These strengthen the earlier controls without using hypothetical physics as
a Lean axiom. Their exact truth concerns the defined models, not their
physical or metaphysical interpretation.

### Each finite prefix is possible; the whole need not be

The inference

$$\forall n\,\Diamond\mathrm{CompletePrefix}(n)
\quad\Longrightarrow\quad
\Diamond\forall n\,\mathrm{CompletePrefix}(n)$$

is not valid merely as a quantifier manipulation. A countermodel has worlds
indexed by arbitrary **finite** capacity `k`, with prefix `n` feasible at
world `k` exactly when `n <= k`. For every `n`, choose world `n`; no one world
has unlimited capacity, because prefix `k+1` exceeds its capacity.

- **`SUPERTASK-FINITE-PREFIX-NONUNIFORM`:** the Lean theorem verifies this
  model. It is related in logical form to
  `LOGIC-QUANTIFIER-SHIFT-EACH-SOMETIME-NOT-INVALID` but uses **worlds and
  task lengths**, not that other theorem's beings and times.
- **Critical reply:** a world with genuinely unbounded capacity might be
  possible, or a finite-duration completed task might not require a
  finite-capacity world. The countermodel defeats the *inference from finite
  prefixes alone*, not the possibility of all supertasks.

### Each particular ball disappears; there is no uniformly empty tail

Consider the simplified two-in-one-out infinite urn. After finite stage `n`
the resident ball IDs are

$$B_n=\{n+1,n+2,\ldots,2n\};\qquad |B_n|=n.$$

Thus there are arbitrarily many balls at finite stages. Nevertheless, any
fixed ball `b` is absent after stage `b`. Define the pointwise membership
limit by the eventual membership of each fixed identifier: that limit is
the empty set. This is **not** the same assertion as saying some finite
stage is followed only by empty urns:

$$\forall b\,\exists N\,\forall n\ge N:\ b\notin B_n,$$

$$\neg\exists N\,\forall n\ge N\,\forall b:\ b\notin B_n.$$

- **`SUPERTASK-URN-POINTWISE-NONUNIFORM`:** the Lean result verifies the
  eventual absence of each ID, the existence of arbitrarily long blocks of
  distinct residents at finite stages, and the absence of any uniformly
  empty tail. The explicit cardinality formula `|B_n|=n` above follows by
  elementary counting; that numerical identity is *not* the advertised Lean
  theorem.
- This is the same logical phenomenon as the well-known Ross–Littlewood urn
  with ten insertions and one removal per stage, for which the finite count
  would be `9n`. The Lean model deliberately uses two insertions to keep the
  foundational argument small. It must not be misreported as a historical
  source reading without a materialized witness.
- **Critical reply:** one may define terminal membership pointwise, but that
  does not prove a real urn could execute the operations or that a terminal
  state has been physically caused. The finite counts and pointwise set
  limit answer different questions; taking cardinality and limit in opposite
  orders need not give matching outcomes.

### No bounded observation prefix settles every stable limit

For any finite cutoff `k`, consider two streams:

1. `false` at every stage;
2. `false` through stage `k`, then `true` at every later stage.

Both have stable but *different* terminal values, while an observer with only
the first `k+1` outputs cannot distinguish them.

- **`SUPERTASK-FINITE-OBSERVATION-UNDERDETERMINED`:** the Lean theorem
  constructs these streams for arbitrary `k`. It **does not** say the result
  of a fully specified, computable stream is unknowable; the generating rule
  is information the finite observer is expressly missing.
- Infinite-time Turing machine models explicitly add a rule for their
  ordinal **limit stages**. Ordinary finite successor transitions do not on
  their own supply that rule. A stipulated limit rule can be coherent without
  being physically executable.

## Next investigations: conditional objections, not assumed impossibilities

| Angle | Mathematical or physical observation | Unresolved bridge or counterexample |
| --- | --- | --- |
| **Accumulation and local finiteness** | Every infinite set of distinct event times in a compact interval has an accumulation point. If physical events must be locally finite (only finitely many occur in each sufficiently small neighborhood), an infinite set of such events in finite time is impossible. | **SU-REAL:** why should *genuinely distinct causal operations* be locally finite? Points of a continuous trajectory are not automatically separate performed acts. |
| **Bounded distinguishable transitions** | Quantum bounds such as the Margolus–Levitin bound restrict the rate of orthogonal state transitions given suitable finite energy and isolation assumptions. | **SU-REAL:** is each task step a distinguishable orthogonal transition, and are the energy/system assumptions met? It is not a ban on continuous nonorthogonal changes or all imaginable physical models. |
| **Scheduling/order sensitivity** | Conditionally convergent series can acquire different ordinary sums under reorderings; absolute convergence is stronger. | **SU-OUTPUT:** a physical proposal must specify operation order and which terminal observable is being summed, not assume convergence guarantees order independence. |
| **Conservation through a limit** | Idealized Newtonian infinite-collision examples obey local collision rules but challenge global conservation or determinism at an accumulation point. | **SU-REAL / SU-GROUND:** which continuity and dynamical laws apply at the boundary? Rival accounts of what makes a legitimate Newtonian system must be compared. |
| **Extra boundary laws** | A finite-step transition rule may be silent on a new limit-state transition; explicit ordinal-time computation supplies additional semantics. | **SU-END / SU-OUTPUT:** is the extra endpoint law constitutive, derived, arbitrary, or physically justified? A bare undefined endpoint is not a contradiction. |
| **Time orientation versus essential causal dependence** | A future omega series accumulating at a terminal time, a beginningless past (reverse omega order), and a simultaneous essentially ordered dependence structure are distinct. | **SU-GROUND:** no impossibility for one order transfers automatically to another. In particular, #310 actuality and #311 explanation need separate grounding arguments. |

### Reading leads, not yet pinned corpus evidence

- J. F. Thomson, *Tasks and Super-Tasks* (1954), for terminal-state and
  successive-operation questions:
  [original paper](https://personal.lse.ac.uk/robert49/teaching/ph103/pdf/Thomson1954a.pdf).
- J. D. Hamkins and A. Lewis, *Infinite Time Turing Machines*, for explicit
  ordinal limit-stage semantics:
  [original paper](https://arxiv.org/abs/math/9808093).
- N. Margolus and L. B. Levitin, *The Maximum Speed of Dynamical Evolution*,
  for finite-energy bounds on distinguishable transitions:
  [original paper](https://arxiv.org/abs/quant-ph/9710043).

These are orientation references, **not source-derived claims** in the
canonical corpus. Historical/physical readings need pinned passages and
separate source-fidelity review before being treated as evidence for a
specific metaphysical premise.

## Frontier effect and next obligation

The three new results are premise-free **countermodel/control results**.
They close their *own* stipulated mathematical propositions once Lean and
Comparator have verified them, but none discharges `SU-END`, `SU-REAL`,
`SU-OUTPUT` (as a universal metaphysical claim), or `SU-GROUND`. No new
argument connects the model propositions to
`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` or the root
`STMT-CATHOLICISM-TRUE` without a new bridge.

The next philosophical target is a **completion principle** with independently
defended meanings of *operation*, *actual performance*, *terminal result*,
and *completed process*. Competing candidates should be tested against the
abstract limit model, the urn, the finite-observation example, physical
resource constraints, and beginningless/reverse-order cases. We are closing
invalid lines of reasoning and mapping dependencies; we have **not** yet
proved that completed supertasks or infinite causal chains are impossible.

For an additional step from temporal limits toward **essentially borrowed
power**, see the escaping-source finite-grounding model in
[causal regress and Grim Reapers](causal-regress-and-grim-reapers.md). Every
finite truncation of that model has a genuine source, while the pointwise
all-active limit retains no intrinsic source. It supplies a counterexample
to *grounding automatically commuting with a limit*, not an identification
of mathematical activity with real metaphysical causal power.

## Seriality of strict and inclusive past

[PastSerialityCertificate](../TruthCore/Modal/PastSerialityCertificate.lean)
connects the existing abstract modal frame to an explicitly temporal
interpretation. For a supplied `Preorder T` and `now`, take only the times
`t = now ∨ t < now`; let `t` access `s` when `s < t`. Transitivity keeps earlier
witnesses inside this subtype. Seriality is then exactly the existing
`PastIsInfinite (<) now` condition. Composing the existing generic D
correspondence gives the same equivalence for one-atom D validity under every
valuation. Adopting D for that strict-past frame therefore adopts a no-first
past condition; it does not independently prove that condition.

By contrast, inclusive accessibility `t → s` iff `s ≤ t` is reflexive and
serial, validating T and D. Nat with `now = 0` has an earliest time and no
strictly earlier witness, while its inclusive frame still validates those
axioms. The checked control separates these interpretations rather than
changing either axiom. An earliest time is not finite elapsed duration or
finite event cardinality. No physical time order, event population or
cosmological premise follows from the abstract mathematical correspondence.
These time-index frames are not an identification of modal alternative
histories with times, nor an interpretation of accessibility as causal edges.
Intended and actual root-premise change: none.

## No first moment need not mean unbounded clock age

[BoundedMetricPastControl](../TruthCore/Modal/BoundedMetricPastControl.lean)
uses the standard real interval `(0,1]`, with `now = 1`. Every admitted point
`t` has the earlier admitted point `t/2`, so the original `PastIsInfinite`
predicate holds and the original earliest-time `PastIsFinite` predicate fails.
Yet every clock age `1-t` lies in `[0,1)`. All these properties hold jointly
for one specified interval, rather than in separate interpretations.

This mathematical control separates absence of an earliest moment from
unbounded age in the chosen real clock. It does not establish physical
realization or that this clock represents cosmological duration. The existing
convergent Zeno schedule instead has a first stage; it is not substituted for
this no-first profile. Neither result infers finite event cardinality from a
finite metric bound. The interval is also not the integer unit grid of the
bounded-resource argument; a uniform resource increment on every integer step
is a separate hypothesis. Intended and actual root-premise change: none.

## When a stage must leave a reliably readable state (#1859)

**Provisional assessment (2026-11-25).** Finite generator action gives a
physical reason to exclude an infinite sequence of uniformly readable
updates of one closed quantum memory, even when adjacent states overlap.
The relevant observation is the reader's advantage over guessing which of
two adjacent states it received. A task that requires only a terminal value
or a continuous change need never produce such an advantage. This extends
the orthogonal-transition test in the [issue checkpoint](https://github.com/moritzbrantner/truth-core/issues/1859). [Assessment record](../corpus/attempts/analytic-supertask-limit-declaration.json)

### What the reader gets

Fix one device, its physical clock and an ordered list of sampling times.
For each adjacent pair, tell the reader which *pair* is under test. In
repeat trials present one copy of the earlier or later internal state with
equal probability. Hide the choice, sampling time and preparation command.
Use the same readout for both alternatives within the pair. The readout
may vary between pairs. Score every trial, assigning a fair guess on a
missing or inconclusive record. Estimate the success probability on fresh
trials after fixing the decoder. With unequal priors even a constant guess
can beat one half. Repeated preparations estimate single-shot performance;
pooling copies to decide each individual trial tests a different resource.

Let the two record distributions be P and Q. If the decoder reports
“later” on a set B, its success probability is
`p = (1 + Q(B) − P(B))/2`. Thus success of at least `1/2 + ε` requires
total variation distance `TV(P,Q) ≥ 2ε`. A binary record suffices. Waldherr
and colleagues prepared two nonorthogonal states of a single nitrogen
nuclear spin and measured correct, wrong and inconclusive identifications
as a function of their overlap. This gives an experimental procedure for
testing readability for individual pairs. It supplies no uniform guarantee
over an infinite schedule and no measurement of that schedule's action.
[Experimental protocol, Eq. (7) and Fig. 3](https://arxiv.org/pdf/1206.0453)

### How much action a readable pair requires

For a finite-dimensional memory, a binary readout has an effect
`0 ≤ E ≤ I`. Its change in “later” probability is
`Tr[E(ρ₁ − ρ₀)] ≤ D`, where `D = ‖ρ₁ − ρ₀‖₁/2`: the traceless difference
has positive eigenvalues summing to D, and projection onto their subspace
attains the bound. A fixed instrument with a fresh, uncorrelated auxiliary
system likewise induces an effect on the memory. For pure endpoints,
`D = √(1 − |⟨ψ₀|ψ₁⟩|²)`, as also follows from the equal-prior minimum-error
formula. The shortest ray distance in the convention of the issue is
`2 arccos |⟨ψ₀|ψ₁⟩| = 2 arcsin D`. Hence for a differentiable unitary
trajectory on this same memory, each tested pair with advantage
`εₙ ∈ [0,1/2]` consumes at least `ℏ arcsin(2εₙ)` of integrated energy
standard deviation. The Hamiltonian may vary with the physical time used
in the integral. [Anandan–Aharonov, Eqs. (1)–(6)](https://www.tau.ac.il/~yakir/yahp/yh64)

For disjoint successive intervals within one action budget
`A = ∫ ΔH(t) dt < ∞`, every finite prefix satisfies

$$
\hbar\sum_{n<N}\arcsin(2\varepsilon_n)\le A.
$$

A memory specified to score at least 75% on every pair therefore allows
at most `⌊6A/(πℏ)⌋` such transitions. Perfect discrimination recovers the
orthogonal cost `πℏ/2`. Even with a changing specification, an infinite
sequence requires summable advantages since `arcsin x ≥ x` for `0 ≤ x ≤ 1`.
A finite test establishes performance only on its tested pairs. The
exclusion concerns a task specification requiring that performance at
*every* stage within the one budget. Calibration can sample an endpoint on
a separate run. If the task measures during evolution, its measurement and
reset dynamics must be included in a justified action bound, for example
for a specified larger closed system.

The metric argument also applies to classical internal distributions: one
common stochastic readout per pair contracts total variation (the chance
of a “later” report is the expectation of a function valued in [0,1]).
Finite total variation of the internal path then bounds twice the sum of
the achievable advantages. The remaining variation on successive intervals
tends to zero, so optimal adjacent-pair success tends to one half. The
sampled states are Cauchy and have a limit if the metric space is
complete. No endpoint act or admitted endpoint state is needed for the
count. A classical variation budget needs its own physical warrant.

### Two controls and the causal application

* **A clock can supply the entire score.** Hold the internal state fixed
  and stamp the record with the externally selected early/late bit. The
  reader scores 100% while the internal distance is zero. A matched
  control can quantify this confound. Keep the decoder, timing, settings
  and apparatus preparation of each arm fixed, but present the earlier
  state in *both* arms. If the original and control scores are p and q,
  only the later-arm probability changes. Its fixed binary effect gives
  `2(p − q) ≤ D`. A reproducible positive excess therefore still gives a
  lower bound on the internal state displacement, even with arm-specific clock information. This comparison requires
  reproducible states and an unchanged readout channel within each arm.
  An intervention that also changes the apparatus or its correlations
  with the input fails that test. A joint system and clock record can
  instead be studied with an action budget for that joint system.
* **Weak changes survive finite action.** In clock units with interval
  length one, take `ψ(t) = cos(t)|0⟩ + sin(t)|1⟩` generated by
  `H = ℏσᵧ`. Here `ΔH = ℏ`. At the existing Zeno times
  `tₙ = 1 − 2⁻ⁿ`, every adjacent pair differs and the best possible
  advantage is $\sin(2^{-(n+1)})/2$. These advantages are positive, summable
  and tend to zero. One bounded, continuous rotation realizes the state
  trajectory in the model. Individuating infinitely many performed acts
  or separately controlled pulses would require further evidence.

**Transfer to the Second Way.** A successful blind readout distinguishes contents. An
occurrence also has a bearer and interval, and two occurrences can share
the same transition. For any proposed effect, locate its actual upstream
bearers in the selected respect. To use the count, show how the relevant
causal links require distinct, nonoverlapping, reliably readable updates
of one system on one physical clock within its budget. A controller or
parallel bearer outside that boundary can contribute to the effect without
causing a separate transition of this memory. The existing negative-integer
clock model also permits unbounded ancestry across intervals.
[Occurrence identity](../TruthCore/Causality/EventIdentityProfiles.lean) ·
[Compact-clock and ancestry controls](../TruthCore/Causality/OperationLocalFiniteness.lean)

In particular, result `d09f6268` needs, **for every effect**, finite
coverage of the selected fact labels of *all* its per se ancestors,
including the effect itself. Bounding updates along one observed path
does not cover other branches. To supply that premise by this route,
exhibit, for each effect, coverage of those labels by its own finite
roster of records with a specified label per record (including the
effect separately if needed). Preserve the same cause relation, dependence
respect, strict-ground mapping and consistent theory used in the result.
Reopen the transfer when a proposed device or argument identifies those
upstream bearers and explains why their contributions require such
records. The present operational test supplies a conditional SU-REAL
objection for readable serial memories. It supplies no premise discharge
for `97f5850f` and no verdict on simultaneous dependence or Reaper
recombination in general. [Exact local-label premise](../TruthCore/Causality/StrictGroundRepresentation.lean)

## Research attempts citing this note

- [Bounded owner-approved resource slice after read-only infinite-past audit; clean base a6648878](../corpus/attempts/bounded-past-resource.json)
