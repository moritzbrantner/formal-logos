# Caused movers and the commitment C\* on the prima via

This note owns the investigation of **C\***: a caused mover is itself being
moved, whenever it moves, in a respect relevant to that moving. The reviewed
lane-A assessment (PR #1768, accepted after an independent challenge, not yet
merged; attempt `a82b06b6` on that branch) located the absolute First-Way
conclusion's contested load in C\* and its three recorded forms. That
assessment is cited as in-flight evidence, not as established.

## 2026-11-19: meaning, unification, test cases and scope

**Target.** The prima via route to GOD_4 exists (`8626f8a5`), argument
`ed7c588a`; the absolute First-Way result `d337ab29` (theorem
`primaViaFromBeingInAct`) and the strong per se premise `1e47e6db`, which the
registered `927421e7` derives from the relevant-respect premise `96da1d33`
and the scope bridge `b3573a61`. The C\* forms: `b3573a61`; `f03798ba` with
`d791628f` and the stated `0628359b` (result `1e3a1278` derives `777646a5`
from them); and `8a22ae75`, the secunda-via twin, as its strengthening over
`446e3f2a`. The regress context is the per se regress `226c38f6` and lane B's
spine I (PR #1769, in-flight; its `d85de8e1` row reports that the regress
warrant is the instrumental reasoning of `1e47e6db`).

Baseline: main `df4909cb025d2e53fee6071a32defe9cf2721284`. Read: the Lean
bodies of every node named above (`Question2/Article3.lean`,
`Article3SecundaVia.lean`, `Question105/Article5.lean`, `MotionMapsBatch1.lean`,
`Physics.lean`), definitions `c9798301`, `55a974ea`, `4a101a4c`, `c195d490`,
`04cbb76b`, `45595dac`, `9f874532`, `a7904c82`, `211a6432`, disambiguations
CAUSE (`00e0d443`), PER-SE-LINK (`c097f626`), MOTION (`a59fd0ac`), POTENCY
(`508617ab`), `brief b3573a61`, `novelty`, and
[borrowed-exercise-741.md](borrowed-exercise-741.md), whose
instrument/secondary-cause distinction this section reuses.

Pinned passages materialized and read this session (`source_evidence.py
materialize`): Physics III.2 (`5e66eaa9`), III.3 (`d0e5f8bf`), the opening of
V.2 (`93c5b826`), ST I q.105 a.5 in the Dominican translation (`915df403`)
and ST I q.25 a.1 in Latin (`09369215`). Everything said of them below is an
analyst reading; no claim record is added. ST I q.54, q.77, De anima III.10,
Physics VIII.5 and VIII.10 and Aquinas's Physics commentary on III.3 were not
read and are not attributed.

### 1. The meaning the route needs

**The Lean shape.** `d337ab29` takes `SecondMoversMoveOnlyAsMovedReading`
(`1e47e6db`: `∀ y x r, y ≠ x → MovesIn y x r → (∃ r', MovedIn y r') →
MovesAsMoved y x`) and `NoInfinitePerSeMoverSeriesReading` (`226c38f6`:
`∀ x, Acc MovesAsMoved x`). `MovesAsMoved` is a primitive. Its intended
reading (DEF [c9798301](../../corpus/definitions/per-se-ordered-series.json))
is "a cause exercising derivative causal power causes only insofar as it is
sustained by an upstream cause", with a here-and-now reading left open. The
weak premise `96da1d33` adds `RelevantTo y x r r'`, glossed by DEF
[55a974ea](../../corpus/definitions/per-se-link-relevant-respect.json) as "bears
on its moving". `b3573a61` asserts that such a relevant respect always exists
when a distinct mover is moved at all.

**Three candidate senses of "itself being moved".**

1. **(i) Some change.** The mover undergoes some MOTION_1 reduction while it
   moves. This is the antecedent `∃ r', MovedIn y r'` and the content of
   `777646a5`. It does not make the moving derivative: the digesting man of DEF
   `55a974ea` is moved and moves the stick by his own power.
2. **(ii) Present enabling dependence.** The mover is being moved now, in a
   respect r', and its present moving of x in r depends on that: were it not
   being so moved, it would not now be moving x in r. This is the stick moved
   by the hand. It is #741's *instrument*: borrowed exercise with an actual
   lender.
3. **(iii) Originating dependence.** The mover received its power from another,
   which need not act now: the son begotten by a father, the heated iron taken
   from the forge. This is #741's *secondary cause*: retained power.

**Which sense the route needs: (ii).** The warrant for `226c38f6`, as lane B's
`d85de8e1` row also reports, is the instrumental reasoning: a link that has
power only as lent needs a present lender, so the lending cannot run on with no
lender. That reasoning concerns (ii). Under (iii) the series is a historical
succession. ST I q.46 a.2 ad 7 (claim `2e18db19`, reading B) treats such
accidentally ordered series as possibly infinite, and DEF `c9798301` excludes
the father/son succession from per se links. Under (i), the digesting man
would count as a per se link. So `RelevantTo` must carry (ii).

**Two readings of relevance.** "Bears on" splits:

- **R1, modulating:** y's being moved in r' affects how y moves x (degree,
  direction).
- **R2, enabling:** were y not being moved in r', y would not now be moving x
  in r at all.

Only R2 matches (ii). R1 also defeats itself on this route. Scratch control 2
below shows that R1 makes `96da1d33` with `226c38f6` inconsistent with any
reciprocal pair, because each party's being moved modulates its acting on the
other. The fixed meaning of C\* is therefore: **whenever a caused mover y moves
a distinct x in r and is being moved in some respect, it is being moved in some
respect r' that is R2-relevant (present-enabling) to that moving.** No DEF
records R1 and R2 separately yet. Splitting `RelevantTo` into two sense types
is a formal follow-up (section 8).

**The rival targets exactly this meaning.** The standing-power rival concedes
(i) and (iii) for its cases and denies (ii). It must concede (i): a standing
mover moved in no respect at all falls outside `b3573a61`'s antecedent. Such a
mover would itself satisfy `FirstUnmovedMoverCannotBeLackingReading`
(`¬¬ ∃ f, (∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r`). The Lean form of the
absolute conclusion is that weak before the naming bridge `a594d8c4` adds
`PureAct` and uniqueness. The rival's case must therefore be a mover that is
moved, but only in R2-irrelevant respects.

### 2. One commitment: the unified derivation (proposal)

New open statements, analyst formulations (no Lean declaration yet):

- `631e014f`: `f03798ba` without the God index. A mover whose being some other
  thing causes (`∃ c, c ≠ y ∧ CausesIn c y esse`) is, whenever it moves, in
  POTENCY_1 to an operation respect o of its own (`OperationOf y x r o ∧
  InPotency y o`). Its domain contains that of `f03798ba`, so it implies
  `f03798ba`.
- `7bf380c6`, **the bridge**: `∀ y x r o, MovesIn y x r → OperationOf y x r o →
  RelevantTo y x r o`.
- `e3afc8a3`: `b3573a61` restricted to caused movers.

Derivation: from `631e014f` obtain o with `OperationOf y x r o` and
`InPotency y o`. `d791628f` gives `ActualizedQuaPotential y o`; the stated
`0628359b` (Physics III.1) gives `MovedIn y o`; the bridge gives
`RelevantTo y x r o`. The antecedent `∃ r', MovedIn y r'` is not used. Full
`b3573a61` then follows classically, with one more input: a mover that nothing
else causes is moved in no respect. The 2026-11-17 esse-composition reasoning
in [prima-via-strength-consumers.md](prima-via-strength-consumers.md#2026-11-17-reducing-the-respects-through-the-source-of-esse)
supplies that input from `4be9a4ac`, `d8024a38` (with the POTENCY_2/POTENCY_1
alignment it records) and `ca07cae9`.

Both steps were checked in a scratch file outside the repository
(`unified`: no axioms; `full`: `propext`, `Classical.choice`, `Quot.sound`).
That file is not a corpus result. Registration and certification belong to the
formal owner.

Sense check. The installed `truth` binary has no `semantics` preflight, so it
was done by hand. MOTION_1 is used throughout (DEF `a7904c82`). `CausesIn` at
esse (CAUSE_2) only restricts the domain; `MovesIn` (CAUSE_1) is a different
predicate in a different position, so there is no passage between senses.
POTENCY_1 is the adopted sense (DEF `9f874532`) in both `631e014f` and
`0628359b`. A Lean registration should use `AdoptedPotency.InPotency` in both.

**What unification shows.** The bridge is exactly where relevance enters.
Without it, `631e014f`, `d791628f` and `0628359b` give only sense (i), which is
what `777646a5` asserts and what its consumer `74eb9113` (through `f8992ef7`)
uses. The first-being bridge therefore needs only (i), not R2. C\* proper is
`e3afc8a3`, with `b3573a61` its classical extension. Lane A's grouping of the
three forms as one commitment is confirmed for the derivation of `b3573a61`.
`8a22ae75` carries the same content in the efficient-cause vocabulary.

### 3. The discriminating test case

**The teacher and the fire are confounded.** A teacher teaches by speaking and
gesturing. Those are local motions of the teacher's own organs, and they are
R2-relevant: without them nothing is taught now. Whatever moves the will to
speak is a further question, recorded here as unassessed (De anima III.10 not
read). Fire heats by ongoing combustion, a present change in the fire without
which it would soon cease to heat. On sense (ii), both are moved in a relevant
respect, so neither tests C\*. The III.3 teacher passage
(202a21-b22, read) concerns *where* teaching is located, in the learner, as
the teacher's activity. It does not say that nothing in the teacher is moved
relevantly. It is therefore not, by itself, the rival's counterexample.

**A clean class: retained-state movers.** Two cases, both ordinary physics:

- **A hot iron laid on cooler wood.** It heats the wood (the wood is reduced
  toward heat by a being actually hot, as `6b9fedc2` requires). The iron is
  itself being moved: it is cooling, so it is being moved toward cold, partly
  by the wood. Its cooling is R1-relevant, since it lowers the heating, but not
  R2-relevant: were the iron not cooling, it would heat the wood still more.
  Nothing presently heats the iron (it is out of the forge). Its heating rests
  on a quality it retains in act. That is sense (iii) (#741 *secondary cause*),
  not (ii).
- **A thrown stone striking a target.** It moves the target. During impact it
  is being decelerated by the target, a MOTION_1 change of its state of motion.
  That deceleration is R1-relevant and R2-irrelevant. Its moving rests on
  momentum it retains. By the corpus's recorded boundary (lane A's objection
  table: uniform inertial motion is no MOTION_1 reduction on the state
  reading), nothing presently moves it in that respect.

The cases use the corpus's own physical instantiation of MOTION_1 (DISAMB-MOTION
admits quality change and change of motion state; DEF `a7904c82` restricts
neither to bodies nor to place). Reaction is present in both. It is assessed,
not ignored: it supplies the antecedent of `b3573a61` (the iron and the stone
are moved) and fails R2. Physics III.2 202a3-7 (read) states that a mover that
is itself movable acts by contact, "so that at the same time it is also acted
upon". On the analyst reading this supports the *antecedent*; it does not
support relevance. This settles lane A's open question whether III.2 is a
consideration in favour of C\*: it is not, on R2.

**The operation form under POTENCY_1.** `631e014f` (like `f03798ba`) requires
`InPotency y o`, which is `CanBe y o ∧ ¬ InAct y o`. A mover already in act in
every operation respect of its moving falsifies it. This is scratch control 1,
`steadyExerciseRefutesPotencyToOperation`, a fact about that interpretation.
The operation form fits successive operations, where the agent is still
acquiring o. A driven stick moving through place is the example. It does not
fit the iron's steady exercise of a retained quality. That exercise is the
second act of a power in act, not a POTENCY_1 to be actualized. DEF-POTENCY
itself excludes "a power possessed during its exercise" from POTENCY_1.

**Thomist replies, each under the objection standard.**

| Reply | Target and mechanism | Assessment |
| --- | --- | --- |
| T1. Concurrence: the creature's power is presently applied to act (ST I q.105 a.5 co. and ad 3, read: God "applies them to act") | The relevant present mover is the applier | God-indexed: it presupposes the being whose existence the route concludes. Its non-God-indexed content, that every creaturely exercise is presently *caused* by another, is a CAUSE_2 or sustaining claim, not MOTION_1 being moved. Under POTENCY_1 an exercise already in act is not being reduced (control 1). A sense bridge from "presently caused in its exercise" to "moved in it" would be needed and is not on file. Not available for C\*; see S below. |
| T2. Operation is an accident distinct from the power (ST I q.25 a.1 ad 2 and ad 3, read: in creatures power is a principle of action, and where act differs from power it is nobler; q.54 not read) | The exercise is a further actuality the agent has | Accepted as a distinction. It shows the exercise is a second act distinct from the first. It does not show that the agent is *being reduced* to it while it already exercises it. This is the gap between onset and steady exercise. |
| T3. Conservation of the retained quality | The iron's heat persists only as conserved | Conservation is not MOTION_1 (`0b9ad38b`, reused). It supports the sustaining option S, not C\*. |
| T4. *Virtus impressa*: the iron acts as instrument of the fire that heated it | Instrumental dependence on the original agent | That agent is not acting now, so this is sense (iii). It does not carry the regress warrant (section 1). |
| T5. Count the cooling as relevant | Relevance as R1 | Self-defeating on this route (control 2). |

Molinist simultaneous concurrence (concurrence on the effect, not on the
power) is a further theistic rival to T1's premotion reading. It is recorded
as navigation only: it was not read and has no evidential weight here.

**The rival's positive account, under the same standard.** *Target:* C\*
(`e3afc8a3`, `b3573a61`; `d791628f` and `631e014f` as its derivation).
*Mechanism:* a retained state in act moves another while the mover's only
present changes do not enable that moving. *Independent justification:*

- the two physical cases above;
- Physics III.3, 202a13-21 (read): the mover's actuality is the moved's
  actuality, located in the moved;
- III.3, 202a25-b8 (read): if acting were a motion in the agent, then "either
  every mover will be moved" or something will have motion and not be moved;
  the resolution is that the teacher need not learn;
- V.2, 225b10-16 (read): there is no motion in respect of agent and patient,
  or mover and moved, "because there is no motion of motion";
- control 1.

These are analyst readings of read text. Claim `849f4443` states only that
motion is in the moved, and it is not counted for more. *Relevance:* C\* carries
`1e47e6db` and hence `d337ab29`. *Established or hypothetical:* the physical
processes are established. Their description in the case's vocabulary uses
DISAMB-MOTION's physical instantiation and the inertia boundary. On R2 the
cases are established instances, not conceivable ones.

**Result of the test.** On the fixed meaning (ii)/R2, the retained-state movers
are a **kept counterexample class** to C\* (`e3afc8a3`, `b3573a61`). The
operation route that would support C\* (`631e014f`/`f03798ba` + `d791628f` +
`7bf380c6`) fails, under POTENCY_1, exactly for steady exercise. This is a
proposed claimed defeat of the universal premise. It awaits the coordinator's
independent semantic challenge and is not a formal refutation.

### 4. New: the strong premise and the regress exclude reciprocity

Scratch control 3 (`strongPerSeRegressExcludeReciprocity`, no axioms) shows
that `1e47e6db` and `226c38f6` together entail: **no two distinct beings each
move the other while each is being moved** (the checked form has each moved
in the respect in which the other moves it; the strong premise needs only that
each is moved in some respect, so the same proof covers any respects). Each
would be a `MovesAsMoved` link of the other, a two-cycle that `Acc` excludes. The iron and the wood are such a
pair; so is any contact interaction in which, as III.2 says, the mover is acted
upon. The new open statement `4f6ac439` records that observation premise. The
bundle {`1e47e6db`, `226c38f6`, `4f6ac439`} is therefore inconsistent. Like
every contradictory bundle, it forces the rejection of at least one member,
not of a preferred one.

Two consequences follow:

- **Whatever reading of `RelevantTo`, the strong route needs repair.**
  `96da1d33` with `b3573a61` gives `1e47e6db` (`927421e7`), so every reading
  that makes `b3573a61` true of the reciprocal pair restores the
  inconsistency. On R2, `b3573a61` fails of the pair (section 3); on R1, the
  bundle fails (control 2).
- **The weak route is consistent with reciprocity.** Scratch control 4
  (`weakPerSeRegressReciprocityModel`, a two-element interpretation) has
  `96da1d33`'s form, `226c38f6`'s form and a reciprocal moved pair together,
  with `RelevantTo` false of the pair. This is a fact about that interpretation
  only.

The natural repair is a series- or respect-indexed per se link: `y` moves `x`
in `r` as moved in an R2-relevant `r'`. Aristotle's stick, hand and man chain
is a chain for one motion; Physics VIII.5 was not read, so this is not
attributed. With that repair, the absolute conclusion again needs C\*.

The same proof pattern applies to the secunda-via pair `8a22ae75` and
`NoInfinitePerSeEfficientCauseSeriesReading` with two mutually efficient
causes. It was not separately checked. This also bears on the charity argument
of result `92d3129c` (AQUINAS-ST-I-Q2-A3-STRONG-READING-INTENDED): read
respect-free, reading A is inconsistent, with Aquinas's own regress claim, with
ordinary contact action. That is a consideration for reading B. It is not a
claim about what Aquinas meant.

### 5. Restricted scopes

| Restricted C\* | Warrant | Suffices for the route? |
| --- | --- | --- |
| Instruments and driven movers: y moves x by a change in it that another presently produces (the stick, a massless rod transmitting a present force) | Strong; near-definitional on R2 | No. The route then needs every moved mover in the chain to be such a mover, which is C\* again. |
| Onset: a caused agent passing from not exercising to exercising is reduced by another (`6b9fedc2`, `079b53bf`) | Moderate. T2 grants that the exercise is a distinct second act; the onset may instead lie in bringing agent and patient together | No. It gives being moved at onset, not present dependence during the series' time. |
| Caused movers only (`e3afc8a3`) | As C\* | No gain: the counterexample class consists of caused movers. |
| **S, the sustaining series:** re-read the per se link as "y's present moving of x would cease were its sustainer z not now sustaining y's power or being" (the removal test of DEF `4a101a4c`, *remota causa removetur effectus*), with no MOTION_1 being moved | Conditional on present conservation of caused beings (lane B's existential-inertia rival on `3ef67739` is the standing rival) and on lane B's regress spine | **Not for `d337ab29`.** It reaches a terminus whose being and powers are unsustained; the 2026-11-17 composition route makes that terminus free of potency in every respect. That terminus *sustains*; it does not `MovesIn`. The conclusion is a **sibling**: a first *mediate* mover, unmoved in every respect. It needs a new mediate-moving sense (direct `MovesIn` is not mediate moving; a bridge between them would be a sense passage) and a sense-indexed sibling of `d337ab29`. |

The retained-state movers are not dead ends under S: the iron's heating would
cease if the iron's being were not now sustained, so the series continues
through its sustainer. S thus answers the counterexample class at matching
scope by changing the link relation, not by denying the cases.

### 6. Competing explanations at matching scope

| Case | Thomist operation-as-actualization | Standing-power or retained-state | Sustaining reading S |
| --- | --- | --- | --- |
| Driven stick | Moved relevantly (its locomotion, produced by the hand) | Same | Same link |
| Teacher, fire | Moved relevantly (speech, combustion) | Agrees that those changes enable; locates teaching in the learner | Same |
| Hot iron, projectile | Needs T1 (God-indexed) or T3 (not MOTION_1); otherwise no present relevant mover | Moved only R2-irrelevantly; no present lender | Link to the sustainer of the iron's being |
| Reciprocal contact | The strong reading gives a two-cycle (control 3) | Consistent with the weak reading on R2 (control 4) | Sustaining links are not mutual (lane B's nonmutual-dependence premises; unassessed here) |

**Self-undermining or precondition considerations.** None was found on either
side. The rival does not rely on denying `6b9fedc2`: the wood is reduced by a
being in act. Nor does it deny the per se regress for instruments. The Thomist
position is coherent, but its universal premise is supplied here only in a
God-indexed form.

### 7. Overall provisional judgment

- **Fixed meaning.** C\* must be (ii)/R2, present enabling dependence. The
  rival targets exactly that and concedes (i).
- **Restricted C\* for instruments and driven movers: well supported**, but
  insufficient for the route. **Onset C\*: moderate**, and insufficient.
- **Universal C\*** (`e3afc8a3`, `b3573a61`), and the operation route to it
  (`631e014f` or `f03798ba` with `d791628f`, `7bf380c6`): **open, blocked by a
  kept counterexample class** (retained-state movers, section 3). Its positive
  warrant beyond Aquinas's own sentence (claim `095dc31a` on `1e47e6db`) is the
  concurrence reading, which is God-indexed. Provisional grade: **weak.** This
  is a proposed influential judgment change, for the independent challenge.
- **`777646a5` and the first-being bridge** need only (i). The counterexample
  class does not touch them: those movers are moved. Only one support of
  `777646a5`, the derivation `1e3a1278` through `f03798ba` and `d791628f`, is
  undercut for steady exercise. A direct option, that every caused agent changes
  in some respect while acting, is not assessed here.
- **The absolute First-Way conclusion `d337ab29` via this route:** a verified
  conditional consequence. Its premise pair (`1e47e6db` respect-free,
  `226c38f6`) is inconsistent with ordinary reciprocal action (section 4), and
  every repair needs C\*. Overall support through this route: **weak.** This
  proposes revising PR #1768's in-flight grade, "moderately supported, bounded
  by C\*". The relative conclusion (`e05d2976`) is unaffected and remains
  consistent with reciprocity on R2 (control 4).
- **What C\* uniquely carries:** the *direct moving edge* of an all-respect
  unmoved first being, and with it the motion-specific naming bridge
  `a594d8c4`. All-respect unmovedness of a first source is available through
  the 2026-11-17 esse-composition route, under its own premises. So C\* is
  crucial for the prima via's own absolute form, not for God's existence on
  the case as a whole.

### 8. Revision conditions and next tests

Revision conditions:

- A non-God-indexed argument that a retained-state mover is presently being
  reduced, in an R2-relevant respect, while it moves would reopen C\*. So would
  a defended physical analysis on which the hot iron or the projectile is not
  a MOTION_1 mover, or on which its reaction is enabling.
- A defended sense bridge from "presently caused in its exercise" to "being
  moved in it", consistent with POTENCY_1, would make T1's content usable and
  merge S into C\*.
- An account on which reciprocal contact is not reciprocal `MovesIn` under
  MOTION_1 would remove the section 4 inconsistency. Section 3 would stand.

Next tests:

1. **Philosophical, option S.** Compare at matching scope present conservation
   of caused beings (the removal test) with existential inertia, for the
   retained-state movers. Ask whether a mediate-moving sense can be defined
   faithfully, so that the terminus of a sustaining series counts as the first
   mover of the motion, without passing from direct `MovesIn`.
2. **Formal, for the formal owner:**
   - certify the unified derivation (`631e014f`, `d791628f`, `0628359b`,
     `7bf380c6` ⊢ `e3afc8a3`) and its classical extension to `b3573a61`;
   - certify control 3 as the inconsistency {`1e47e6db`, `226c38f6`,
     `4f6ac439`}, and its secunda-via analogue;
   - certify controls 1, 2 and 4 as registered models or controls;
   - split `RelevantTo` into R1 and R2 sense declarations with a
     disambiguation;
   - draft a series-indexed per se link.

### Records

New open statements: `631e014f-685d-434c-86b7-4a683a507b4d`,
`7bf380c6-fcdd-4b14-bae5-d5a5acdebd5c`,
`e3afc8a3-b51b-4f44-a093-ce27cf8e1f0a` and
`4f6ac439-627d-43f2-9364-2700cd4a49d2`. Attempt
`b7e7af8c-0b41-4431-aa40-0543408ddb9d`. No theorem, Challenge, claim,
definition, argument or formal status changed. Scratch controls 1-4 are not
repository evidence until registered.
