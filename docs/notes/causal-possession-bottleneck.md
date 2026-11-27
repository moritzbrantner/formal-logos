# Causal possession: the shared bottleneck "nothing gives what it does not have"

First checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143):
the curation pass connected many verified results to the root, and research now
turns to the warrant of the open premises that the most God-existence and
divine-attribute routes share. Baseline: main `03c3fd7ad` (merge of #2154).
The computed ranking that selected this family is recorded in
[the dependency map](spine-dependency-map.md#bottleneck-ranking-for-the-warrant-phase-2026-11-27).
[Attempt record](../../corpus/attempts/40645dd9-6ec0-46ec-aead-f3c98922d820.json) ·
[Batch spec](../../specs/more-such-sense-collapse.toml) ·
[Lean vocabulary](../../TruthCore/Causality/MoreSuchSenseCollapse.lean) ·
[Lean results](../../TruthCore/Results/Causality/MoreSuchSenseCollapse/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no
theorem, Challenge, claim, definition, frontier rule or closure. It is
**unreviewed** until the independent semantic challenge recorded in the PR.

## 1. Which premise is actually load-bearing

`truth bottlenecks` ranks "nothing gives what it does not have" (`376d6a5a`) first
on the Catholicism root (all 28 routes, 10 of 16 stage-one and all 10 stage-two
stage routes) and among the first on the GOD_4 root (16 of 20 routes). Two
features of the computation make the unrestricted maxim look more central than
it is:

- **Strength-order expansion.** The distinct-cause version `2c0b9bd7` is derived
  in the registered graph only by the strength application `777d3b8d`
  (unrestricted ⇒ distinct-cause) and by the cycle through "more such"
  (`9e7de16d`, which needs `d5a94eb1`, which is derived only from `2c0b9bd7` or
  `376d6a5a`). Under strict expansion every derivation therefore bottoms out in
  `376d6a5a`, although no route consumer uses its self-causation case: the frozen
  `924302df` records in `strong_version_needed` that its proof uses the principle
  only for distinct causes.
- **Stated leaves expanded through their derivations.** The routes carry the
  family as proved leaves: "more such" `d5a94eb1` (nine routes), "grades have a
  maximum" `6c27657f` (eleven), "nothing moves except as in act" `f296a694`
  (three, plus the prima via `ed7c588a` below its leaves), and preexistence
  `64498e7e` with `c11369aa` (one). Each of `d5a94eb1`, `6c27657f` and
  `f296a694` also has a direct option on its stating claim. A route needs the
  possession family only on the derivations of those leaves.

So the substantive node is the **possession family**: the distinct-cause
principle `2c0b9bd7` (whose unrestricted and cause-of-being versions `376d6a5a`
and `d0fc96b7` share its warrant), together with the comparative package that
turns possession into "more such": the reception bundle `a9036c3c`, `cdb79aa6`,
`39a4c28c`, `d0b76fb9`, the exceeding step `7030af77` and "what is more such has
the perfection" `c11369aa`. The four GOD_4 routes outside it are the two
definitional transcriptions (`0489c24b`, `4f71236b`) and the two
grades-at-being-only routes (`3367bf93`, `fc46b7f9`). Esse-only consumers can
also avoid the family: `cffad050` (a distinct cause of a thing's being is more in
being) has a transfer-free derivation from `4ccb319f` and the reception bundle at
esse (`causeOfBeingMoreInBeing`).

## 2. Fixed meanings

- `DistinctCauseHasWhatItGives CausesIn InAct` (`2c0b9bd7`):
  `∀ c x r, c ≠ x → CausesIn c x r → InAct c r`. `CausesIn` is CAUSE_2
  (DEF-CAUSE-OF-PERFECTION: effective causal responsibility for x's being r, which
  may run through secondary causes). `InAct` is one parameter. The statement's
  recorded reading is inclusive: IN_ACT_3, formally or virtually.
- The act senses of DISAMB-IN-ACT: IN_ACT_1 formal (`ActFrame.InActFormally`:
  the same form in which the cause produces it), IN_ACT_2 virtual
  (`ActFrame.InActVirtually`: "in a higher way, as a power to produce it"),
  IN_ACT_3 their disjunction. The new sibling statement `26632e48` is the IN_ACT_1
  reading of `2c0b9bd7`; `25b67649` is its exact negation.
- **An open sub-fork inside IN_ACT_2.** Its definition joins two determinations
  that come apart. *Power*: c has r virtually when c has an active power whose
  exercise produces r. *Containment*: c has r virtually when c formally has some
  higher perfection s that includes r's positive content (independently of
  whether c produces r). This checkpoint does not register the sub-fork; its
  results hold for any single act predicate, so they do not depend on it. The
  judgment below uses it only where it states so.
- `MoreIn r c x` is MORE_1, the primitive comparative, with no order structure.
  Two comparatives matter here: the **ordinary** comparative ("hotter" as a
  thermometer orders bodies), which is the reading of the paraphrase of
  `d5a94eb1` ("the cause of another's heat is hotter"), and an **eminent**
  comparative on which a cause that has r virtually counts as more r than the
  recipient. No record specifies the eminent comparative.

## 3. The formal results

- [`moreSuchPackageForcesFormalPossession`](../../TruthCore/Results/Causality/MoreSuchSenseCollapse/Solution.lean)
  (statement `97a338be`, premise-free). For **every** single act predicate
  `InAct` shared by the possession premise and the exceeding step: distinct-cause
  possession in `InAct`, the four reception premises, the exceeding step in
  `InAct` and the more-such bearer `c11369aa` **read with formal act** imply formal
  distinct-cause possession. It composes the registered
  `moreSuchOfDistinctCauseGives` (at `InAct`) with `distinctCauseGivesOfMoreSuch`
  (at formal act). The two registered steps leave their act predicates
  unconstrained; when they differ, the cycle turns eminent possession into formal
  possession.
- [`controls`](../../TruthCore/Results/Causality/MoreSuchSenseCollapse/Solution.lean)
  (statement `84ba508d`, a structural surrogate). Two beings (source, recipient),
  two respects (being, heat); the source causes the recipient's heat; only the
  recipient is formally hot; the source has heat virtually; the recipient's heat
  is received in and limited by the recipient. With the ordinary comparative
  (the recipient is hotter), the formal gap `25b67649`, inclusive possession, the
  four reception premises and the formal more-such bearer hold, while the
  inclusive exceeding step `7030af77`, "more such" `d5a94eb1` and formal
  possession `26632e48` fail. With the eminent comparative on the same causes,
  acts and reception, the whole package holds at inclusive act and only the
  formal more-such bearer fails. Disclosed artifacts: reception and limitation
  coincide; nothing causes the respect of being; the eminent comparative is
  stipulated, not derived from any measure.

Both are verified (`scripts/verify-result.sh`: Comparator and NanoDa accept).
Neither asserts a member of the package.

## 4. The negated-premise test

**The denial, with its original scope.** `25b67649`: some c, distinct from x,
causes x's being r and does not have r formally.

**Positive warrant for the denial: actual cases.** Induction heating: a
water-cooled copper coil carrying alternating current heats a steel workpiece
far above the coil's own temperature (engineering practice; Rudnev, Loveless and
Cook, *Handbook of Induction Heating*, is navigation only and was not read for
this note). The coil is effectively responsible for the workpiece's heat, so it
is a CAUSE_2 cause on the recorded definition, and it is not formally hot to
that degree. The case does not rest on counting instruments in general: in a
hydroelectric supply the principal causes upstream (turbine, generator, falling
water) are not formally hot either. Rumford's cannon-boring trials are a second,
documented case: a blunt, mechanically driven borer brought water to the boil
([productive-store note](productive-store-1378.md#when-does-finite-output-require-a-particular-feed),
which records the primary report's locators).

**What the rival commits to.** The denial of formal possession commits only to
production by causes that lack the produced quality in the same form. It is
compatible with inclusive possession (the coil has heat virtually on either
determination of IN_ACT_2: it has the power to heat, and on a containment
reading its electromagnetic energy contains the heat it supplies). It conflicts
with no accepted floor item, with none of its own commitments and with no
precondition of inquiry that this checkpoint could identify.

**What discriminates.** Formal possession and the formal gap make opposite
predictions about the coil, and the observation decides between them under the
recorded meaning of CAUSE_2. By `moreSuchPackageForcesFormalPossession`, the
same observation decides against every reading of the package that combines
**any** single act predicate in the possession premise and the exceeding step
with the formal more-such bearer: some member of that package is false of the
case. The control shows which member fails under each comparative in one
interpretation: with the ordinary comparative, the exceeding step (and with it
"more such"); with the eminent comparative, the formal more-such bearer.

**Substantive Objection Standard, both sides.**

| Target | Record | Classification |
| --- | --- | --- |
| Formal possession `26632e48` | The induction and Rumford cases | **Kept, established case**, conditional only on CAUSE_2 counting the coil (or borer) as a cause of the heat, which the recorded definition does. Mechanism: energy is transferred by induction (or by mechanical work), not by a hotter body. |
| "More such" `d5a94eb1` on the ordinary comparative | The same cases: the cause is not hotter | **Kept, established case** for the unrestricted Posterior Analytics I.2 reading. Metaphysics II.1's sourced restriction to synonymous causes (STMT-SYNONYMOUS-CAUSE-OF-QUALITY-IS-AT-LEAST-AS-SUCH) is untouched: the coil is not a synonymous cause of heat. |
| Exceeding step `7030af77` at inclusive act with the ordinary comparative | The same cases, through the control's first table | **Kept**, under that pair of readings only. At formal act its antecedent fails for the coil and the case does not touch it. |
| Inclusive possession `2c0b9bd7` on the power determination | Candidate: a cause that produces r with no power to produce r | **No substantive objection identified.** Actual production is the standard evidence of an active power. The Humean regularity view deflates powers but can accept the deflated ascription; occasionalism denies that creatures cause, which leaves the conditional untouched. |
| Inclusive possession `2c0b9bd7` on the containment determination | Capacity or law-mediated production (modal-spine row 14) | **Restated**, unchanged: a positive conceptual alternative, not evidence that production without containment occurs. No case discriminating containment from capacity is on file. |
| Instrument objection (modal-spine row 12) | Chisel and shape | **Unchanged, kept conditionally.** Whether it is answered on the power determination depends on whether IN_ACT_2's power includes the transient instrumental power of a tool in use (ST III q.62 a.4, unread here) or only the principal agent's own power; that is the open sub-fork of §2. |

No further objection is recorded. In particular no objection is raised against
the reception bundle: it holds in the control, and nothing here bears on it.

## 5. Strongest positive warrant

| Reading | Strongest positive warrant | Independent of the others? |
| --- | --- | --- |
| `2c0b9bd7` inclusive, power determination | Close to a meaning postulate: an actual cause of r can produce r, and on this determination having r virtually is just having that power. Prima facie strong; it carries little load, because it says no more about the cause than its causing already says. | Shares the form of its warrant, an inference from a cause's exercise to what the cause is, with the agency-in-act premise `ef068f46` (a cause of being is in act in some respect). They are different propositions; a defeat of that inference form would reach both. |
| `2c0b9bd7` inclusive, containment determination | Two independently specified cases: at esse, where every perfection is a mode of being (q.4 a.2 co.) and the cause-of-being ladder `d0fc96b7` ⇒ `4ccb319f` applies; and conserved quantities in physics, where a cause gives no more energy than it has. For arbitrary perfections without a common measure no specification of "contains" is on file. | The esse case is the warrant of `d0fc96b7`, not an additional one. |
| `26632e48` formal | Ordinary synonymous generation (fire heats, man begets man) and Metaphysics II.1 for synonymous causes. | These are the scope of the sourced synonymous premise, not of the unrestricted formal reading. |
| `d5a94eb1` and `c11369aa`, uniform eminent comparative | Survives the cases (control, second table). Its only positive rationale is the Thomist account of eminence. | Same missing specification as the recorded degree-calibration gap (`fd2c8710`, `9eaa3b6e`; [causal-perfection-transfer note](causal-perfection-transfer.md#d-overall-provisional-judgment-revision-conditions-and-next-test)). |
| `376d6a5a`, `d0fc96b7` | Unchanged: no independent warrant beyond `2c0b9bd7` (with `67aa5b5c` for the self-causation case) and the esse ladder. | Strength siblings of one principle. |

## 6. Provisional judgment (2026-11-27, unreviewed)

1. **The formal reading of possession is contradicted by actual cases** under the
   recorded meaning of CAUSE_2. It is not a candidate for the routes' reading.
2. **Inclusive possession `2c0b9bd7` is strong prima facie but light.** On the
   power determination it is near-analytic and no substantive objection is
   identified. It then adds almost nothing to what causing already gives: on that
   determination the comparative steps downstream must do the work.
3. **The comparative package is where the weight sits.** On the ordinary
   comparative, "more such" `d5a94eb1` and the inclusive exceeding step
   `7030af77` are contradicted by the same cases. On a uniform eminent comparative
   the package survives them, but then (a) `c11369aa` must be read at inclusive
   act, (b) "more such" delivers only eminent comparison and inclusive possession,
   and (c) its warrant is the specification of the eminent comparative, which no
   record supplies. That is the same gap as the degree calibration.
4. **The mixed reading is excluded.** Eminent possession with a formal more-such
   bearer and the package is inconsistent with the observed formal gap
   (`moreSuchPackageForcesFormalPossession` with `25b67649`). A route that reads its
   possession premise eminently and its more-such bearer formally is committed to
   a falsehood about the cases.
5. **`376d6a5a` is unchanged**: avoidable and without independent warrant. Its
   first place in the computed ranking is an artifact of strength-order expansion,
   not evidence that the routes need its self-causation case.

This is the first grade for `2c0b9bd7`, `26632e48`, `d5a94eb1` on its two
comparatives and `7030af77` at inclusive act. It declares no revision. The
earlier records it touches stay as they were: modal-spine rows 12 to 15 and their
"not graded" standing of `376d6a5a`, the 2026-11-12 reconciliation draft's
capacity rival, and the calibration blocker.

**Revision conditions.**

- An independent specification of the eminent comparative that makes
  `7030af77` and `c11369aa` jointly true at inclusive act, without defining
  eminence as the power to cause, would strengthen the package at arbitrary r.
- A restriction of CAUSE_2 that excludes coil- and borer-type causes, with a
  rationale other than saving the principle, would reopen the formal readings.
- A consumer audit showing that the route consumers (`c201b61a` for `6c27657f`,
  `a31b3e52`/`924302df` for `d5a94eb1`, `d0c022f8` for `f296a694`) need only
  inclusive possession and an inclusive bearer would confine the defeat of the
  formal readings to readings no route uses.
- A case of production without any power to produce would defeat the power
  determination.

## 7. Shared-warrant map

Count once:

- `376d6a5a`, `2c0b9bd7` and `d0fc96b7` are one principle at three scopes.
- `2c0b9bd7` and `d5a94eb1` derive each other through `c11369aa` and the
  reception bundle (`9e7de16d`, `a31b3e52`). The cycle adds no warrant to either;
  its only external inputs are the stating claim of `d5a94eb1` (Posterior
  Analytics I.2) and whatever warrants `2c0b9bd7` directly.
- The prima via's "nothing moves except as in act" (`f296a694` via `d0c022f8`)
  uses `2c0b9bd7` at inclusive act and neither comparative; the
  grades-to-a-maximum route (`6c27657f` via `c201b61a`) uses `2c0b9bd7` and
  `c11369aa` at one act predicate; the maximal-cause routes use `d5a94eb1`. These
  look like independent ways (motion, grades, causal maximum) but share this one
  family. Their support for GOD_4 must not count it more than once.
- The eminent comparative and the degree calibration (`fd2c8710`, `9eaa3b6e`,
  `98755509`) are one missing specification. The registered graph shows the
  same link from the other side: the exceeding step `7030af77` is itself derived
  (argument `1fbc8de7`) from the calibration premises `a961a13e`, `f6677834` and
  `9eaa3b6e`. So wherever the cases contradict `7030af77` (inclusive act, ordinary
  comparative), at least one of those three fails under the matching degree
  reading, and the route's exposure there is to the calibration family.
- The other inputs of the package are derived from the participation and
  dependence families: `a9036c3c` from `efe134d4` and `9da93cd4` (argument
  `5e42f97e`), `d0b76fb9` from `3e890700`, `e0088de9` and `47b151ca` (argument
  `29851dcb`). Those families are separate bottlenecks in the ranking; the cases
  here bear on none of them.
- On the power determination, `2c0b9bd7` shares the form of its warrant (from a
  cause's exercise to what the cause is) with the agency-in-act premise
  `ef068f46`; they are different propositions.

## 8. Next discriminating test

Run the consumer audit named in the third revision condition: for `c201b61a`,
`a31b3e52`, `924302df`, `d0c022f8` and the stage-two attribute bridges that use
the maximum's possession (for example of intellect), record whether each needs
formal possession, formal comparison or only their inclusive and eminent
counterparts, and whether its observed premise (the grades "found in things")
is formal. A consumer that needs formal possession at a perfection other than
being is refuted on its present package by §4. One that needs only inclusive
readings moves the burden to the eminent comparative. Then register the IN_ACT_2
sub-fork (power against containment) if a consumer needs containment.
