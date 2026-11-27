# Causal possession: the shared bottleneck "nothing gives what it does not have"

First checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143).
The curation pass connected many verified results to the root. Research now
turns to the warrant of the open premises that the most God-existence and
divine-attribute routes share. Baseline: main `03c3fd7ad` (merge of #2154).
The computed ranking that selected this family is in
[the dependency map](spine-dependency-map.md#bottleneck-ranking-for-the-warrant-phase-2026-11-27).

[Attempt record](../../corpus/attempts/40645dd9-6ec0-46ec-aead-f3c98922d820.json) ·
[Batch spec](../../specs/more-such-sense-collapse.toml) ·
[Lean vocabulary](../../TruthCore/Causality/MoreSuchSenseCollapse.lean) ·
[Lean results](../../TruthCore/Results/Causality/MoreSuchSenseCollapse/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no frontier
rule or closure, and it changes no theorem or Challenge outside its own batch.

**Review status.** An independent semantic challenge of PR #2166 at head
`30ca1de` accepted the judgment with qualifications: three P1 and seven P2
findings. It accepted both original Lean results, the cycle claim, the "no
price" classification of the rival, and the separation of judgment from
closure. This version repairs every finding ([§9](#9-review-repairs)) and adds
the consumer audit ([§6](#6-consumer-audit)). The repaired assertions await the
challenger's re-check.

## 1. Which premise is actually load-bearing

`truth bottlenecks` ranks "nothing gives what it does not have" (`376d6a5a`)
first on the Catholicism root and among the first on the GOD_4 root. It appears
in the expanded derivations of all 28 Catholicism routes and 16 of the 20 GOD_4
routes; direct options remain. Two features of the computation make the
unrestricted maxim look more central than it is.

**Strength-order expansion.** The distinct-cause version `2c0b9bd7` is derived
in the registered graph only in two ways:

- by the strength application `777d3b8d` (unrestricted ⇒ distinct-cause);
- by the cycle through "more such": `9e7de16d` needs `d5a94eb1`, which is
  derived only from `2c0b9bd7` or `376d6a5a`.

Under strict expansion every derivation therefore bottoms out in `376d6a5a`. Yet
no route consumer uses its self-causation case: the frozen `924302df` records in
`strong_version_needed` that its proof uses the principle only for distinct
causes.

**Stated leaves expanded through their derivations.** The routes carry the
family as proved leaves:

- "more such" `d5a94eb1` (nine routes);
- "grades have a maximum" `6c27657f` (eleven routes);
- "nothing moves except as in act" `f296a694` (three routes, plus the prima via
  `ed7c588a` below its leaves);
- preexistence `64498e7e` with `c11369aa` (one route).

Each of `d5a94eb1`, `6c27657f` and `f296a694` also has a direct option on its
stating claim. A route needs the possession family only on the derivations of
those leaves.

**The node.** The substantive node is the possession family. Its core is the
distinct-cause principle `2c0b9bd7`; its unrestricted and cause-of-being
versions `376d6a5a` and `d0fc96b7` share its warrant. Around it sits the
comparative package that turns possession into "more such":

- the reception bundle `a9036c3c`, `cdb79aa6`, `39a4c28c`, `d0b76fb9`;
- the exceeding step `7030af77`;
- "what is more such has the perfection" `c11369aa`.

Four GOD_4 routes lie outside the family: the two definitional transcriptions
(`0489c24b`, `4f71236b`) and the two grades-at-being-only routes (`3367bf93`,
`fc46b7f9`).

## 2. Fixed meanings

**Possession.** `DistinctCauseHasWhatItGives CausesIn InAct` (`2c0b9bd7`) is
`∀ c x r, c ≠ x → CausesIn c x r → InAct c r`.

- `CausesIn` is CAUSE_2 (DEF-CAUSE-OF-PERFECTION). On the recorded causal scope
  ([causal-perfection-transfer](causal-perfection-transfer.md#a-what-the-cluster-supports-and-under-which-fixed-meanings))
  it is effective causal responsibility for x's being r, which may run through
  secondary causes.
- `InAct` is one parameter. The statement's recorded reading is inclusive:
  IN_ACT_3, formally or virtually.

**The act senses of DISAMB-IN-ACT.**

- IN_ACT_1, formal: `ActFrame.InActFormally`, having r in the same form in which
  the cause produces it.
- IN_ACT_2, virtual: `ActFrame.InActVirtually`, "in a higher way, as a power to
  produce it".
- IN_ACT_3: their disjunction.

**New siblings.** `26632e48` is the IN_ACT_1 reading of `2c0b9bd7`, and
`25b67649` is its exact negation.

**An open sub-fork inside IN_ACT_2.** Its definition joins two determinations
that come apart:

- *Power*: c has r virtually when c has an active power whose exercise produces
  r.
- *Containment*: c has r virtually when c formally has some higher perfection
  that includes r's positive content.

The clause "in a higher way" is the comparative part of the definition, and it
is where the eminent comparative enters. Read without that clause, the definition
gives the power determination. Read with it, it gives containment or some
surpassing order that needs its own specification. This checkpoint does not
register the sub-fork.

**Respects are binary for possession.** `InActFormally c r` either holds or does
not. With the respect "having some heat", a coil at 30–60 °C has it formally.
With a degree-indexed respect ("having heat at or above the workpiece's
temperature") or the threshold quality "being hot" (DEF-RESPECT's example), the
coil lacks it. On a degree-indexed respect, formal possession by the cause
amounts to the cause being at least as hot as the effect. That is the "at least
as such" claim of STMT-SYNONYMOUS-CAUSE-OF-QUALITY-IS-AT-LEAST-AS-SUCH without its
synonymy condition.

**Comparatives (disambiguation `cdb0de59`, now with four senses).**

- MORE_1 is the primitive `MoreIn` that every statement of the case uses.
- MORE_2 is the represented-degree comparative.
- New MORE_3 `OrdinaryComparative`: both comparands have r formally, and the
  first has a strictly higher measured degree, as one body is hotter by
  temperature.
- New MORE_4 `EminentComparative`: the first has r virtually and surpasses the
  second in its mode of having r. `Surpasses` is an explicitly open primitive.

No statement identifies MORE_3 or MORE_4 with MORE_1. At being, DISAMB-ORDER-OF-BEING
records two order models: the homogeneous scale and the order by approach to a
primary.

## 3. The formal results

All four results are verified: `scripts/verify-result.sh` reports Comparator and
NanoDa acceptance. None asserts a member of the package.

**[`moreSuchPackageForcesFormalPossession`](../../TruthCore/Results/Causality/MoreSuchSenseCollapse/Solution.lean)**
(statement `97a338be`, premise-free). The claim holds for every single act
predicate `InAct` that the possession premise and the exceeding step share. Under
that condition the following together imply formal distinct-cause possession:

- distinct-cause possession in `InAct`;
- the four reception premises;
- the exceeding step in `InAct`;
- the more-such bearer `c11369aa` read with formal act.

The proof composes the registered `moreSuchOfDistinctCauseGives` (at `InAct`)
with `distinctCauseGivesOfMoreSuch` (at formal act).

**`controls`** (statement `84ba508d`). There are two beings (coil, workpiece) and
two respects (being, and heat read as the threshold quality "being hot").

- With the ordinary comparative, these hold: the formal gap, inclusive
  possession, the reception premises and the formal bearer. These fail: the
  inclusive exceeding step, "more such" and formal possession.
- With an eminent comparative, the package holds at inclusive act, and only the
  formal bearer fails.

**`ordinaryControls`** (statement `b4521b89`; the MORE_3 reading of "more such" is `31b55b01`). There are three respects: being,
having some heat, and having heat at the workpiece's degree. Temperatures are 40
(coil) and 1000 (workpiece). The decision check shows:

- The coil has some heat formally but not heat at the workpiece's degree. The
  formal possession gap is therefore witnessed only at the degree-indexed
  respect.
- The ordinary-comparative gap holds, and the MORE_3 reading of "more such"
  fails.
- A stipulated MORE_4 reading holds.
- "Nothing moves except as in act" fails read formally and holds read
  inclusively.

**Disclosed artifacts in both controls.** Reception coincides with limitation.
Being is caused by nothing. The temperatures and the eminent relation are
stipulated. Both controls are structural surrogates of the case, not its
evidence.

## 4. The negated-premise test

**The denials, with their original scope.**

- `25b67649`: some distinct cause of r in x lacks r formally.
- `e7db0c0f`: some distinct cause of r in x is not more r than x on the ordinary
  comparative.

**Positive warrant: induction heating.** This is standard engineering practice,
stated here as such and not read from a pinned source; a handbook would only be
navigation. A copper coil carrying alternating current, cooled by circulating
water and typically below about 60 °C, heats a steel workpiece to roughly
800–1200 °C for hardening or forging. On DEF-CAUSE-OF-PERFECTION the coil is
effectively responsible for the workpiece's heat, so it counts as a CAUSE_2
cause.

- With r as "having some heat" and temperature as the degree, the coil is not
  hotter. This witnesses `e7db0c0f`.
- With r degree-indexed or as "being hot", the coil lacks r formally. This
  witnesses `25b67649`.

**The hydroelectric supply.** It matters only on the degree-indexed respect.
Turbine, generator and falling water lack heat at the workpiece's degree
formally, though a generator's windings have some heat.

**Rumford's cannon boring: not a case against the proximate cause.** The
[productive-store note](productive-store-1378.md#when-does-finite-output-require-a-particular-feed)
records only that the water warmed while a mechanically driven borer supplied
work. At the bore, the rubbing metal is formally hot and hotter than the water,
so the proximate cause is a formal possessor. The case counts at most against
formal possession by the remote mechanical drive. It does so only if CAUSE_2
counts a remote cause that works through a real secondary cause, which the
recorded scope allows. This note gives it no independent weight beyond
induction.

**What the rival commits to.** It commits only to production by causes that
lack the produced quality in the same form, or to the same degree. That is
compatible with inclusive possession. No conflict was identified with a floor
item, with the rival's other commitments, or with a precondition of inquiry.

**What discriminates.** The observation decides against formal possession at a
degree-indexed respect and against "more such" on MORE_3. By
`moreSuchPackageForcesFormalPossession`, it also decides against every reading
of the package that combines one act predicate with a formal more-such bearer.

**Substantive Objection Standard, both sides.**

| Target | Record | Classification |
| --- | --- | --- |
| Formal possession `26632e48` at a degree-indexed respect or "being hot" | Induction | **Kept, established case**, conditional only on CAUSE_2 counting the coil. At "having some heat" the case does not reach it. |
| `d5a94eb1` on MORE_3 | Induction (`e7db0c0f`, typed `attacks`) | **Kept, established case.** It does not touch MORE_4, the esse instance `cffad050` (the coil causes no being), or Metaphysics II.1's synonymous premise (the coil is no synonymous cause of heat). |
| `7030af77` at inclusive act with MORE_3 | Induction, through the first control | **Kept** under that pair of readings only. At formal act its antecedent fails for the coil. |
| `f296a694` read formally ("moves only insofar as in act") | The coil moves the workpiece from cold to hot | **Kept** at a degree-indexed respect: the second control checks the structure. By DISAMB-IN-ACT the prima via is then forced onto the uniform inclusive reading. Non-simultaneity must then hold for inclusive act, and the formal-only Metaphysics IX.6 support for it does not carry over. |
| Inclusive possession `2c0b9bd7`, power determination with an instrument's transient power | A cause that produces r with no power to produce r | **No substantive objection identified.** The Humean view can accept a deflated power ascription. Occasionalism denies creaturely causing and leaves the conditional untouched. |
| Inclusive possession `2c0b9bd7`, containment by energy | The energy-form reply: the coil's field "contains" the heat as energy | **Restated as an IN_ACT_2 containment reply.** It cannot save `26632e48`, because it is not formal possession of heat. Against `d5a94eb1` it would need r = energy. There the coil's field energy at any moment is far below the workpiece's thermal energy, so "more such" holds only for the whole supply under conserved-quantity bookkeeping. |
| Inclusive possession, containment determination generally | Capacity or law-mediated production (modal-spine row 14) | **Restated**, unchanged. |
| Instrument objection (modal-spine row 12) | Chisel and shape | **Unchanged, kept conditionally.** It depends on whether IN_ACT_2's power includes the transient power of a tool in use. |

## 5. Strongest positive warrant

**`2c0b9bd7` inclusive, power determination.** Its warrant is close to a meaning
postulate, provided "in a higher way" carries no comparative content. An actual
cause of r can produce r, and on this determination having r virtually is having
that power. It is strong prima facie and carries little load. It shares the form
of its warrant (from an exercise to what the cause is) with agency-in-act
`ef068f46`.

**`2c0b9bd7` inclusive, containment determination.** Two specifications are on
record:

- At esse, every perfection is a mode of being (q.4 a.2 co.), and the
  cause-of-being ladder `d0fc96b7` ⇒ `4ccb319f` applies. That is the warrant of
  `d0fc96b7`, not an additional one.
- Descartes' eminent containment (definition `705f28fe`, Second Replies Def. IV):
  what is present "differs in quality but suffices to take its place". It is a
  substitution criterion, not a comparative. It explains how a cause can contain
  what it lacks formally, but it supplies no order on which the container is
  *more* r than the effect.

The analyst's energy analogue applies only to perfections that are modes of a
conserved quantity.

**`26632e48` formal.** Its warrant is synonymous generation and Metaphysics II.1
for synonymous causes. That is the scope of the sourced synonymous premise.

**`d5a94eb1` on MORE_4 at arbitrary r.** No record specifies an eminent
comparative at arbitrary r under which `d5a94eb1` holds for every distinct
cause. The one recorded analogical order, approach to a primary at being,
certifies "more such" only with the primary as cause (`29133b2b`). It shows in a
model that the same order does not give it for every cause.

**`376d6a5a`, `d0fc96b7`.** Unchanged.

## 6. Consumer audit

**Method.** The audit covers every registered argument with `d5a94eb1` as a
premise and a result. For each, the Lean proof was read to see where the
hypothesis is applied, following hand-offs to imported lemmas. It also covers
the three consumers of `2c0b9bd7` and the bearer `c11369aa`.

| Pattern | Direct applications | Respect | Cause |
| --- | --- | --- | --- |
| A. Maximum or source as cause | `atMostOneMaximeEns` (`ef122ccf`), `godExistsFromMaximeEnsCausingAll` (`678ff65f`), `godMaximalFromCausing` (`482f4ad2`), `AttributesFromEsse.namedSource` (oneFromSource, perfectFromSource, goodFromSource, fromSource), `godHasClassicalAttributes` (`53819d8a`), the identity routes (`c8aa7df3`, `7be49bc0`), `QuartaViaDegreeFork.coverage` (`528ccadd`, through `strictTop`) | esse only | a maximum in being that causes all being |
| B. Maximum as effect | `godIsSimple` (`c473ec4b`; through it godHasIntellect, godHasWill, godIsInfinite), `maximumHasNoDistinctEsseCause` (`8bbe817d`; through it quartaViaWitness), `fromGodCause` (`0acc8761`), `firstMoverIsFirstBeing` (`f8992ef7`) | esse only | any distinct cause of a maximum's being |
| C. Any cause at esse | `everywhereAscentOfCause` (`815d22c8`), `groundMoreInEsseOfCause` (`3eafe507`), strength application `74caa472` | esse only | any |
| D. Arbitrary respect | `nothingMovesExceptInAct` (`892db443`, prima via `f296a694`), `gradesHaveAMaximum` (`1dff22d0`, `6c27657f`), `preexistFromCausalTransfer` (`6b609ddc`, `64498e7e`), `containmentOfStrictComparative` (`62dae664`), `degreeAdequacyOfStrictComparative` (`c974d1f0`), the cycle `9e7de16d` | any r | any distinct cause |

The many Catholicism assemblies pass the hypothesis to the stage theorems above
and inherit their pattern.

**Answers to the audit questions.**

1. **The God-existence and stage-two attribute consumers use "more such" only at
   esse** (patterns A–C). The arbitrary-r comparative, and with it the ordinary
   versus eminent problem and the induction case, does not reach them: the coil
   causes no being. The esse instance `cffad050` would serve them. It has a
   derivation without arbitrary-r possession (`causeOfBeingMoreInBeing`, from
   `4ccb319f` and the reception bundle and exceeding step at esse). Several
   consumers already have such siblings (`5d2b7c6e`, `4d1efe91`); the others
   (`ef122ccf`, `8bbe817d`, `87dd8489`, `3eafe507`, `815d22c8`, godIsSimple and
   its dependants) await certification.
2. **Is the primary as cause enough?** Only for pattern A. There the cause is the
   maximum that causes all being, so `PrimaryCauseIsMoreSuchReading` at esse
   would serve. On the attribution order it is certified by `29133b2b`'s first
   part, given strict primacy and the identification of the maximum with the
   order's primary.
   - Pattern B needs more: that any distinct cause of a maximum's being would be
     more in being than it. That is the claim that a maximum has no distinct
     cause of its being. The primary-as-cause restriction does not give it.
   - Pattern C needs the full esse instance.
3. **Formal or inclusive?**
   - `d0c022f8` (prima via) needs only inclusive possession and no comparative.
   - `c201b61a` (grades maximum) needs inclusive possession, and the bearer only
     at the initial observed comparison. It does not use the exceeding step, so
     `moreSuchPackageForcesFormalPossession` does not apply to it.
   - `892db443` and `1dff22d0` are the legacy arbitrary-r derivations of the
     same two leaves and have those siblings.
   - `6b609ddc` (preexistence) and the two Cartesian results use "more such" at
     arbitrary r with an arbitrary cause of being. On MORE_3 they are refuted by
     the induction case; on MORE_4 they await its specification.
4. **Is the observed-grades premise formal?** In `c201b61a` the observed grades
   ("some things are found more and less good, true, noble") are MORE_1. Their
   examples (hotter, colder) are ordinary comparatives. Since `c201b61a` takes
   possession inclusively and never returns to a formal comparative, the
   induction case is consistent with it. The coil has heat virtually, is exceeded
   by the workpiece, and has its heat from a further cause. Whether the routes
   use `6c27657f` only at esse is unaudited.
5. **Stage-two possession bridges.** No stage-two consumer of `d5a94eb1` applies
   it outside esse. The question whether GOD_4 has intellect formally or eminently
   lies in other premises (CartesianAdequacy's asymmetric containment and
   exemplar bridges), outside this family.

## 7. Provisional judgment (2026-11-27, repaired after challenge)

1. **Formal possession is contradicted by an actual case** at a degree-indexed
   respect or the threshold quality "being hot", under the recorded meaning of
   CAUSE_2. At the respect "having some heat" the case does not reach it. It is
   not a candidate reading for the routes.
2. **Inclusive possession `2c0b9bd7` is strong prima facie but light.**
   - On the power determination it is near-analytic, with no substantive
     objection identified. This holds if power includes an instrument's transient
     power and "in a higher way" carries no comparative content.
   - Restricted to a principal agent's own power, the instrument objection stays
     kept conditionally.
3. **The arbitrary-r comparative package carries less of the God routes' load
   than the first draft said.**
   - On MORE_3, "more such" `d5a94eb1` and the inclusive exceeding step are
     contradicted by the induction case. That is now a typed `attacks`.
   - On MORE_4 no specification at arbitrary r exists.
   - But the audit shows that the God-existence and stage-two consumers use
     "more such" only at esse. **For those routes the load is the esse
     comparative**: `cffad050`, its exceeding step at esse, and that step's
     derivation from the degree-calibration premises. Pattern-A uses are
     certified on the attribution order with the primary as cause (`29133b2b`).
     Pattern-B uses need the open claim that a maximum in being has no distinct
     cause of its being.
   - The arbitrary-r package stays load-bearing only for preexistence
     (`6b609ddc`), the Cartesian containment results, and the legacy derivations
     that already have siblings.
4. **The mixed reading is excluded.** It combines eminent possession with a
   formal bearer and the package.
5. **`376d6a5a` is unchanged.**

Nothing is established, defeated in the frontier sense, or closed.
`truth frontier-diff` shows no change.

**Revision conditions.**

- An independent specification of MORE_4 at arbitrary r. Its form would be a
  `Surpasses` that makes `7030af77` and `c11369aa` jointly true at inclusive act
  without defining eminence as the power to cause.
- A principled CAUSE_2 restriction excluding coil-type causes.
- A demonstration that the esse comparative fails for some maximum's distinct
  cause of being. That would reach pattern B.
- A case of production without power.

## 8. Shared-warrant map

Count each item once.

- `376d6a5a`, `2c0b9bd7` and `d0fc96b7` are one principle at three scopes.
- `2c0b9bd7` and `d5a94eb1` derive each other. The cycle adds no warrant; its
  external inputs are the stating claim of `d5a94eb1` and whatever warrants
  `2c0b9bd7` directly.
- The prima via (`f296a694` via `d0c022f8`), the grades maximum (`6c27657f` via
  `c201b61a`) and the maximal-cause routes share the family.
- **For the God routes the shared item is the esse comparative**, and the eminent
  comparative and the degree calibration are one missing specification. The
  exceeding step `7030af77` is derived (argument `1fbc8de7`) from the calibration
  premises `a961a13e`, `f6677834` and `9eaa3b6e`. The ranking therefore merges the
  calibration family with the eminent-comparative gap.
- `a9036c3c` and `d0b76fb9` are derived from the participation and dependence
  families (arguments `5e42f97e`, `29851dcb`). The cases here bear on neither.

## 9. Review repairs

| Finding | Repair |
| --- | --- |
| P1-1 respect | The respect is fixed in `25b67649`, §2 and §4, including the hydroelectric step. The "at least as such" consequence is stated. With "having some heat", the case reaches the family only through MORE_3. The new control checks both respects. |
| P1-2 Rumford | Restricted to the remote drive under the stated condition, with no independent weight. |
| P1-3 eminent comparative | `cdb0de59` and DISAMB-ORDER-OF-BEING are linked from `97a338be` and `84ba508d`. The wording now follows `29133b2b`. `705f28fe` is engaged in §5. The primary-as-cause question is answered in §6. |
| P2-1 energy reply | In the §4 table, with its classification. |
| P2-2 "in a higher way" | Stated in §2 and §5. |
| P2-3 ranking | Union-of-routes counts per family. Grades-ascent row (`5cda1946`, `f29a6b53`) added. Calibration merged with the eminent comparative. |
| P2-4 wording | "Appears in the expanded derivations; direct options remain." |
| P2-5 `f296a694` | In §4, §6 and the second control. |
| P2-6 induction basis | Stated as standard engineering practice with typical temperatures. |
| P2-7 reviewed revision | The attempt's current assessment names the challenged head and this repair. |

## 10. Next discriminating test

The audit moves the God routes' question to the esse comparative:

1. Certify esse siblings for the pattern-A and pattern-B consumers, so that the
   routes consume `cffad050`, or `PrimaryCauseIsMoreSuchReading` at esse for
   pattern A, in place of `d5a94eb1`. The `d5a94eb1` leaf then leaves those
   routes.
2. Assess the warrant of pattern B's claim, that no distinct cause of a
   maximum's being fails to exceed it in being. Assess it together with the
   degree-calibration family at esse (`a961a13e`, `f6677834`, `9eaa3b6e`), which
   is the next ranked bottleneck on this branch of the graph.
