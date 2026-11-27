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
closure. The next version repaired every finding and added the consumer audit
([§6](#6-consumer-audit)).

A re-check at head `7c483b6a` accepted that version with qualifications: five P1
and five P2 findings. From the Lean proofs of all 73 consumers it confirmed that
every direct stage-one God-route use is at esse, except the older `1dff22d0` and
`892db443`, which have siblings. It also confirmed that the two
older arbitrary-respect derivations have siblings, and that MORE_3 and MORE_4 are
distinct declarations. Its findings were:

- the headline overreached, because stage two reaches arbitrary-respect "more
  such" through preexistence;
- the pattern-A certificate was overstated;
- the first control's comparative was mislabelled as MORE_3;
- the attack crossed senses.

This version repairs all ten ([§9](#9-review-repairs)). The repaired
assertions await re-check.

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

- With a stipulated comparative on which the workpiece is hotter, these hold: the
  formal gap, inclusive possession, the reception premises and the formal bearer.
  These fail: the inclusive exceeding step, "more such" and formal possession.
  This comparative is **not MORE_3**: `OrdinaryComparative` requires both
  comparands to have the respect formally, and here the coil lacks it. The MORE_3
  version of this check is in `ordinaryControls`.
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
- "Nothing moves except as in act" fails read formally at the degree-indexed
  respect and holds read inclusively. At "having some heat" the coil has heat
  formally.
- With MORE_3 as the frame comparative, the package is checked at "having some
  heat". Inclusive possession, the four reception premises and the formal
  more-such bearer hold. The exceeding step `7030af77` at inclusive act fails.

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
| The MORE_3 sibling `31b55b01` of "more such" | Induction (`e7db0c0f`, `alternative_to` and typed `attacks`, both on the sibling) | **Kept, established case.** The attack does not target `d5a94eb1`, whose comparative is the primitive MORE_1; no statement identifies MORE_1 with MORE_3. It would reach those consumers of `d5a94eb1` that apply it at an arbitrary perfection with an arbitrary distinct cause, if read with MORE_3: the older `1dff22d0` and `892db443` (with siblings `c201b61a`, `d0c022f8` that do not use `d5a94eb1`) and the Cartesian `62dae664` and `c974d1f0`. It does not reach MORE_4, the esse uses, the cause-of-being uses at any perfection (preexistence, pattern E in §6), or Metaphysics II.1's synonymous premise. |
| `7030af77` at inclusive act with MORE_3 | Induction, through `ordinaryControls` (MORE_3 as frame comparative, respect "having some heat") | **Kept** under that pair of readings only. At formal act its antecedent fails at the degree-indexed respect. |
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
premise and a result. For each, the Lean proof was read to find where the
hypothesis is applied, following hand-offs to imported lemmas. The audit also
covers the three consumers of `2c0b9bd7` and of the bearer `c11369aa`. The re-check
at `7c483b6a` read all 73 consumers' proofs independently.

**Direct applications by pattern.**

**A. A maximum or source as cause** (respect: esse only; cause: a maximum in being
that causes all being).

- `atMostOneMaximeEns` (`ef122ccf`)
- `godExistsFromMaximeEnsCausingAll` (`678ff65f`)
- `godMaximalFromCausing` (`482f4ad2`)
- `AttributesFromEsse.namedSource`
- `godHasClassicalAttributes` (`53819d8a`, first use)
- the identity uniqueness steps (`c8aa7df3`, `7be49bc0`)

**A+B. Homogeneous-scale fork** (respect: esse only; cause: a maximum as cause,
and every distinct cause through `causesRaiseDegree`).

- `QuartaViaDegreeFork.coverage` (`528ccadd`, `QuartaViaDegreeFork/Solution.lean`
  lines 35–37) and through it `strictTop` (`210019ee`).
- Both sit on `HomogeneousScaleReading`.

**B. A maximum as effect** (respect: esse only; cause: any distinct cause of a
maximum's being).

- `godIsSimple` (`c473ec4b`)
- `maximumHasNoDistinctEsseCause` (`8bbe817d`, conclusion `18561596`)
- `fromGodCause` (`0acc8761`)
- `firstMoverIsFirstBeing` (`f8992ef7`)

**C. Any cause at esse.**

- `everywhereAscentOfCause` (`815d22c8`)
- `groundMoreInEsseOfCause` (`3eafe507`)
- the strength application `74caa472`

**D. Arbitrary respect, arbitrary distinct cause.**

- the older `gradesHaveAMaximum` (`1dff22d0`) and `nothingMovesExceptInAct`
  (`892db443`), whose siblings `c201b61a` and `d0c022f8` do not use `d5a94eb1`;
- `containmentOfStrictComparative` (`62dae664`);
- `degreeAdequacyOfStrictComparative` (`c974d1f0`);
- the cycle `9e7de16d`.

**E. Arbitrary respect, cause of being as cause** (respect: any r; cause: a cause
of x's being).

- `preexistFromCausalTransfer` (`6b609ddc`, `PerfectionPreexistence/Solution.lean`
  line 28). It applies the premise only where c causes x's being (`hTransfer c x r
  hc hx`).

**Inherited patterns.** The following pass the hypothesis on and inherit the
pattern of the theorem named.

| Consumers | Inherited from | Pattern |
| --- | --- | --- |
| `bc0cff0b` godIsOne; `5ed93bb0` maximeEnsIsGod; `1ac60473` naming; `117cc323` governorIsMaximeEns (via maximeEnsIsGod); `beec1dc1` stageOneViaMaximeEns (via maximeEnsIsGod); `3e86eea5` maximeEnsIsGodViaFullDescription; `661ce61d`, `fd1f7e75` (via maximeEnsIsGodViaFullDescription) | `atMostOneMaximeEns` | A |
| `210019ee` strictTop | `QuartaViaDegreeFork.coverage` | A+B |
| `39c30529` firstMoverIsFirstInBeing | `firstMoverIsFirstBeing` | B |
| godHasIntellect, godHasWill, godIsInfinite; `7366a9b4` attributesFromSeparateProofs | `godIsSimple` | B |
| `87dd8489` quartaViaWitness | `maximumHasNoDistinctEsseCause` | B |
| `d8529011` oneFromSource, `1c648123` perfectFromSource, `4c30239f` goodFromSource | `namedSource` | A |
| `827fa9cd` fromSource | `namedSource` and `godIsSimple` | A and B |
| `6c6549ae` (local-logic registration) | the local-logic godHasClassicalAttributes | A and B |
| `51fd6d58`, `79252a71`, `732e38d5`, `1f42ffcd` (godHasClassicalAttributes variants) | the same pair | A and B |

The Catholicism assemblies pass the hypothesis to the stage theorems above.

**Preexistence enters stage two separately.** 62 registered arguments take
`64498e7e` (preexistence) as a direct premise, about 40 of them on God routes
(the re-check's count). Among them are:

- `fromGodCause` `0acc8761`, `fromSource` `827fa9cd` and `perfectFromSource`
  `1c648123`;
- the godHasClassicalAttributes family and `6c6549ae`;
- the Dei Filius roots and the Catholicism assemblies.

So stage two is also exposed to pattern E through `64498e7e`. Its registered
options are:

| Option | Inputs | Exposure |
| --- | --- | --- |
| `6b609ddc` | transfer `f8ba2429`, `d5a94eb1` at pattern E, `c11369aa`, excluded middle | E |
| `e8a3eb51` | transfer `f8ba2429`, cause-of-being possession `d0fc96b7` | none |
| `400ba1f0` | transfer `f8ba2429`, containment in every cause `634a80b8` | `634a80b8`'s derivation `62dae664` uses `d5a94eb1` at pattern D, which induction on MORE_3 reaches |
| Direct option | the q.4 a.2 claim `50df1fd8` | none |

All three derivations share unrestricted transfer `f8ba2429`. The 2026-11-18
assessment in causal-perfection-transfer judged it no stronger than nonuniversal
transfer `10cd24ed`, which has no positive warrant on file.

**Answers to the audit questions.**

1. **The esse restriction.** Every direct stage-one God-route use applies "more
   such" only at esse (patterns A, A+B, B, C), except the older `1dff22d0` and
   `892db443`, which have siblings that do not use `d5a94eb1`. Stage two also
   takes preexistence `64498e7e`, whose `6b609ddc` derivation applies `d5a94eb1` at
   every perfection with a cause of being as cause (pattern E).
2. **Is the primary as cause enough?** Not as a lighter load.
   - For pattern A, `PrimaryCauseIsMoreSuchReading` at esse would serve under the
     open premises `ApproachToPrimaryReading` at esse and `StrictPrimacyReading`.
     These are the hypotheses of `29133b2b`'s first part.
   - But strict primacy (`near x < near p` for every x ≠ p) together with the
     approach order already makes p more in being than every other being. So
     every maximum is p, and the uniqueness conclusions follow without any
     causal premise.
   - The certificate therefore shifts pattern A's load onto the order model and
     strict primacy at esse. Both are open, and both carry uniqueness by
     themselves.
   - Pattern A+B sits on `HomogeneousScaleReading`, where `29133b2b` does not
     apply.
   - Pattern B needs `18561596` (a maximum in being has no distinct cause of its
     being). Its only registered derivation is `8bbe817d` from `d5a94eb1` at esse,
     and no independent warrant is recorded for it.
3. **Formal or inclusive?**
   - `d0c022f8` (prima via) needs only inclusive possession and no comparative.
   - `c201b61a` (grades maximum) needs inclusive possession, and the bearer only at
     the initial observed comparison. It does not use the exceeding step, so
     `moreSuchPackageForcesFormalPossession` does not apply to it.
   - `6b609ddc` is **not refuted by the induction case**: the coil causes no
     being. Read with MORE_3, it would require every cause of a thing's being to
     have each of that thing's perfections formally, at a higher measured degree.
     That conflicts with the route's own account of eminence, since q.4 a.2 places
     bodily perfections in the first cause only eminently. Read with MORE_4, it is
     unspecified.
   - The Cartesian `62dae664` and `c974d1f0` apply it at any respect with any
     distinct cause. Read with MORE_3, their premise is reached by the case.
4. **Are the observed grades formal?** In `c201b61a` the observed grades
   ("some things are found more and less good, true, noble") are MORE_1. Their
   examples (hotter, colder) are ordinary comparatives. Since it takes possession
   inclusively and never returns to a formal comparative, the induction case is
   consistent with it. Whether the routes use `6c27657f` only at esse is
   unaudited.
5. **Stage-two possession.** Stage two takes arbitrary-respect possession through
   preexistence. Whether GOD_4 has intellect formally or eminently also lies in
   other premises (CartesianAdequacy's asymmetric containment and exemplar
   bridges).

## 7. Provisional judgment (2026-11-27, second repair)

1. **Formal possession is contradicted by an actual case** at a degree-indexed
   respect or the threshold quality "being hot", under the recorded meaning of
   CAUSE_2. At the respect "having some heat" the case does not reach it. It is
   not a candidate reading for the routes, and the formal reading of `f296a694`
   fails at the same respect.
2. **Inclusive possession `2c0b9bd7` is strong prima facie but light.**
   - On the power determination it is near-analytic, with no substantive
     objection identified. This holds if power includes an instrument's transient
     power and "in a higher way" carries no comparative content.
   - Restricted to a principal agent's own power, the instrument objection stays
     kept conditionally.
3. **Where the load sits.**
   - **Stage one** uses "more such" directly only at esse, apart from older
     derivations that have siblings. Its load is the esse comparative and what
     replaces it:
     - for pattern A, the order model at esse plus strict primacy, which carry
       uniqueness by themselves;
     - for pattern A+B, the homogeneous-scale fork;
     - for pattern B, `18561596`, which has no independent warrant;
     - for patterns B and C, `cffad050` with its exceeding step at esse and the
       calibration premises behind it.
   - **Stage two** also takes preexistence `64498e7e`. Its derivations share
     unrestricted transfer `f8ba2429`, and one of them (`6b609ddc`) uses "more
     such" at every perfection with a cause of being as cause. The induction case
     does not reach that use. Read with MORE_3 it conflicts with the route's own
     eminence account; read with MORE_4 it is unspecified.
   - On MORE_3, the sibling `31b55b01` and the inclusive exceeding step are
     contradicted by the case. The typed attack targets the sibling, not
     `d5a94eb1`.
4. **The mixed reading is excluded.** It combines eminent possession with a
   formal bearer and the package.
5. **`376d6a5a` is unchanged.**

Nothing is established, defeated in the frontier sense, or closed.
`truth frontier-diff` shows no change.

**Revision conditions.**

- An independent specification of MORE_4 at arbitrary r, or at r with a cause of
  being as cause (pattern E).
- Independent warrant for `18561596`, or for the order model at esse plus strict
  primacy.
- A principled CAUSE_2 restriction excluding coil-type causes.
- Positive warrant for nonuniversal transfer `10cd24ed`, which would strengthen
  `f8ba2429` and with it every derivation of preexistence.
- A case of production without power.

## 8. Shared-warrant map

Count each item once.

- **One principle.** `376d6a5a`, `2c0b9bd7` and `d0fc96b7` are one principle at
  three scopes.
- **One stage-two load.** Preexistence `64498e7e` and cause-of-being possession
  `d0fc96b7` are one load under that principle: `e8a3eb51` derives the former
  from the latter with transfer `f8ba2429`. All registered derivations of
  `64498e7e` share `f8ba2429`.
- **The cycle.** `2c0b9bd7` and `d5a94eb1` derive each other. The cycle adds no
  warrant; its external inputs are the stating claim of `d5a94eb1` and whatever
  warrants `2c0b9bd7` directly.
- **Stage one.** The prima via (`f296a694` via `d0c022f8`), the grades maximum
  (`6c27657f` via `c201b61a`) and the maximal-cause routes share the family. For
  their uses of "more such", the shared item is the esse comparative. The eminent
  comparative and the degree calibration are one missing specification: the
  exceeding step `7030af77` is derived (argument `1fbc8de7`) from `a961a13e`,
  `f6677834` and `9eaa3b6e`.
- **The pattern-A substitute is a separate premise.** The order model at esse
  plus strict primacy carries the uniqueness conclusions by itself. It is not
  another presentation of the esse comparative.
- **Participation and dependence.** `a9036c3c` and `d0b76fb9` are derived from the
  participation and dependence families (arguments `5e42f97e`, `29851dcb`). The
  cases here bear on neither.

## 9. Review repairs

**First challenge (head `30ca1de`).**

| Finding | Repair |
| --- | --- |
| P1-1 respect | The respect is fixed in `25b67649`, §2 and §4, including the hydroelectric step. The "at least as such" consequence is stated. |
| P1-2 Rumford | Restricted to the remote drive, with no independent weight. |
| P1-3 eminent comparative | `cdb0de59` and DISAMB-ORDER-OF-BEING are linked. The wording follows `29133b2b`. `705f28fe` is engaged in §5. |
| P2-1 to P2-7 | Energy reply classified; "in a higher way" located; ranking union counts, grades-ascent row and calibration merged; wording "appears in the expanded derivations"; `f296a694` covered; induction basis stated; attempt revision recorded. |

**Re-check (head `7c483b6a`).**

| Finding | Repair |
| --- | --- |
| P1-1 preexistence | Pattern E added. The three derivations and the direct option of `64498e7e` are recorded. The headline is restated for stage one and stage two (§6, §7). |
| P1-2 `6b609ddc` | No longer called refuted. It is reclassified: on MORE_3 it conflicts with the route's eminence account; on MORE_4 it is unspecified (§6 answer 3). |
| P1-3 pattern-A certificate | It now "would serve under the open premises ApproachToPrimary at esse and StrictPrimacy; strict primacy already entails the uniqueness conclusions". `528ccadd` and `210019ee` moved to A+B on the homogeneous scale. |
| P1-4 first control | Its comparative is relabelled as stipulated workpiece-hotter, not MORE_3, in Lean, statement, argument and relation notes. `ordinaryControls` now checks the MORE_3 package: possession, reception and the formal bearer hold, and the exceeding step fails. |
| P1-5 attack | Retargeted to the MORE_3 sibling `31b55b01`. The relevance clause names the consumers it would reach (`1dff22d0`, `892db443`, `62dae664`, `c974d1f0`). The degree-indexed control's "more such" test is retargeted to the sibling too. |
| P2-1 "only at esse" | Qualified by the older derivations with siblings, here, in the spine-map row and in the attempt. |
| P2-2 respect of `f296a694` | Stated in relation `17658e46`, in §3 and §4, and in the attempt. |
| P2-3 pattern B | Linked to `18561596`, which has no independent warrant. |
| P2-4 review state | The attempt's current assessment is set to unreviewed and names the re-check head `7c483b6a`. |
| P2-5 inheritance | Every consumer is covered in §6, directly or by inheritance. |

## 10. Next discriminating test

The coordinator proposed preexistence `64498e7e` together with strict primacy and
uniqueness at esse as the next checkpoint. **Confirmed, split into two
checkpoints**, because they rest on different principles:

1. **Preexistence `64498e7e`** (stage two). This means:
   - assessing its direct option on the q.4 a.2 claim `50df1fd8`;
   - assessing the transfer premise `f8ba2429` that all three derivations share,
     where the open question is nonuniversal transfer `10cd24ed`;
   - the pattern-E use of "more such" with a cause of being as cause.

   It is the larger exposure, about 40 God-route arguments, so it goes first.
2. **The esse comparative** (stage one). This means:
   - the order model at esse plus strict primacy, which carries uniqueness for
     pattern A;
   - `18561596` for pattern B;
   - the degree-calibration premises behind `7030af77` at esse.

Certifying esse siblings for the remaining A–C consumers is routine formal
follow-up for either checkpoint. It would take the `d5a94eb1` leaf off those
stage-one routes.
