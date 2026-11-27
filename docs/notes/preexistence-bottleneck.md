# Preexistence of the effect's perfections in its cause (q.4 a.2)

Second checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143).
The first checkpoint (PR #2166) assessed the possession family, "nothing gives
what it does not have". Its consumer audit found that stage two of the case
takes q.4 a.2 preexistence `64498e7e` as a direct premise of about 40 God-route
arguments. One of the three registered derivations of preexistence uses "more
such" at every perfection, with a cause of being as the cause (pattern E).

Baseline: main `caaca6e0e`.

[Attempt record](../../corpus/attempts/57ff1c60-317d-4614-a612-3ff248471c05.json) ·
[Batch spec](../../specs/universal-preexistence.toml) ·
[Lean vocabulary](../../TruthCore/Causality/UniversalPreexistence.lean) ·
[Lean results](../../TruthCore/Results/Causality/UniversalPreexistence/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no frontier
rule or closure, and it changes no existing theorem or Challenge. It is
**unreviewed** until the independent semantic challenge recorded in the PR.

## 1. Fixed meaning

**The Lean statement.** `PerfectionsOfEffectPreexistInCauseReading InAct
CausesIn esse` is `∀ c x r, CausesIn c x esse → InAct x r → InAct c r`.

- One `InAct` predicate stands on both sides. The statement record links
  DEF-ACT; where it is instantiated over the shared frame it is the mode-open
  IN_ACT_4.
- `CausesIn c x esse` is CAUSE_2 at being: c is a cause of x's being.
- No comparative occurs in it.

**The source.** I read the passage in the materialized SCTA witness (passage
`ddbc72a3`, I q.4 a.2) before writing this section. The first proof reads:

> quidquid perfectionis est in effectu, oportet inveniri in causa effectiva: vel
> secundum eandem rationem, si sit agens univocum, ut homo generat hominem; vel
> eminentiori modo, si sit agens aequivocum … Manifestum est enim quod effectus
> praeexistit virtute in causa agente: praeexistere autem in virtute causae
> agentis, non est praeexistere imperfectiori modo, sed perfectiori … agens vero,
> inquantum huiusmodi, est perfectum. Cum ergo Deus sit prima causa effectiva
> rerum, oportet omnium rerum perfectiones praeexistere in Deo secundum
> eminentiorem modum.

The second proof starts from God as *ipsum esse subsistens*, with the premise
"omnium autem perfectiones pertinent ad perfectionem essendi".

**Three differences between the Lean statement and the passage.** The claim
`50df1fd8` records the reading choice behind the second difference; the other
two are recorded here.

1. **Mode.** The passage is asymmetric. The effect has the perfection; the agent
   has it "secundum eandem rationem" (formally) or "eminentiori modo". The Lean
   statement uses one predicate on both sides. On the uniform inclusive reading
   it also requires whatever the effect has only virtually to preexist in the
   cause. The existing `CartesianAdequacy.asymmetricFromUniform` gives the
   asymmetric reading from the uniform one, under its two directed sense
   calibrations.
2. **Which perfections.** The passage grounds the principle in "effectus
   praeexistit virtute in causa agente": the effect, as this agent produces it,
   preexists in the agent's power. So its general claim covers the perfections
   that the agent produces. The Lean statement covers every perfection of a
   thing whose being c causes, including any that c does not produce.
   - The two coincide when the cause of a thing's being produces each of its
     perfections. That is the transfer premise `f8ba2429`.
   - It is also the passage's own application, God as "prima causa effectiva
     rerum".
3. **Which causes.** The Lean statement ranges over every cause of a thing's
   being. The passage states the general principle for agent causes and draws
   its "omnium rerum perfectiones" conclusion only for the first cause of all.

**Which eminence.** The passage specifies eminent preexistence in two steps:

- preexistence **in the agent's power** ("in virtute causae agentis"), which is
  the power determination of IN_ACT_2 registered in PR #2166;
- the further thesis that this is a **more perfect mode**, because "the agent as
  such is perfect".

The second step is a comparative of modes. It is close to the eminent
comparative MORE_4 registered in PR #2166, whose `Surpasses` is an open
primitive. **The Lean statement `64498e7e` does not encode the second step.**
Read with inclusive act, it asserts only that each perfection of the effect is
in the cause formally or virtually.

## 2. Consumer audit

**Method.** I scanned the whole library for every theorem with a hypothesis of
type `PerfectionsOfEffectPreexistInCauseReading` that is applied to explicit
arguments. Of the 62 registered arguments with `64498e7e` as a premise, the
others pass the hypothesis to one of the theorems below.

| Pattern | Application sites | Cause |
| --- | --- | --- |
| U, universal source | `godIsPerfect` (`70b9fa04`); `godHasClassicalAttributes` in `StageTwo.ClassicalAttributesLocalLogic` and `StageTwo.ClassicalAttributesIdentity` (the latter is `53819d8a`); `perfectFromGodCause` (`ea6317cf`); `perfectFromSource` (`1c648123`); `firstMoverHasPerfectionsOfThings` (`ee93f52b`); `DirectEsseRootPerfectionGoodness.perfectOfMaximum` | GOD_4, a maximum in being, the source, or the first mover, each a cause of the being of every other being that has being |
| N, nonuniversal causes of being | `perfectFromAncestry` (`aba2aba4`) | each intermediate actual cause of being on a finite ancestry path |
| S, strength and bridge registrations | `causeOfABeingHasBeingOfPreexistence` (`82c7e24b`), `causeOfBeingHasWhatItGives` (`90e85f77`), `wholeEffectContainmentOfPreexistence` (`28befad7`), `asymmetricFromUniform` | arbitrary |

The Catholicism assemblies, the Dei Filius roots and the necessary-root
derivations pass the hypothesis to the stage-two theorems of row U.

**Result.** Every God-route application except `perfectFromAncestry` uses
preexistence only with a universal source of being as the cause.

## 3. The formal results

All five results are verified: `scripts/verify-result.sh` reports Comparator and
NanoDa acceptance.

**`UniversalSourcePreexistence`** (statement `60176223`). If c causes the being of
every other being that has being, then every perfection of any other thing whose
being c causes is in c. It is `64498e7e` restricted to universal sources and
distinct effects. A registered strength order goes from `64498e7e` to it.

**`UniversalSourceHasWhatItGives`** (statement `66252c05`). This is the
cause-of-being possession `d0fc96b7` at the universal source. A strength order
goes from `d0fc96b7` to it.

**`universalPreexistenceOfTransferAndPossession`.** Universal-source preexistence
follows from:

- universal-scope transfer `b26c10a0`;
- universal-source possession.

It uses no unrestricted transfer `f8ba2429` and no nonuniversal transfer
`10cd24ed`. It is the universal counterpart of `e8a3eb51`.

**`perfectFromGodCauseOfUniversalPreexistence`** concludes "perfection of GOD_4"
`78b7c124`. It is a sibling of `ea6317cf` with universal-source preexistence in
place of `64498e7e`. `truth frontier-diff` lists it as a new verified support
alternative for `78b7c124`.

**`controls`** (statement `b4a0e5cc`) is an impersonal universal source. There
are three beings (source, living effect, nonliving effect) and two respects
(being, life). The source causes the being and each formally had perfection of
the others. Only the living effect has life formally; the source has life only
virtually; the frame's act is inclusive.

- These all hold: universal-scope transfer, universal-source possession,
  universal-source preexistence, `64498e7e`, `f8ba2429`, "nothing has actuality
  except insofar as it is", and the inclusive perfection `GodIsPerfect` of the
  source.
- The source does not have life formally.
- Disclosed artifacts: the virtual relation is stipulated, and nothing encodes
  whether it is power or higher-mode containment.

## 4. Strongest positive warrant

| Statement and reading | Strongest positive warrant | Shared with |
| --- | --- | --- |
| `64498e7e` direct option (claim `50df1fd8`) | The q.4 a.2 first proof. It directly supports two things: the agent-produced perfections, and the universal-source restriction, which is the passage's own application to God as first cause. Its extension to every perfection of a thing caused by any cause of being is the analyst's reading recorded in the claim. | The universal-source restriction is the passage's application; the agent-produced form is the possession principle of PR #2166. |
| `64498e7e` by derivation (`e8a3eb51`, `6b609ddc`, `400ba1f0`) | Each derivation is transfer `f8ba2429` plus one presentation of the possession principle: cause-of-being possession `d0fc96b7`, "more such" at pattern E with the bearer, or containment in every cause `634a80b8` (from `62dae664`, pattern D). | All three share `f8ba2429` and the possession principle. They are not three independent supports. |
| Universal-source preexistence `60176223` | Derived from universal transfer `b26c10a0` and universal-source possession. Its direct support is the passage's explicit application. | `b26c10a0` is shared with naming, reduced naming and goodness (2026-11-18 assessment). |
| Universal transfer `b26c10a0` | Derived (`dae70d8a`) from three premises: `5e281daf` (a universal cause of being is the total cause of each effect's being), `2f6b9eff` (a total cause of being causes each mode of being), and `791fa216` (every perfection had in act is a mode of being). `791fa216` is the premise of the q.4 a.2 second proof: "omnium autem perfectiones pertinent ad perfectionem essendi". | The 2026-11-18 assessment left the three inputs unassessed. |
| Universal-source possession `66252c05` | The possession principle at the universal source. On the power determination it is near-analytic: a universal cause of every perfection has the power to produce each. | The possession family of PR #2166, counted once. |

## 5. Rivals and the negated-premise test

**Does a cause of being contain every perfection of its effect, or only being?**

- **Only being.** `4ccb319f` (a cause of being has being) is derived from agency
  in act and q.4 a.1 ad 3 without any transfer premise. This part is
  uncontested.
- **Every perfection.** This needs transfer (the cause of being causes each
  perfection) plus possession.
  - At the universal source, transfer `b26c10a0` rests on the mode-of-being
    thesis `791fa216` and the total-cause premises.
  - At nonuniversal causes it rests on `10cd24ed`, for which no positive warrant
    is on file.

**Denial at nonuniversal causes**, with the respect fixed: some cause of x's
being lacks, formally and virtually, a determinate perfection of x. An example
respect is knowing a particular theorem that x learned from a teacher.

- **Mechanism:** a perfection x acquires from another cause. Ordinary learning
  is the independent justification.
- **Condition:** CAUSE_2 at esse must count the generator (the parent) as a cause
  of the child's being. DISAMB-BECOMING-BEING-CAUSE reads generators as causes
  of becoming, not of being, as an open bridge. Attempt `b1cfe22d` finds that a
  univocal generator need not directly supply the generated individual's esse.
- **Classification:** **kept conditionally** against `64498e7e`'s nonuniversal
  scope, under the generator reading only.
- **Relevance:** it bears on `perfectFromAncestry` if that consumer's actual esse
  causes include generators. It does not touch the universal-source restriction
  or any pattern-U consumer.

**Denial at the universal source**, with the respect fixed: the universal source
of being lacks, formally and virtually, some perfection of a thing whose being it
causes.

- On the power determination this requires a universal source that does not
  produce that perfection. That is the recorded secondary-cause rival `e3da0672`,
  which targets transfer `b26c10a0`, not possession. The 2026-11-18 assessment
  restated it as a non-entailment fact with no weight against `b26c10a0`. This
  checkpoint adds nothing to it.
- **No substantive objection is identified** to universal-source preexistence on
  the power determination, given universal transfer.

**The impersonal-source rival.**

- *Positive account:* a universal source with determinate productive powers that
  produces living and knowing things without itself being living or knowing.
- It **grants** universal-source preexistence and `64498e7e` read inclusively, as
  power. The `controls` certificate shows these premises, with universal and
  unrestricted transfer, jointly hold while the source lacks life formally.
- *What it denies:* the passage's second step, that preexistence in the agent's
  power is a more perfect mode of having the perfection itself.
- *Discriminator:* the encoded `64498e7e` does not separate the two. The
  difference sits in the unencoded "more perfect mode" thesis and in the
  downstream intrinsic-possession bridges. Those are `d164b1ff`, `122b112e` and
  `fe67d766` with the E and L obligations assessed on 2026-11-24 in
  causal-perfection-transfer.
- *Price:* none identified at this premise.

**Substantive Objection Standard, both sides.**

| Target | Classification |
| --- | --- |
| `64498e7e` at nonuniversal causes, generator reading | Kept conditionally (above) |
| Universal-source preexistence, power determination | No substantive objection identified |
| The "more perfect mode" thesis (unencoded) against the impersonal source | Parity at this premise: its positive warrant ("the agent as such is perfect") and the rival's (productive power without the produced quality) are not separated here. The 2026-11-24 assessment of E/L is the place where they are compared, and it is not revised. |
| `791fa216` (mode-of-being thesis) | No substantive objection identified. It has no assessment and no independent warrant beyond the q.4 a.2 second proof on file. |

## 6. Provisional judgment (2026-11-27, unreviewed)

1. **`64498e7e` as encoded is stronger than its source** in mode, in which
   perfections it covers, and in which causes it covers. Its direct option on
   claim `50df1fd8` supports the universal-source restriction and the
   agent-produced form. The extension to every perfection of a thing caused by
   any cause of being is the analyst's. That extension faces a conditional
   objection under the generator reading.
2. **Every God-route application except `perfectFromAncestry` needs only
   universal-source preexistence.** That premise is derived without nonuniversal
   transfer, and a route sibling now consumes it for "perfection of GOD_4".
   `10cd24ed` was already needed by no route under the computed expansion; it
   remains in some derivations of all 28.
3. **On the inclusive (power) reading, universal-source preexistence is
   near-analytic given universal transfer.** It does not discriminate classical
   theism from an impersonal universal source; this is certified by the control.
   The theistic content of q.4 a.2 lies in the unencoded "more perfect mode"
   thesis and the second proof. In the corpus that content is carried by the
   downstream intrinsic-perfection bridges, not by `64498e7e`.
4. **So preexistence's real load at the universal source is universal transfer
   `b26c10a0`.** Its inputs are the total-cause premises and the mode-of-being
   thesis `791fa216` (the second-proof premise), together with the possession
   principle already assessed in PR #2166.
5. **`perfectFromAncestry` is the one consumer that needs nonuniversal scope**,
   and with it `10cd24ed`, which has no positive warrant on file.

These are first grades. Nothing is established, defeated in the frontier sense
or closed.

**Revision conditions.**

- An independent warrant for, or a defeater of, `791fa216` or the total-cause
  premises would move universal-source preexistence.
- An encoding of the "more perfect mode" thesis that discriminates the
  impersonal source would give preexistence theistic content of its own.
- A principled reading of CAUSE_2 at esse that includes generators would turn the
  conditional objection into a defeat of the nonuniversal scope.
- Positive warrant for `10cd24ed` would support `perfectFromAncestry`.

## 7. Shared-warrant map against PR #2166

Count each item once.

- **`64498e7e` and `d0fc96b7` are one stage-two load** under the possession
  principle (`376d6a5a`, `2c0b9bd7`, `d0fc96b7`). Universal-source possession
  `66252c05` is the same principle at universal scope.
- **The three derivations of `64498e7e` are one presentation each of that
  principle, plus the shared transfer `f8ba2429`.** In particular, `6b609ddc` uses
  "more such" at pattern E and `400ba1f0` uses `634a80b8` from `62dae664` at
  pattern D (PR #2166 §6). They must not be counted as support independent of
  the possession family.
- **`b26c10a0` is one premise** shared by universal-source preexistence,
  naming, reduced naming and goodness.
- **The claim `50df1fd8` is the only sourced presentation.** Its explicit
  application supports the universal restriction.
- **The "more perfect mode" thesis is one unencoded item.** It is the same gap as
  the eminent comparative MORE_4 of PR #2166 and the downstream
  intrinsic-perfection bridges. It is not three separate gaps.

## 8. Next discriminating test

1. **Assess universal transfer `b26c10a0` through its inputs,** first the
   mode-of-being thesis `791fa216` (q.4 a.2 second proof), which has no
   assessment. This is where preexistence at the universal source now rests.
2. **Then the esse-comparative checkpoint** from PR #2166: strict primacy and the
   order model at esse, and `18561596`.

Routine formal follow-up is to register universal-source siblings for the other
row-U consumers.
