# Preexistence of the effect's perfections in its cause (q.4 a.2)

Second checkpoint of the warrant phase (owner direction 2026-11-27, #2103, #143).
The first checkpoint (PR #2166) assessed the possession family, "nothing gives
what it does not have". Its consumer audit found that stage two takes q.4 a.2
preexistence `64498e7e` as a direct premise of about 40 God-route arguments. One
of the three registered derivations of `64498e7e` uses "more such" at every
perfection, with a cause of being as the cause (pattern E). Baseline: main
`caaca6e0e`.

[Attempt record](../../corpus/attempts/57ff1c60-317d-4614-a612-3ff248471c05.json) ·
[Batch spec](../../specs/universal-preexistence.toml) ·
[Lean vocabulary](../../TruthCore/Causality/UniversalPreexistence.lean) ·
[Lean results](../../TruthCore/Results/Causality/UniversalPreexistence/Solution.lean)

This is a provisional judgment under the systematic loop. It changes no frontier
rule or closure and no existing theorem or Challenge.

**Review status.** An independent semantic challenge of PR #2170 at head
`fc038086` read I q.4 a.2 in full from the pinned witness. It checked all five Lean
results, the control (by hand), row U and the teacher objection, and accepted the
judgment with qualifications: two P1 and seven P2 findings. The two P1 findings
were these:

- The rival was placed at the wrong step, and the quotation elided the clause
  that decides it.
- The scope of the cause was wrongly counted as an overreach.

This version repairs all nine findings ([§9](#9-review-repairs)). The repaired
assertions await re-check.

## 1. Fixed meaning

**The Lean statement.** `PerfectionsOfEffectPreexistInCauseReading InAct
CausesIn esse` is `∀ c x r, CausesIn c x esse → InAct x r → InAct c r`.

- One `InAct` stands on both sides. The statement record links DEF-ACT. Over the
  shared frame it is the mode-open IN_ACT_4.
- `CausesIn c x esse` is CAUSE_2 at being.
- No comparative occurs.

**The source.** I read it in the materialized SCTA witness of I q.4 a.2 (passage
`ddbc72a3`). The first proof says:

> quidquid perfectionis est in effectu, oportet inveniri in causa effectiva: vel
> secundum eandem rationem, si sit agens univocum, ut homo generat hominem; vel
> eminentiori modo, si sit agens aequivocum, sicut in sole est similitudo eorum
> quae generantur per virtutem solis. Manifestum est enim quod effectus
> praeexistit virtute in causa agente: praeexistere autem in virtute causae
> agentis, non est praeexistere imperfectiori modo, sed perfectiori; licet
> praeexistere in potentia causae materialis, sit praeexistere imperfectiori
> modo: eo quod materia, inquantum huiusmodi, est imperfecta; agens vero,
> inquantum huiusmodi, est perfectum. Cum ergo Deus sit prima causa effectiva
> rerum, oportet omnium rerum perfectiones praeexistere in Deo secundum
> eminentiorem modum.

The second proof starts from God as *ipsum esse subsistens* and has the premise
"omnium autem perfectiones pertinent ad perfectionem essendi". Ad 3 adds "ipsum
esse Dei includit in se vitam et sapientiam".

**Two differences between the Lean statement and the passage.**

1. **Mode.** The passage is asymmetric: the effect has the perfection, and the
   agent has it "secundum eandem rationem" (formally) or "eminentiori modo".
   - The Lean statement uses one predicate on both sides. On the uniform
     inclusive reading it also requires that whatever the effect has only
     virtually preexist in the cause.
   - The existing `CartesianAdequacy.asymmetricFromUniform` obtains the
     asymmetric reading from the uniform one under two directed sense
     calibrations.
2. **Which perfections.** The passage grounds the principle in "effectus
   praeexistit virtute in causa agente": the effect, as this agent produces it,
   preexists in the agent's power. So its general claim covers the perfections
   the agent produces. The Lean statement covers every perfection of a thing
   whose being c causes, including any that c does not produce. The two coincide
   when the cause of a thing's being produces each of its perfections, which is
   transfer `f8ba2429`. That holds for the first cause of all, which is the
   passage's application.

**The scope of the cause is not an overreach.** The passage states its principle
for every effective cause, univocal and equivocal ("ut homo generat hominem"; the
sun). Only "omnium rerum perfectiones" is restricted to the first cause.
Restricting the cause to a cause of being narrows the passage.

**The produced-perfection reading is now its own claim.** Sibling claim
`29789ca3` (`interpretation_of` `50df1fd8`) binds it to `d0fc96b7`. It keeps the
original claim's reading of "effect", reads the perfection as one the cause
produces, and constrains only the cause's act.

**Which eminence: two steps, two comparands.**

- **Preexistence in the agent's power** ("in virtute causae agentis"). This is
  the power determination of IN_ACT_2 (PR #2166).
- **The "more perfect mode" step.** The sentence names its comparand:
  preexistence in material potency. The equivocal agent has the effect's
  perfection "eminentiori modo", which compares it with the univocal mode
  "secundum eandem rationem", the effect's formal possession.
- **The passage's own equivocal agent is the sun.** It is nonliving and
  impersonal, and holds the likeness "per virtutem solis".

The two comparands are encoded as a strength fork over a primitive comparison of
modes, `ModeAbove`. That comparison compares modes, not bearers (definition
`41446d47`):

- weak `47b51faf`: an agent's power is above material potency;
- strong `b9143dd2`: an agent's power is above every other mode, the effect's
  formal possession included;
- `strengthens` strong → weak is registered, and strictness is witnessed.

`64498e7e` encodes neither step.

## 2. Consumer audit

**Method.** A library-wide scan of every theorem that applies a
`PerfectionsOfEffectPreexistInCauseReading` hypothesis to explicit arguments. The
re-check confirmed row U.

| Pattern | Sites | Cause |
| --- | --- | --- |
| U, universal source | `godIsPerfect` (`70b9fa04`); `godHasClassicalAttributes` in `StageTwo.ClassicalAttributesLocalLogic` and `StageTwo.ClassicalAttributesIdentity` (the latter is `53819d8a`); `perfectFromGodCause` (`ea6317cf`); `perfectFromSource` (`1c648123`); `firstMoverHasPerfectionsOfThings` (`ee93f52b`); `DirectEsseRootPerfectionGoodness.perfectOfMaximum` | GOD_4, a maximum in being, the source or the first mover, each a cause of the being of every other being that has being |
| N, nonuniversal causes, any perfection | `perfectFromAncestry` (`aba2aba4`) | each intermediate actual cause of being on an ancestry path |
| N-esse, nonuniversal causes, being only | `82c7e24b` (`64498e7e` ⇒ `4a5a43a5`, "nothing gives being it does not have"), used by `9eb83aff` for `c99f9d23` | any cause of being, at esse only. It is root-reaching, and `4a5a43a5` has independent support through `c5775355` from `4ccb319f` |
| S, strength and bridge registrations | `causeOfBeingHasWhatItGives` (`90e85f77`), `wholeEffectContainmentOfPreexistence` (`28befad7`), `asymmetricFromUniform` | arbitrary |

The Catholicism assemblies, the Dei Filius roots and the necessary-root
derivations pass the hypothesis to the stage-two theorems of row U.

**Result.** Every God-route consumer except `perfectFromAncestry` needs
preexistence only at the universal source, or, for N-esse, only at esse, where an
independent support exists. `perfectFromAncestry` now records in
`strong_version_needed` that it is the one consumer needing the nonuniversal
scope. Universal-source siblings of the other row-U consumers are routine
follow-up.

## 3. The formal results

All six results are verified: `scripts/verify-result.sh` reports Comparator and
NanoDa acceptance.

- **`UniversalSourcePreexistence`** (`60176223`) is `64498e7e` restricted to
  universal sources and distinct effects. **`UniversalSourceHasWhatItGives`**
  (`66252c05`) is `d0fc96b7` restricted the same way. A strength order is
  registered from each original.
- **`universalPreexistenceOfTransferAndPossession`** derives universal-source
  preexistence from universal transfer `b26c10a0` and universal-source
  possession, with no `f8ba2429` and no `10cd24ed`.
- **`perfectFromGodCauseOfUniversalPreexistence`** is a sibling of `ea6317cf` for
  `78b7c124` that consumes the restriction.
- **`agentPowerAboveMaterialPotencyOfEveryOther`** registers the strength order
  of the mode fork (§1).
- **`controls`** (`b4a0e5cc`) models an impersonal universal source. The frame's
  act is checked to be the act frame's inclusive act (`GradesActIsInclusive`).
  - These hold: universal and unrestricted transfer, universal-source possession,
    universal-source preexistence, `64498e7e`, and the inclusive perfection of
    the source.
  - The source lacks "life" formally. "Life" here is a Boolean stand-in respect,
    not any recorded sense of LIVING.
  - A stipulated mode order satisfies the weak mode step and falsifies the strong
    one.

## 4. Strongest positive warrant

| Statement and reading | Strongest positive warrant | Shared with |
| --- | --- | --- |
| `64498e7e`, direct option (claim `50df1fd8`) | The q.4 a.2 first proof. It supports the produced-perfection form at every agent cause (now sibling claim `29789ca3` on `d0fc96b7`) and the universal-source application. The extension to every perfection of the effect is the analyst's reading recorded in the claim. | The produced-perfection form is the possession principle of PR #2166. |
| `64498e7e`, by derivation (`e8a3eb51`, `6b609ddc`, `400ba1f0`) | Transfer `f8ba2429` plus one presentation of the possession principle. | All three derivations share `f8ba2429` and the possession principle. |
| Universal-source preexistence `60176223` | Universal transfer `b26c10a0` plus universal-source possession, and the passage's explicit application. | `b26c10a0` is shared with naming, reduced naming and goodness. |
| Universal transfer `b26c10a0` | Derived (`dae70d8a`) from `5e281daf`, `2f6b9eff` and `791fa216`. `791fa216` is an OPEN Lean-bound reading of `5c5281dd` (q.4 a.2 co.: "omnium autem perfectiones pertinent ad perfectionem essendi"). It reads "pertain to the perfection of being" as "is a mode of its being". Claim `5dd2d69f` states `5c5281dd` and supports the transfer bridge with a gap note. | The second proof (§7). |
| Universal-source possession `66252c05` | The possession principle at the universal source; near-analytic on the power determination. | The PR #2166 family, counted once. |
| Weak mode step `47b51faf` | The passage's own sentence and its ground: "agens, inquantum huiusmodi, est perfectum; materia, inquantum huiusmodi, est imperfecta". | Granted by the impersonal-source rival (§5). |
| Strong mode step `b9143dd2` | The passage's "eminentiori modo" for the equivocal agent, illustrated by the sun. | Applied by the passage to an impersonal agent (§5). |

## 5. Rivals and the negated-premise test

**Does a cause of being contain every perfection of its effect, or only being?**

- *Only being:* `4ccb319f` is derived without any transfer premise.
- *Every perfection:* this needs transfer plus possession.
  - At the universal source, `b26c10a0` rests on `791fa216` and the total-cause
    premises.
  - At nonuniversal causes it rests on `10cd24ed`, which has no positive warrant
    on file.

**Denial at nonuniversal causes**, with the respect fixed: some cause of x's being
lacks, formally and virtually, a determinate perfection of x that x acquired from
another cause. The example respect is knowing a particular theorem learned from a
teacher.

- **Classification:** kept conditionally against `64498e7e`'s
  every-perfection extension, under the reading on which generators are causes of
  being. DISAMB-BECOMING-BEING-CAUSE reads generators as causes of becoming
  instead, and attempt `b1cfe22d` finds that a univocal generator need not
  directly supply esse.
- **Reach:** it bears on `perfectFromAncestry` if that consumer's esse causes
  include generators. It does not touch the produced-perfection form or the
  universal-source restriction.

**Denial at the universal source**, given universal transfer: no substantive
objection identified on the power determination. The secondary-cause rival
`e3da0672` targets transfer and is unchanged from the 2026-11-18 assessment.

**The impersonal-source rival.**

- **Positive account:** a universal source with determinate productive powers
  that produces living and knowing things without being living or knowing.
- **What it grants.**
  - Universal-source preexistence and `64498e7e` read inclusively. The control
    certifies this for the stand-in respect.
  - The weak mode step: preexistence in an agent's power is a more perfect mode
    than preexistence in material potency.
  - The passage's own equivocal agent is the sun: impersonal, and said to have
    the generated things' likeness "eminentiori modo". So the rival can also
    grant the strong mode step read as a ranking of modes.
- **What it denies.** It denies two things, and these are where the
  discriminating content lies:
  - (a) that the source's higher mode is a way of really having the perfection
    intrinsically. That is a surpassing of the effect's formal possession that
    amounts to intrinsic possession (MORE_4's open `Surpasses` together with the
    intrinsic-perfection bridges `d164b1ff`, `122b112e`, `fe67d766` and the
    2026-11-24 E and L obligations).
  - (b) the second proof's subsistent-esse premises with ad 3: God is *ipsum esse
    subsistens*, all perfections pertain to the perfection of being, and "ipsum
    esse Dei includit in se vitam et sapientiam".
- **Price at this premise:** none identified. Neither `64498e7e` nor the mode step
  separates the rival from classical theism.

**Substantive Objection Standard, both sides.**

| Target | Classification |
| --- | --- |
| `64498e7e`'s every-perfection extension, nonuniversal causes, generator reading | Kept conditionally |
| Universal-source preexistence, power determination | No substantive objection identified |
| Weak mode step | No substantive objection identified. The rival grants it. |
| Strong mode step as a ranking of modes | No substantive objection identified. The passage applies it to the sun. |
| (a) intrinsic possession and (b) the second proof against the impersonal source | Not assessed in this checkpoint. The 2026-11-24 E and L assessment is reused, not revised. |
| `791fa216` | No substantive objection identified. It has no assessment, and no warrant on file beyond the q.4 a.2 second-proof sentence it reads, through `5c5281dd` and `5dd2d69f`. |

## 6. Provisional judgment (2026-11-27, repaired after challenge)

1. **The direct option on claim `50df1fd8` supports two things**: the
   produced-perfection form at every agent cause (now sibling claim `29789ca3` on
   `d0fc96b7`), and its universal-source application.
   - `64498e7e` overreaches the passage in mode (one `InAct` on both sides) and in
     perfection scope (every perfection of the effect). The scope of the cause is
     not an overreach.
   - The analyst's extension to every perfection of the effect at nonuniversal
     causes is why `perfectFromAncestry` needs `10cd24ed`. That extension faces a
     conditional objection under the generator reading.
2. **Every God-route consumer except `perfectFromAncestry` needs preexistence only
   at the universal source, or only at esse** (`82c7e24b`, independently supported
   through `c5775355`).
   - Universal-source preexistence is derived without nonuniversal transfer.
   - A route sibling now consumes it for "perfection of GOD_4".
   - `10cd24ed` was needed by no route under the computed expansion before this
     PR.
3. **On the inclusive (power) reading, universal-source preexistence is
   near-analytic given universal transfer.**
   - For the stand-in respect of the control, it does not discriminate classical
     theism from an impersonal universal source.
   - The impersonal source grants the passage's weak mode step, and by the
     passage's own example of the sun can grant "eminentiori modo" as a ranking
     of modes.
   - The theistic content lies elsewhere: (a) intrinsic possession in the higher
     mode (MORE_4 against formal possession, with the intrinsic-perfection
     bridges) and (b) the second proof with ad 3. Neither is carried by
     `64498e7e`.
4. **The load of `64498e7e` is transfer plus possession.** Possession is
   near-analytic on the power reading, so the substantive load is transfer. At
   the universal source that means `b26c10a0`, and through it the total-cause
   premises and `791fa216`.
5. **`perfectFromAncestry` is the one consumer needing the nonuniversal
   extension**, and with it `10cd24ed`, which has no positive warrant on file.

These are first grades. Nothing is established, defeated in the frontier sense,
or closed.

**Revision conditions.**

- Warrant for, or a defeater of, `791fa216`'s reading or the total-cause premises.
- A specification of the comparison of modes that makes a mode above formal
  possession a way of really having the perfection.
- An assessment of the second proof's subsistent-esse premises and ad 3.
- A principled generator reading of CAUSE_2 at esse.
- Positive warrant for `10cd24ed`.

## 7. Shared-warrant map against PR #2166

Count each item once.

- **One possession load.** `64498e7e`, `d0fc96b7` and `66252c05` are one
  possession load, now sourced through sibling claim `29789ca3`.
- **Derivations of `64498e7e`.** Each pairs transfer `f8ba2429` with a
  PR #2166 presentation of possession: `6b609ddc` is pattern E, and `400ba1f0` is
  pattern D via `62dae664`. Since possession is near-analytic on the power
  reading, **the substantive load of `64498e7e` is transfer**.
- **`b26c10a0`** is one premise, shared with naming, reduced naming and goodness.
- **Two theistic loci, kept apart.**
  - (a) MORE_4 against formal possession, together with the intrinsic-perfection
    bridges. These form one gap.
  - (b) The second proof and ad 3.
- **The weak comparand is not part of the MORE_4 gap.** The rival grants it.
- **One shared dependency.** The second proof (b) and universal transfer
  `b26c10a0` both lean on the same q.4 a.2 sentence, "omnium autem perfectiones
  pertinent ad perfectionem essendi" (`5c5281dd`, read by `791fa216`). A
  judgment of that sentence's reading moves both.

## 8. Next discriminating test

1. **Assess the reading `791fa216` of `5c5281dd` together with the second proof's
   subsistent-esse premises and ad 3.** They share the sentence. This is where
   preexistence at the universal source rests (through `b26c10a0`), and it is
   locus (b) of the theistic content.
2. **Then the esse-comparative checkpoint** from PR #2166.

Universal-source siblings for the other row-U consumers are routine follow-up.

## 9. Review repairs

| Finding | Repair |
| --- | --- |
| P1-1 rival placement and elided clause | The sun clause and the material-potency comparand are restored in §1. The rival grants the weak comparand and, by the sun, the eminent ranking. The discriminating content is (a) and (b) (§5, §6.3, attempt, PR body). |
| P1-2 cause scope | Removed from the overreach list. Judgment 1 is reworded. |
| P2-1 missed use | `82c7e24b` → `4a5a43a5` → `9eb83aff` → `c99f9d23` added (N-esse). Judgment 2 now says "needs". |
| P2-2 `791fa216` | Described as an OPEN Lean-bound reading of `5c5281dd`, with claim `5dd2d69f`. |
| P2-3 control scope | Stand-in respect stated in `b4a0e5cc`, the spec, §3 and §6.3. Relation `60160ce8` says "IN_ACT_4 conclusion, interpreted inclusively here". `GradesActIsInclusive` is checked. |
| P2-4 mode step | Encoded as a strength fork (weak `47b51faf`, strong `b9143dd2`, definition `41446d47`, `strengthens` registered, strictness witnessed). Connection plans target `fe67d766`. |
| P2-5 shared-warrant map | Two theistic loci kept apart. Weak comparand removed from the MORE_4 gap. Shared `5c5281dd` made visible. `64498e7e`'s substantive load is transfer. |
| P2-6 `strong_version_needed` | Added on `aba2aba4`. Row-U siblings recorded as follow-up. |
| P2-7 sibling claim | `29789ca3`, `interpretation_of` `50df1fd8`, on `d0fc96b7`, with an attribution note. |
