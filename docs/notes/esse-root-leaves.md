# Leaves of the esse-root and quarta-via GOD_4 routes

This note collects assessments of the open leaves that the GOD_4 routes other
than the prima via reach when their verified supports are expanded: the
esse-root routes `3367bf93` ("GOD_4 exists from an actual root without
contingent dependence, grades at being") and `fc46b7f9` ("from the direct-esse
first root, grades to a maximum at being only"), the fixed-esse bundle
`c98328f1`, and the quarta-via routes `5d2b7c6e`, `678ff65f` and `661ce61d`.
The leaves concern reception and limitation of esse, causal power, and degrees
of being. Earlier assessments of neighbouring leaves stay in the notes that own
them; this note links them rather than repeating them.

## Current cluster assessment under the substantive objection standard (2026-11-19)

[Assessment record](../../corpus/attempts/b1fa5613-099d-430d-be5a-1e168d7ffe8d.json)

**Scope and boundary.** Issue #1751, bottom-out walk of the GOD_4 routes, family
F: the fourteen open leaves that remain unassessed after the prima via route
(`ed7c588a`) was walked in families A–E and C. Drafted on main
`df4909cb025d2e53fee6071a32defe9cf2721284`. The fourteen are:

- reception and limitation of esse: `29e71e43`, `7de89edb`, `1304b462`,
  `e2462fa8`, `331f4751`, `38cf20d9`;
- causal power: `ae68972c`, `0a7896e7`, `54b0131b`, `c8394eaf`, `82eeeb3c`,
  `2068f91c`;
- degrees of being: `e462cf2f`, `fad8af3e`.

None has a concluding argument, and none had a current assessment. Findings of
the other families are cited as the assessments of PRs #1768 (A), #1769 (B),
#1772 (D), #1773 (E) and #1776 (C). These were accepted after independent
challenge but are not merged; nothing below treats them as established, and
every condition on them is stated. Observations marked "analyst observation" are
unregistered. The checks marked "scratch-checked" were compiled against the
built library in a scratch file; none is a registered result. This section
changes no theorem, Challenge, claim, statement, definition, relation, closure
or formal status.

### (a) Fixed meanings

- **Reception of esse** `EsseReceivedIn x r` (DEF-ESSE-RECEIVED-IN,
  RECEPTION_OF_ESSE_VERSUS_EXTERNAL_CAUSE_1 of DISAMB-ESSE-RECEPTION): the esse
  of x is received in the principle r as receiving potency to received act. The
  real constitution of the receiving principle is left open. Reception is kept
  apart from having an external cause of esse (sense 2).
- **Limited esse** `EsseLimited x` (DEF-ESSE-LIMITED,
  LIMITATION_OF_ESSE_VERSUS_REPRESENTED_LIMITING_1 of DISAMB-ESSE-LIMITATION):
  the esse of x is finite in formal perfection, the q.7 notion. It is monadic,
  with no limiter argument. DEF-ESSE-LIMITED says that its content is fixed only
  by `1304b462` and the unlimited-is-infinite reading.
- **Creature** (DEF-CREATURE, CREATURE_1 of `c49de1e9`): some g other than x
  causes the being of every other being in act and causes x's being. In the
  consuming theorem `nothingElseReachesPrimary` (result `f2ca811c`) `Creature`
  is a free Lean parameter; the sense-fixed sibling `ea2c4745` exists.
- **Order by approach** `ApproachToPrimaryReading` (DEF-ORDER-BY-APPROACH-TO-A-PRIMARY,
  MORE_AND_LESS_IN_BEING_2) with strict primacy (DEF-STRICT-PRIMACY): the primary
  `p`, the nearness map `near` and the represented degree `value` are theorem
  parameters, supplied by whoever applies the result.
- **More and less** `MoreIn r x y` (DEF-MORE-IN): the primitive comparative,
  used here at `esse` (DEF-ESSE: being as the act of all things). DISAMB-BEING
  (univocity) reads it analogically; its Lean form is compatible with both
  readings.
- **Maximal** `IsMaximalIn` = `IsMaximumIn` (MAXIME_1, DEF-MAXIME-ENS): has
  being and nothing is more a being. Strictly greatest (`StrictlyGreatestIn`,
  MAXIME_3) is the stronger sense.
- **Causal power** `hasCausalPower w x` (DEF-POWER-CAPACITY-READING,
  CAUSAL_CAPACITY_VERSUS_ACTUAL_EXERCISE_1): an ability to bring about an effect
  under suitable conditions, exercised or not.
- **Existence at the world** `m.ExistsAt w x`: in the intended esse profile
  (owner #1113, recorded on `0436de86`) this is existence in re.
- **Cause of being** `CausesIn c x esse` (DEF-CAUSE-OF-PERFECTION, CAUSE_2,
  CAUSING_AN_EFFECT_3): tenseless and mode-unspecified. Its originating and
  sustaining refinements are CAUSE_OF_BEING_1/2 of `88a8fba7`.
- **Dependence for being** `DependsForBeing x c` (DEF-DEPENDS-FOR-BEING): x
  would not be if c were not, in the sense of q.44 a.1 ad 2. Its
  originating/sustaining fork is open (#1626).
- **Concrete** (CONCRETE_AND_ABSTRACT_6, DEF-CONCRETE-ESSE-IN-RE): having esse in re. In the
  Lean of `82eeeb3c` it is the profile field `m.concrete`; see (e) for the gloss
  mismatch.
- **Opining** `Opines x p` (DEF-OPINING, OPINING_2): judging *or having it
  appear* that p; the definition includes phantasia.

### (b) Where the fourteen enter, which instance each route consumes, and bypasses

Consumer arguments (all verified) and the instances their Solutions use:

| Consumer (result, theorem) | Leaves | Instance used in the proof |
| --- | --- | --- |
| `c8002f3e` (`f2ca811c`, `nothingElseReachesPrimary`), concluding strict primacy `dd732014` | `29e71e43`, `7de89edb`, `1304b462`, `e2462fa8` (with `612078bf`, `fd2c8710`) | `29e71e43` and `7de89edb` at every x ≠ p; `1304b462` (contraposed) and `e2462fa8` at the supplied primary p only |
| `bcc00761` (`0000c819`, `approachToPrimaryFromDegreeMeasure`), concluding `82286a91` | `38cf20d9`, `331f4751`, `e462cf2f` (with `dd732014`, `c11369aa`, excluded middle) | All at one respect, instantiated at `esse` (`82286a91` is BEING_2). `e462cf2f` is used once, to get a bearer and then `InAct p esse` |
| `985d9280` (`f3e50c70`, `existingInActAtFromEleaticPower`), concluding `0436de86` | `ae68972c`, `0a7896e7` (with `7067553d`) | Universal over existents at w |
| `57f22435` (`69c40b27`, `esseCauseGroundViaDistinctDependence`), concluding `cb1cdea9` | `2068f91c`, `82eeeb3c` (with `c99f9d23`, `a8298fbd`) | At each distinct esse-cause c of an actual concretum x |
| `563414ac` (`04066382`, `inhabitedFromFloorActivity`), concluding `56f68b40` | `54b0131b` | At the bearer of the witnessed thought episode |
| `cc2ae5ba` (`03ab719f`, `thoughtIsExerciseFromOpining`), concluding `8cf54bde` | `c8394eaf` (with `a082d5be`) | Universal over borne episodes; the route needs the witnessed episode only |
| `8c0cce46` (`9b25d298`, `maximeEnsCausesAllMaximal`), concluding `0881e859` | `fad8af3e` (with `da09703b`) | Once, for the witness m |

The route theorems were read for the esse-root routes (`godOfRootAtBeing`,
`maximumEqualsRoot` and `maximumExistsOfExistingRootAtBeing`):

- `0436de86` is applied at the actual root n.
- `cb1cdea9` is applied at the pair (a maximum y, the root n) with y ≠ n. So
  `2068f91c` and `82eeeb3c` are consumed at c = a maximum in being and x = the
  root. The `CausesIn y n esse` edge is supplied by the genus principle
  (`d9fad785` on `3367bf93` and `fc46b7f9`, `da09703b` on `c98328f1`), and the
  step is a reductio against n's rootness.
- `e4e6b0cd` is used only in the horn of `actualFork` where no maximum exists.

| Route | Entry of family F | Leaves reached |
| --- | --- | --- |
| `3367bf93`, `fc46b7f9` | `56f68b40`, `0436de86`, `cb1cdea9` and `e4e6b0cd` (through `8eab5889`) | all except `fad8af3e` |
| `c98328f1` | the same, with `da09703b` in place of `d9fad785` and `6c27657f` in place of `e4e6b0cd`; it reaches `e4e6b0cd` only through `5c898d24` (`2247dfc4`, `dbf76ba6`) | all except `fad8af3e` |
| `5d2b7c6e`, `678ff65f` | `0881e859` (through `8c0cce46` or `4487819b`) and `eaa4c679` (through `3fdc8ab7`) | all fourteen |
| `661ce61d` | `eaa4c679` through `3fdc8ab7` and `2247dfc4` | all except `fad8af3e` |

The reception leaves also reach `da09703b` through `0609389b` → `8176a284` →
`142d2d1d` (`identityAscentFromReception`). There `1304b462` is applied to an
identity-bearer cause c, `7de89edb` to its effect x, and `29e71e43` enters
through `da72ae93`. The only derivation of `da72ae93`, `b25dbaad`, uses
`ea2c4745`, which `0ff5d4a7` obtains from `29e71e43` by instantiation.

**Bypasses (every registered consumer path checked).**

- `ae68972c`, `0a7896e7`: `0436de86` has two other derivations, `425afcd6`
  (`adf07168` with `7067553d`) and `f1ea8b89` (excluded middle, `a62975a9`,
  `c85117b0`). The only registered derivation of `adf07168` is `9fb695f9`,
  from these two leaves, so on `425afcd6` `adf07168` stands on its direct
  option.
- `54b0131b`: `56f68b40` has six other derivations: `660673ca`, `fe08da3c`,
  `7bd58160`, `fc055978`, `28da3e80` and `32c7d630`.
- `c8394eaf`: `8cf54bde` has `cecc4365` (`4bc1befb`, `84c57a8c`), and three
  derivations of `56f68b40` (`fc055978`, `28da3e80`, `32c7d630`) avoid
  `8cf54bde` altogether.
- `82eeeb3c`: `cb1cdea9` has `88f13485` and `f501bad3`, which use `0e02cd69`
  instead.
- The reception quartet and the approach triple feed `dd732014` and `82286a91`.
  Neither has another derivation. They are consumed by `e4e6b0cd` (alternatives:
  `5584b295` from `6c27657f`; `f52deeb7` from `7dfa068a`, `c11369aa` and
  excluded middle) and by `da09703b` (alternative: `f4abae1b` from `d9fad785`).
  `0609389b` also has a sibling `f4df2153` through `cffad050`. So each route
  can avoid them. The existence of a maximum rests on a being in act at esse
  together with `e4e6b0cd`. Outside family F, `e4e6b0cd` has two options:
  `6c27657f` (through `5584b295`), or `7dfa068a` with `c11369aa` and excluded
  middle (through `f52deeb7`). Otherwise it rests on the supplied primary.
  Universal causal reach (`da09703b`) rests separately on `d9fad785`
  (`f4abae1b`), `cffad050` (`f4df2153`), `3eb63770` with `3e2fc282`
  (`5106f118`), or `2336e5b4` with `6f4824c9` (`f35f4105`) (lane D, #1772).
- `e462cf2f`: as for the approach triple.
- `fad8af3e`: `0881e859` has seven other derivations.
- **`2068f91c`: no bypass among registered derivations; `cb1cdea9`'s direct
  option (an analyst bridge) remains.** All four registered derivations of
  `cb1cdea9` (`57f22435`, `88f13485`, `f501bad3`, `915ad35a`) contain it.
  `cb1cdea9` is a direct premise of `3367bf93`, `fc46b7f9` and `c98328f1`, and a
  premise of `4487819b`, `2247dfc4`, `dbf76ba6` and the three derivations of
  `7abdee27` (`8e61d00e`, `9253999d`, `7ae73896`). Of the fourteen, `2068f91c`
  is the only leaf that every expansion of the esse-root routes uses.
- Non-trapping `5c898d24` shares this dependency: `2247dfc4` and `dbf76ba6` run
  through `cb1cdea9` and so through `2068f91c`; only `9f2b1c6c` (`e27ea8e3`)
  avoids it.

### (c) End state of each premise

End states: **D** derived or derivable by a specified short derivation; **P**
defended primitive or direct option; **O** open with a concrete blocker.

| Leaf (Lean content) | End state | Strongest positive warrant | Reason to stop, or blocker |
| --- | --- | --- | --- |
| `29e71e43` `∀ x, Creature x → ∃ z, EsseReceivedIn x z` | **P**, moderate to strong | Read in this slice from the pinned q.7 a.2 (`AQUINAS-ST-I-Q7-A2`). The corpus says that a created subsistent form "habet esse, et non est suum esse", so "ipsum eius esse sit receptum et contractum". Ad 1 says "contra rationem facti [est], quod essentia rei sit ipsum esse eius". Analyst observation: together they give reception for every made thing, not only for subsistent created forms. Relation `904404f7` (supports) cites only a.2 co.; no relation records ad 1. CREATURE_1 (caused in being by a universal cause) falls under "factum". | Stop: a source reading whose generalization rests on two sentences of one article. Derivable from `da72ae93` on its direct option without circularity. Through `b25dbaad` it would be a closed cycle (`b25dbaad` uses `ea2c4745`, obtained from `29e71e43`). `da72ae93` has no recorded warrant beyond the same q.7 a.2 generalization (and De ente c.4, unread here), so the derivation adds no independent warrant; the end state stays P. No substantive objection identified (rows 9 and 12 of (f)). |
| `7de89edb` `∀ x r, EsseReceivedIn x r → EsseLimited x` | **P**, moderate to strong | q.7 a.2 co. joins reception and contraction ("receptum et contractum ad determinatam naturam. Unde non potest esse infinitum simpliciter"), and q.7 a.1 co. gives the parallel for form received in matter ("fit forma determinate huius rei"). Both were read in this slice. Relation `869031e3` (supports). | On the **role** reading of limitation (contraction by a receiver) it is near-analytic. On the **measure** reading (finite in formal perfection) it is q.7 a.2's generalization from created subsistent forms to every received esse, which is the analyst's. No substantive objection identified (rows 9 and 10). |
| `1304b462` `∀ x, EsseLimited x → ∃ r, EsseReceivedIn x r` | **P**, strong as a reading | Stating claim `b69b9bb1` reads it as the warrant that q.7 a.1 co. needs: "Cum igitur esse divinum non sit esse receptum in aliquo, sed ipse sit suum esse subsistens, … manifestum est quod ipse Deus sit infinitus". The sentence states only the application to God. Ad 3 repeats it: infinite "ex hoc ipso quod esse Dei est per se subsistens non receptum in aliquo". Substantive warrant: esse is "maxime formale omnium", so it has no internal principle of determination. | On the measure reading this is the substantive claim that only reception limits esse; on the role reading it is analytic. Per DEF-ESSE-LIMITED's own note, it partly fixes the meaning of `EsseLimited` until an account of limitation independent of reception is registered. No substantive objection identified (row 11). |
| `e2462fa8` `∀ z, ¬ EsseReceivedIn p z` for the supplied primary p | **O** | Relation `e8e23c3b`: q.7 a.1 co. says it of God ("esse divinum non sit esse receptum in aliquo, sed ipse sit suum esse subsistens"). | **Blocker: missing identity-bearer bridge at p.** The passage grounds non-reception in God's esse being subsistent, so the warrant transfers to p only if p's essence is its esse, and no route supplies that. Supplying it directly would assume a central part of what the GOD_4 routes are to show. No derivation is on file. Analyst observation: the route uses it only with `1304b462` to get `¬ EsseLimited p`, so the weakest sufficient input is "the primary's esse is not limited" ((d) 1). Next test in (g). |
| `331f4751` `∀ x y, value x ≤ value y ↔ near x ≤ near y` | **P**, a representation postulate | Relation `394a49a5`: q.3 a.5 ad 2, "dicitur tamen mensura omnium, ex eo quod unumquodque tantum habet de esse, quantum ei appropinquat". Read in this slice; the antecedent of "ei" is God. | `value` occurs only in this leaf and `38cf20d9`. With `value := near` it is trivial ((d) 4, scratch-checked), so it adds no content beyond the order-by-approach clause. Because the source speaks of God, it adds no non-question-begging warrant for the existence of a primary. No substantive objection identified (row 13). |
| `38cf20d9` `∀ x y, MoreIn r x y ↔ value y < value x` | **P**, a representation postulate | A global calibration (bearers and non-bearers) at the respect `esse` that the route uses. Its only content beyond the bearer-restricted calibrations of lane D is globality. | With `value := near` it is exactly the order clause of `ApproachToPrimaryReading` ((d) 4). Candidate strength pair → `70508140` (bearer-restricted), unregistered. No substantive objection identified. |
| `e462cf2f` `∃ x y, MoreIn esse x y` | **D** | Specified derivation, scratch-checked (`gradesInBeingFromVerum`): the verum conjunct of `a9622441` (stating claim `c558e6bc`, q.2 a.3) with the left-to-right direction of the comparative conjunct of `5a948c37` (stating claim `b7d959b1`, Metaphysics II.1), taking `being := esse`. Not circular: neither premise depends on `e462cf2f`. | Same-sense condition: the `being` respect of `5a948c37` is the `esse` of DEF-ESSE, and TRUE_3 is used on both sides (as lane C checked for `5a948c37`). Lane C's next test runs the converse direction (being to verum). Using both directions would be a closed cycle and adds nothing; each is a separate support option. Kept, sense-relative rival on the direct option: row 14. |
| `fad8af3e` `∃ m, IsMaximalIn InAct MoreIn esse m` | **D** | Two specified derivations. (i) From `e462cf2f` and `e4e6b0cd` by modus ponens (scratch-checked `someMaximalFromGradesAndGradesToMaximum`; `IsMaximalIn` unfolds to `IsMaximumIn`). (ii) From one being in act as to esse, `e4e6b0cd` and excluded middle, as `actualFork`/`actualCore` already prove inside `maximumExistsOfExistingRoot`. None of the three derivations of `e4e6b0cd` uses `fad8af3e`. | On (ii) a flat world with no grades makes every being in act maximal, so the degree deniers of row 14 do not reach it. The weakness of MAXIME_1 moves the load to the genus principle `da09703b`, which then speaks of every maximal being (lane D's tie point P2). |
| `ae68972c` `∀ x, ExistsAt w x → hasCausalPower w x` | **D** (unregistered converse reading) | Specified derivation: `adf07168` (every existent is in act in some respect) with the act-to-active-principle direction of q.25 a.1 co., "unumquodque, secundum quod est actu et perfectum, secundum hoc est principium activum alicuius". The article itself uses that direction: God is pure act, "unde sibi maxime competit esse principium activum". Ad 1 adds "unumquodque agit secundum quod est actu". All three were read in this slice. Relation `3b9a2215` says that the passage does not state this direction; the article's own inference to God uses it, so it is supported, though not stated. `adf07168` is supported by q.7 a.2 ad 3 (read): prime matter does not exist by itself "cum non sit ens in actu". | Circularity condition: `adf07168` must stand on its direct option, not on `9fb695f9`, which derives it from this leaf. With `0a7896e7` it is conservative over `adf07168` inside `9fb695f9` ((d) 3). It is dispensable on every route. Rows 1–3 restated or no objection. |
| `0a7896e7` `∀ x, hasCausalPower w x → ∃ r, InAct x r` | **P**, strong | Stating claim `a5d11a9e` (q.25 a.1 co.); ad 1, "potentia activa … fundatur in [actu]". Near-conceptual: an ability to act on another is founded on what the bearer actually is. | No substantive objection identified (row 3). It is existential in the respect and holds on each IN_ACT sense. |
| `54b0131b` `∀ b e, IntellectualExercise b e → ∃ y, Causes w b y` | **O** | The inner word or concept as product of understanding (the statement's paraphrase). Source search [`09f03f51`](../../corpus/attempts/round4-source-support-unsupported.json) found no supporting passage. | **Blocker: immanent action and the effect slot.** Kept objection (row 4). In addition, `Ontic.Causes w b y` requires y in the candidate domain of individuals, and a concept is not such a candidate in the intended esse profile. The Lean does not require y ≠ b. The blocker is whether `Causes` admits the agent's own perfection (y := b). The paraphrase's "of another" is not in the Lean type (prose/Lean gap). Further consumer: `4fbd7594`. The capacity sibling `8061edec` with the capacity clause (`660673ca`, `7bd58160`) avoids it. |
| `c8394eaf` `∀ b e, Bears b e → Opines b (content e) → IntellectualExercise b e` | **O** (route instance strong) | Judging is an act of intellect. | **Blocker: DEF-OPINING includes "having it appear that p"** (phantasia). Kept scope objection (row 5): imaginings are thought episodes under lane C's broad carrier, but not intellectual exercises on a faculty psychology that places imagination in sense. The route's episode is a performed doubt, a questioning, for which the premise holds. The `ThoughtOccurs` export forgets which episode it is (lane C), so a restricted sibling needs that adapter. |
| `82eeeb3c` `∀ c x, CausesIn c x esse → m.concrete c` | **D** (with an unregistered dictionary) | At CONCRETE_AND_ABSTRACT_6, from `4ccb319f` ("whatever causes the being of anything is itself in act as to being"; derived from `ef068f46` and `7067553d` by `9355c3db`) with the profile dictionary `InAct x esse → m.concrete x`. That dictionary is the owner's adopted sense (#1103, #1113), but no statement registers it for `m.concrete`. Lane E grades `ef068f46` strong for efficient causes of being (#1773). | Not circular: neither derivation of `4ccb319f` uses `82eeeb3c`. On the causal-capacity gloss its paraphrase gives, it is analytic. The sense mismatch is recorded in (e). No substantive objection identified (row 6). |
| `2068f91c` `∀ c x, c ≠ x → CausesIn c x esse → DependsForBeing x c` | **O**, strong on the aligned sustaining reading | q.44 a.1 ad 2, read in this slice: an agent cause is required "quia effectus non esset, si causa non esset", the conditional holding for impossible antecedents too (relation `7d001102`, supports; claim `3ed36bec`). The received-esse argument of [causal-dependence-support-investigation.md](causal-dependence-support-investigation.md#6-p8-received-esse-same-respect-effects-and-export-to-the-bearer) (merged 2026-11-13) gives it substantive warrant. | **Blocker: mode alignment.** `CausesIn` at esse is tenseless and mode-unspecified; `D`'s originating/sustaining fork is open (#1626). With an originating cause and sustaining `D` it fails (row 7). With both originating it holds, but its partner `a8298fbd` then meets lane B's kept origin counterexample (#1769), and so does its stronger, non-distinct sibling `2e248016`. The pair is jointly warranted only on the sustaining reading, of the originating/sustaining pair considered, which the registered bridge `ce55210c` supplies for `CausesIn` (open). |

Tally: D 4 (`e462cf2f`, `fad8af3e`, `ae68972c`, `82eeeb3c`; the last two need
a registered reading or dictionary); P 6 (`29e71e43`, `7de89edb`, `1304b462`,
`0a7896e7`, and the representation postulates `331f4751` and `38cf20d9`); O 4
(`e2462fa8`, `54b0131b`, `c8394eaf`, `2068f91c`).

Shared dependencies (one assumption each, however many statements present it):

- **The supplied primary p** of the approach order: `e2462fa8`, `331f4751`,
  and through `dd732014` the whole quartet. With `612078bf` read at CREATURE_1
  and `30a8373c` it also carries a universal cause of being (as
  [modal-spine.md](modal-spine.md) records for `612078bf`).
- **The reception theory and the real-distinction question** (lane E, #1773;
  DEF-ESSE-RECEIVED-IN leaves the constitution open): `29e71e43`, `7de89edb`,
  `1304b462`.
- **The mode of causing esse** (lanes B, D and E): `2068f91c` here, `a8298fbd`
  and `000e1f65` in lane B, `5cda1946` in lane D, and the efficiency profile in
  lane E.
- **The existence-in-re reading of `ExistsAt`** (owner #1113): `ae68972c`,
  `adf07168`, `0436de86`.
- **The episode carrier and its export** (lane C, #1776): `54b0131b`,
  `c8394eaf`.
- **The sense of "more being"** (DISAMB-BEING univocity, DISAMB-ORDER-OF-BEING):
  `e462cf2f`, `38cf20d9`, `331f4751`.

### (d) Packages and structural findings

All checks were scratch-compiled against the built library, with no axioms
beyond those of the imported modules. None is a registered result.

1. **The reception quartet is conservative over a limitation pair**
   (`quartetGivesPair`, `pairGivesQuartet`).
   - Within `nothingElseReachesPrimary`, the quartet with `612078bf` gives
     "every x ≠ p has limited esse" and "p's esse is not limited".
   - Conversely, any interpretation satisfying "every creature has limited
     esse" and "p's esse is not limited" extends to one of the quartet, by
     reading `EsseReceivedIn x _` as `EsseLimited x` over a one-point principle
     type.

   `EsseReceivedIn` is constrained elsewhere in the library (`6dfe01ab`,
   `7fcfcee8`), but in this theorem it is universally quantified. So within
   this consumer the quartet adds no formal content beyond the pair. Its value
   is the q.7 reasoning it makes explicit.
2. **The answer to lane D's fork.** Lane D's package P1 (#1772) is inconsistent
   because the relative `LimitedBy y r z` cannot be read on one sense (role or
   measure) across cross-receiving possessors. The four reception leaves here
   use the monadic `EsseLimited` and `EsseReceivedIn` instead. Their
   per-perfection counterparts `cdb79aa6` and `39a4c28c` correspond to
   `7de89edb` and `1304b462` only informally ([modal-spine.md](modal-spine.md),
   "no bridge is registered"), so P1 does not transfer formally.
   - A monadic analogue of the fork exists. On the role reading, `7de89edb`
     and `1304b462` are near-analytic, and the comparative content moves to
     `fd2c8710` (limited approaches less nearly than unlimited). On the measure
     reading, those two carry q.7's substantive claims.
   - No inconsistency follows. Nothing compares the capacities of two limited
     things, and `fd2c8710` compares only limited with unlimited. The batch
     witness `Round2PerfectionPrimacy.Control.witness`, decided in the same
     Solution, satisfies all six premises of `c8002f3e` together.
   - The consumption pattern also differs from P1: `c8002f3e` applies the leaves
     at every x ≠ p and at p, not only at a cause and its effect.
3. **The Eleatic pair is conservative over `adf07168`** (`eleaticPairFromSomeAct`).
   With `hasCausalPower w x := ∃ r, InAct x r`, both leaves hold whenever
   `adf07168` does. `hasCausalPower` is constrained elsewhere (the owner
   commitment `e27489c3`), but in `985d9280` and `9fb695f9` it is a parameter.
4. **The calibration pair is conservative over the approach order clause**
   (`pairFromOrderClause`). With `value := near`, `331f4751` holds by `Iff.rfl`
   and `38cf20d9` is the clause `MoreIn esse x y ↔ near y < near x`.
5. **The approach support supplies its own witness**
   (`approachSuppliesWitness`, `approachPackageGivesStrictlyGreatest`).
   - `gradesAtBeingFromApproach` (`8eab5889`) ignores the antecedent
     (`fun _ => …`): the maximum is the supplied primary.
   - For that p, `38cf20d9`, `331f4751` and strict primacy (the conclusion of
     the reception quartet), with `InAct p esse`, entail
     `StrictlyGreatestIn InAct MoreIn esse p` (MAXIME_3). That is strictly
     stronger than what `8eab5889` concludes (a MAXIME_1 maximum when grades
     exist).
   - So this support option for `e4e6b0cd` adds
     no independent warrant for the *existence* of a maximum. The existential
     load sits in the supply of p, which no leaf of family F argues for. What
     they add is structure: if there is a primary, it is strictly greatest and
     unique.
6. **No inconsistent package found among the fourteen.** Their Lean bodies are
   Horn-type universals and two existentials. The only negations are
   `e2462fa8`'s and the contraposed use of `1304b462`, and the batch witness
   above covers them. `e462cf2f`, `fad8af3e`, `38cf20d9` and `331f4751` hold
   jointly in the `Round3FourthWay` control model used for the batch (two
   beings, one primary).
7. **Not transcriptions.** No consumer applies a premise whose consequent is its
   conclusion. `gradesAtBeingFromApproach` is a two-line projection, but it is
   not a transcription: it derives maximality from the approach order.
8. **Duplicates and strength pairs (none registered).**
   - `29e71e43` / `ea2c4745`: legacy and sense-fixed sibling, tied by the
     instantiation `0ff5d4a7`.
   - `da72ae93` (CREATURE_2 scope) / `29e71e43`: the stronger is derived from
     the weaker through the CREATURE bridge, so the converse derivation would be
     circular.
   - `38cf20d9` → `70508140` (global → bearer-restricted): candidate strength
     pair.
   - `54b0131b` (activity) / `8061edec` (capacity): not a formal strength pair;
     it would need the exercise-to-power interface.
   - `7de89edb` / `cdb79aa6` and `1304b462` / `39a4c28c`: esse and
     per-perfection counterparts in different vocabulary.

### (e) Semantics view and sense findings

`truth semantics` was run on all fourteen leaves and on the consumers
`985d9280`, `c8002f3e`, `bcc00761`, `57f22435`, `563414ac`, `cc2ae5ba`,
`8c0cce46`, `8eab5889` and `18fe3293`. It reports no unbridged mixing. Its
other findings:

| Finding | Classification |
| --- | --- |
| `cc2ae5ba`: THOUGHT_EPISODE_VERSUS_OPINING_1/_2 | **Genuine passage, carried by an explicit premise.** `a082d5be` takes thought episodes to opining. It is not declared in `sense_bridges` (legacy allowlist). |
| `563414ac`: A_THOUGHT_OCCURS_VERSUS_SOMETHING_CONCRETE_1/_2 | **Not an equivocation.** The two senses are different propositions (premise and conclusion), and the argument derives the second from the first through explicit premises. CONCRETE_AND_ABSTRACT_3/_6 are reported bridged. |
| `915ad35a` (a derivation of `cb1cdea9`): WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT_1/_2 | **Over-link.** Sense 1 enters only through the argument's own `definition_ids`; sense 2 through `2e248016`. |
| Off-route consumers `0a26eff0` (RECEPTION_OF_ESSE_1/_3), `95c04a6d` (HAVING_EVERY_PERFECTION_1/_2), `fd940c01` (MAXIMAL_4/5/6, MORE_AND_LESS_IN_BEING_2/3), `bf5f323d` (CONCRETE_AND_ABSTRACT_3/_6) | Not on these six routes; not classified here. |
| `bcc00761`, `8eab5889`, `18fe3293`: BEING_4 (label says BEING_2) "no distinct Lean declaration" | A sense label without a distinct type (P2). |

Findings the tool cannot see, because each runs through one Lean type or one
link:

1. **`82eeeb3c` gloss mismatch (P1 for the record).** Its `definition_ids` link
   CONCRETE_AND_ABSTRACT_6 (esse in re). Its paraphrase and the Lean doc comment of
   `EsseCausesAreConcrete` read concreteness "as causal capacity" (the CC100
   #11 gloss, CONCRETE_AND_ABSTRACT_5 of DISAMB-CONCRETE-ABSTRACT-CRITERIA), and its only
   support relation `81e519b7` supports that gloss alone. On CONCRETE_AND_ABSTRACT_5 the
   premise is analytic; on CONCRETE_AND_ABSTRACT_6 it says that causes of esse have esse in
   re. The record should state which reading is formalized.
2. **The monadic limitation fork** ((d) 2). DISAMB-ESSE-LIMITATION separates
   `EsseLimited` from `HasLimitingPrinciple`, but not the role reading from the
   measure reading. The fork moves warrant between `7de89edb`/`1304b462` and
   `fd2c8710`; it does not threaten validity.
3. **Causal-power links (P2).** `ae68972c` links DEF-POWER-CAPACITY-READING;
   `0a7896e7` links `d662ee50` (the owner commitment) for the same parameter in
   `985d9280`. Both gloss power as ability including unexercised ability, so
   this is an inconsistent link, not an equivocation.
4. **CREATURE_1 on a free parameter** (restated from
   [modal-spine.md](modal-spine.md)). `c8002f3e` reports CREATURE_1, but
   bind-check cannot hold the free `Creature` to it. The sense-fixed sibling
   `ea2c4745` exists; `c8002f3e` does not use it.
5. **DISAMB-IN-ACT** is linked from `0a7896e7` without a sense. That is apt:
   its existential "in act in some respect" holds on all three senses.

### (f) Recorded objections and rivals, classified

| # | Record | Classification |
| --- | --- | --- |
| 1 | Platonism about causally inert abstracta against `ae68972c` (its paraphrase; relation `3b9a2215`) | **Restated as a scope boundary.** It has a target only if `ExistsAt` covers abstracta. In the intended esse profile `ExistsAt` is existence in re, and abstracta have none (DEF-ABSTRACT-NO-ESSE-IN-RE). On the derivation in (c), the load sits in `adf07168`. |
| 2 | Epiphenomenalism against `ae68972c` (paraphrase) | **Restated.** It denies causal power to mental properties or events. These are not candidate individuals, and their bearers keep physical powers. It has a target only on a domain of events. |
| 3 | Humean powers-free ontology (brief, this section) against `ae68972c` and `0a7896e7` | **No substantive objection identified under the selected sense.** DEF-POWER-CAPACITY-READING is an ability under conditions, which a Humean analyses counterfactually instead of denying. It reaches only a realist reading of powers, which is not selected. |
| 4 | Immanent action against `54b0131b` (its paraphrase) | **Kept.** *Target:* the universal over intellectual exercises. *Mechanism:* understanding is an operation that remains in the agent and produces no effect in another candidate individual. *Justification:* relation `946bd61a` records that the pinned q.18 a.3 co. "classes understanding as an action that remains in the agent", and the typing of `Ontic.Causes` puts a candidate individual in the effect slot. *Relevance:* the premise's only warrant is the inner word, which is not such an individual. |
| 5 | Imagination placed in sense against `c8394eaf` (its paraphrase) | **Kept, as a scope objection.** *Target:* the universal over episodes opined in the "appear" sense of DEF-OPINING. *Mechanism:* an imagining is a thought episode on the broad carrier and an opining on DEF-OPINING, but it is an exercise of a sensitive power. *Justification:* the definition itself separates judging from appearing and includes phantasia (Physics VIII.3, claim `c528a52f`); the faculty placement of imagination is the paraphrase's stated condition, not read here. *Relevance:* it does not reach the route's episode, a questioning. |
| 6 | "An abstract cause of esse would falsify" `82eeeb3c` (paraphrase) | **No substantive objection identified.** No abstract cause of esse is established or argued on file. A rival positing Forms as causes of being must either grant them esse in re, which makes them CONCRETE_AND_ABSTRACT_6 by the owner's stipulation, or explain how what has no esse in re gives esse; no record does the latter. |
| 7 | Origin without sustaining dependence (new for `2068f91c`; extends lane B's row 2 against `a8298fbd`, #1769) | **Kept, conditional.** *Target:* `2068f91c` when `CausesIn` at esse covers originating causes and `D` is read sustaining. *Mechanism:* a parent originates a child's being, and the child can be while the parent is not. *Justification:* ordinary generation; q.104 a.1's contrast of a cause of becoming with a cause of being (claim `40aefb2e`, not re-read here). *Relevance:* DEF-CAUSE-OF-PERFECTION leaves the mode open, and the route's edge comes from the genus principle, whose mode is also open. On the narrower sense that claim `40aefb2e` records, a cause of becoming is not a cause of being as such; there the parent is no `CausesIn` cause of the child's esse, and the objection has no target. |
| 8 | Redundant (overdetermining) causes against the bare counterfactual gloss of `D` (brief) | **No substantive objection identified.** Redundant causation is established for qualities and events, not for the esse of one bearer. No case is on file, and the route's instance concerns a root with no other ground. |
| 9 | Real-distinction deniers against `29e71e43` and `7de89edb` ([original assessment](modal-spine.md)) | The original assessment recorded an unread lead. The subsequent [reading of Suárez, DM XXXI](de-ente-esse-source-1628.md#can-an-identity-of-essence-and-existence-rule-out-a-supplier) applies when internal reception requires a really distinct principle. DEF-ESSE-RECEIVED-IN leaves that interpretation open. Scotus and Ockham remain unread. |
| 10 | Divine processions (scope condition, definition `80dea550`, on `da72ae93`) for `7de89edb` | **Restated as a scope boundary.** It is excluded by the domain stipulation, and it belongs to a deferred research phase. |
| 11 | "A finite subsistent being" (rival table, [modal-spine.md](modal-spine.md)) against `1304b462` | **No substantive objection identified.** The rival table records it as a formal alternative with no justification on file. |
| 12 | United-soul communication of esse (DISAMB-ESSE-RECEPTION's open case; SCG II.80 n.13) | **No target on the four reception leaves.** It bears on STMT-ESSE-RECEIVED-IN-OWN-ESSENCE and on lane D's `3e890700`. |
| 13 | No proportioned measure (q.3 a.5 ad 2; relation `394a49a5`) against `331f4751` | **No substantive objection identified**, as lane D found for its degree postulates (#1772): a preorder degree is not a common measure. |
| 14 | Degree-of-being deniers (univocal existence; brief, this section) against `e462cf2f`, and the content of `38cf20d9` and `331f4751` | **Kept, sense-relative.** *Positive account:* "exists" is the univocal existential quantifier and admits no degrees; things differ in their properties, not in how much they exist. *Mechanism:* `MoreIn esse` would never hold, so `e462cf2f` is false. *Justification:* the success of the quantificational analysis of existence statements, including negative existentials (Frege, Russell, Quine; attribution deferred, not read here). *Relevance:* it reaches `e462cf2f` on the existence-as-quantifier reading of being. On DEF-ESSE's act reading it must deny graded actuality, which is a different thesis, and on the derivation in (c) it then bears on `5a948c37`'s comparative conjunct and `a9622441`'s verum conjunct. It does not reach `fad8af3e` (derivation (ii)). |
| 15 | Omission controls: `nothingElseReachesPrimary_omit_*` (`Round2PerfectionPrimacy`), the `Round3FourthWay` controls, and the `Round2ExistenceAct` controls | **Restated** as facts about single interpretations. Each shows a premise is needed there. None is evidence against a premise. |
| 16 | Source search `09f03f51` (no supporting passage for `54b0131b`) | **Restated** as an absence of source support, not an objection. |

Tally: kept 4 (rows 4, 5, 7, 14; rows 5 and 7 conditional, row 14
sense-relative); restated 6 (rows 1, 2, 9, 10, 15, 16); no substantive
objection identified 6 (rows 3, 6, 8, 11, 12, 13). Leaves with no kept
objection: `ae68972c`, `0a7896e7`, `1304b462`, `7de89edb`, `29e71e43`,
`331f4751`, `38cf20d9`, `fad8af3e`, `82eeeb3c`. `e2462fa8`'s blocker is not an
objection to its truth; it concerns the warrant of applying the source.

### (g) Overall provisional judgment, route-level judgment, revision conditions and next test

**Cluster judgment.** Family F bottoms out in three ways.

- **Derivable (four).**
  - `e462cf2f` and `fad8af3e` follow from stated quarta-via premises
    (`a9622441`, `5a948c37`) and from the route's own `e4e6b0cd`.
  - `ae68972c` and `82eeeb3c` are near-analytic once one supported reading
    (q.25 a.1 act → active principle) or one profile dictionary (CONCRETE_AND_ABSTRACT_6
    for `m.concrete`) is registered.
- **Defended (six).**
  - Three q.7 reception readings, moderate to strong: `29e71e43`,
    `7de89edb`, `1304b462`.
  - A stated power–act reading, strong: `0a7896e7`.
  - Two representation postulates, `331f4751` and `38cf20d9`, which add no
    content beyond the approach order.
- **Open (four).**
  - `e2462fa8`: a missing identity-bearer bridge for applying a passage about God to the
    supplied primary.
  - `54b0131b`: immanent action.
  - `c8394eaf`: imagination; the route's instance survives.
  - `2068f91c`: mode alignment.

Thirteen of the fourteen are dispensable on all six routes. The reception and
approach leaves add no independent warrant for the existence of a maximum: for
the primary they are applied to, they entail that it is strictly greatest
((d) 5). The existence claim of the quarta-via routes therefore does not gain
from family F. The existence of a maximum rests on a being in act at esse
together with `e4e6b0cd`. Outside family F, `e4e6b0cd` has two options:
`6c27657f` (through `5584b295`), or `7dfa068a` with `c11369aa` and excluded
middle (through `f52deeb7`). Otherwise it rests on the supplied primary.
Universal causal reach (`da09703b`) rests separately on `d9fad785`
(`f4abae1b`), `cffad050` (`f4df2153`), `3eb63770` with `3e2fc282`
(`5106f118`), or `2336e5b4` with `6f4824c9` (`f35f4105`). The cluster's real
contributions are:

- the q.7 reception theory, as a coherent account of why caused things are
  limited and an unreceived esse is not;
- two short derivations that tie `e462cf2f` and `fad8af3e` to stated premises.

This is a provisional warrant assessment, separate from proof validity and from
computed closure.

**Route-level judgment for the esse-root routes** (`3367bf93`, `fc46b7f9`; the
same holds for `c98328f1` with `da09703b`). The routes are valid conditional
compositions. Their inputs fall into three groups.

1. **An actual, ungrounded root.** The population input `56f68b40` has strong
   local warrant ([cogito-esse-1113.md](cogito-esse-1113.md), reviewed
   2026-11-17). Non-trapping `5c898d24` and the priority bridge `86efed1a` are
   not assessed here; lane B's priority findings (#1769) bear on the latter.
   Non-trapping `5c898d24` shares the group-2 dependency: `2247dfc4` and
   `dbf76ba6` run through `cb1cdea9` and so through `2068f91c`; only
   `9f2b1c6c` (`e27ea8e3`) avoids it. `fc46b7f9` adds `c71c068c`, against which lane B keeps existential
   inertia as the standing rival (#1769).
2. **Identification of the maximum with the root.** This runs through the
   genus principle `d9fad785`/`da09703b` and `cb1cdea9`. Lane D (#1772) finds
   that the universal causal reach of a greatest bearer is a missing bridge,
   with `d9fad785` supported only. `cb1cdea9` rests on `2068f91c`, the one leaf
   of this family with no bypass among registered derivations, and on
   `a8298fbd` or its stronger, non-distinct sibling `2e248016`, which meets the
   same origin counterexample. They are jointly warranted only when the
   `CausesIn y n esse` edge and `D` are both sustaining (only on the sustaining
   reading, of the originating/sustaining pair considered). The genus principle must then say that the maximum *sustains*
   the being of every other being, which adds a mode condition to lane D's open
   bridge.
3. **Naming.** `b26c10a0` (lane D: concurrence for operations open), `09c6d5f0`
   (lane E: source-stated direct option) and the nominal bridge `1ec205ed`.

Provisional judgment: the esse-root routes give **moderate** support for an
actual ungrounded root, conditional on the non-trapping and priority inputs
not assessed here, and **weak to moderate** support for GOD_4. The binding
constraint is group 2: the universal sustaining reach of the maximum together
with the sustaining alignment of `2068f91c`. Through `5c898d24` the same
dependency also reaches group 1, unless non-trapping is taken through
`9f2b1c6c`. Family F's other leaves do not change this.

This judgment is conditional on the other lanes as they stand in the cited PRs:

- lane B's originating/sustaining treatment of `D` and its counterexample
  against `a8298fbd`;
- lane D's universal-reach finding for the genus principle;
- lane E's efficiency profile, which admits merely originating agents;
- lane C's carrier and export limits for `c8394eaf`.

PR #1775 found the caused-mover premise C* weak, and with it the absolute First
Way conclusion. These routes do not use C*, so that finding does not reach
them. They do not make up for it either: their own binding constraint is a
different principle of universal causal scope, the genus principle, here in
sustaining form.

**Revision conditions.**

- A registered sustaining sibling of `2068f91c`, with the genus edge shown to be
  sustaining on independent grounds. This would move `2068f91c` to P and remove
  row 7's target on the route.
- An established case of a cause of esse that is merely originating while the
  effect persists, read in the same `CausesIn` sense the route uses. This would
  make row 7 a counterexample on the route.
- An account of limitation of esse independent of reception (DEF-ESSE-LIMITED's
  own sourcing condition). This would test `1304b462` instead of presupposing it.
- A registered derivation of "the primary's esse is unreceived" from
  identity-bearer premises (next test 2). This would move `e2462fa8` from O to
  D, conditional on an identity-bearer input.
- A justified reading of `ExistsAt` that includes abstracta. This would give row
  1 a target.
- Fixing `82eeeb3c`'s sense (CONCRETE_AND_ABSTRACT_5 or CONCRETE_AND_ABSTRACT_6). This would decide
  whether it is analytic or derivable.
- An established non-quantifier account of degrees of existence, or a
  successful defence of univocity against graded actuality. Either would move
  row 14.

**Most discriminating next test.** Register the sustaining sibling of
`2068f91c`. Its antecedent is `SustainsBeing` (CAUSE_OF_BEING_2) with c ≠ x;
its consequent is `D` on the sustaining reading.

1. Derive the route's instance at (maximum, root) from it and the registered
   bridge `ce55210c`.
2. Lean-check whether the parent–child interpretation (an originating giver,
   with the effect persisting after the giver ceases) satisfies every premise
   except `ce55210c`.

The test can fail in two ways.

- If the composition needs more than `ce55210c` (for instance, a separate law
  taking `SustainsBeing` to the counterfactual `D`), the extra bridge becomes
  the exact open input of the esse-root identification step.
- If it succeeds, the step costs exactly `ce55210c`'s warrant. Its two
  derivations are `366a6ea3` (`da72ae93`, `40a97664` and concurrence
  `d7f5a528`; `da72ae93` brings in `29e71e43` through `ea2c4745`) and
  `835330d4` (`23e04ae5`).

The primary discriminating comparison is then `ce55210c` (sustaining causation
of being, stated in the temporal-history framework of CAUSE_OF_BEING_2) against
existential inertia (lane B's row 3). The first step likely needs a law from
`SustainsBeing` to the counterfactual `D`, since `D` is not time-indexed.

Second test: register `e2462fa8`'s identity-bearer derivation. If the primary's
essence is its esse, `6dfe01ab`, `7fcfcee8` and `14325c83` exclude any
receiving principle, by the `hNoRec` step of `identityAscentFromReception`.
This replaces an application of a God-passage by an explicit identity-bearer
input at the primary.

Third test: register the two derivations of `e462cf2f` and `fad8af3e` in (c).

**Declared revisions: none.** None of the fourteen had an earlier current
assessment, and these are first grades. Retained unchanged:

- the merged 2026-11-13 received-esse assessment of `2068f91c`'s positive
  warrant;
- the modal-spine records on `612078bf`, CREATURE_1 and the unread
  real-distinction lead;
- every other family's classification cited above.

Relation `3b9a2215` records that q.25 a.1 does not state the act-to-power
direction. This note agrees, and adds that the general sentence "unumquodque,
secundum quod est actu…, secundum hoc est principium activum" and the inference
"unde sibi maxime competit" use it. A sibling claim reading that sentence in the
act → power direction is defensible (invariant 5).
