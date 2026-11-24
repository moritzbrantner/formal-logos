# Will versus chance at a necessary, patientless source (#1926 phase 3)

Outcome label (rigor contract 6): **a new bridge**, conditional. Part A is
**already established** elsewhere and is only connected here. In part B only
arguments C and D add support options on a root route: C for `a9776d21`, and D
for STMT-GOD-HAS-WILL (`66aecdd7`); their crux is shown to be the chance rival's
exact denial. Arguments A and B are an intellect-based route found here that
discriminates without restating that denial; they conclude `fdd2b1cf`, which has
no root consumer yet (§10, gap 3).

Lean: `TruthCore.Causality.WillVersusChance` (vocabulary, laws, models) and
`TruthCore.Results.Causality.WillVersusChance` (Solution). Spec:
`specs/will-versus-chance.toml`. All arguments are analyst formulations,
attribution deferred. Every model is a finite structural surrogate on #1897's
frames; it witnesses only its formal interpretation, never metaphysical
possibility.

## 1. Target and question

- **Root-route node.** STMT-GOD-HAS-WILL `66aecdd7` (`GodHasWill IsGod HasWill`,
  HAS_WILL_1 at the capacity level). It is already closed (proved) through the
  intellect route `571e36f0` (GOD_4 has intellect, `29818edd`; whatever has
  intellect has will, `090be689`) and the maximal-being route `13338e9c`.
- **Blocker.** #1897 (`docs/notes/pruss-power-premises.md` §5, §7) derived a
  necessary holder with a two-way (withholding) giving profile and left the
  "Θ.5 bridge" from that profile to will blocked by the **chance rival**: an
  indeterministic non-rational power has the same profile. 68 of 680 attempts
  list the impersonal-source rival (#1926).
- **Questions.** (A) Does the PSR-collapse family exclude a *necessitating*
  impersonal source? (B) What, if anything, discriminates choice from chance at
  a necessary source with an invariant set-up?

## 2. Part A: a necessitating source is excluded, already

**Senses of "necessitate"** (fixed here; no argument passes between them):

| Sense | Vocabulary | Definition | Exclusion of a necessary source with a contingent effect |
| --- | --- | --- | --- |
| NECESSITATE_1: strict efficacy of one rigid act token | #555 `OutputProfile` | `StrictEfficacy`, DEF `01b44013` | `SimplicityCollapse.rigid_core` (the first clause of `Core`); `ModalSenseSupport.RivalNegations` with `Core` refutes `NecessaryActStrictlyYieldsContingent` outright, premise-free |
| NECESSITATE_2: fixed giving (same beings wherever the giver exists) | #1897 `CausalityFrame` | `FixedGiver`, DEF `7bc1d667` | #1897 laws 3 and 4 |
| NECESSITATE_3: set-up necessitation (same set-up ⇒ same giving) | this batch, agency overlay on the same frame | `SetupNecessitatedAt`, DEF `ca00e246` | controls law 8, **only at a source with an invariant set-up** |
| NECESSITATE_4: necessitating reason (a fact-level analogue, not a source relation) | #755 `Arena` | `PSRStrength.Necessitating`, DEF `3055e6f1` | `PSRStrength.necessitating_reason_contingent` |

The senses are joined by the disambiguation NECESSITATE `5836e1f6`.

**The brief's first test is already answered.** Joint satisfiability of the
route premises with `NecessaryActStrictlyYieldsContingent` fails: that
proposition is refuted outright, since `ModalSenseSupport.RivalNegations` (second
clause) derives its negation from `SimplicityCollapse.Core`, whose first clause
`rigid_core` proves. The core fact is K-closure
on the access relation: a necessary source, a strict implication from it to the
effect, hence a necessary effect. Nothing new was proved for it.

**What this batch adds (laws 8–10, premise-free).**

- Law 8: with factive giving, a necessary giver whose set-up is invariant and
  whose giving is set-up necessitated gives being at `w` only to necessary
  beings. Without the invariance hypothesis the law fails: on `theistG` with
  `varyingState`, the necessary `g` gives the contingent `c` only at `false`,
  its set-up varies, and it is vacuously set-up necessitated.
- Law 9: with excluded middle, VG (variation needs a varying set-up) is exactly
  set-up necessitation of every being at `w`.
- Law 10: #1897's withholding holder, with P5 and an invariant set-up, is a
  two-way giver and is **not** set-up necessitated, whatever its power.
- Law 14: with an invariant set-up, set-up necessitation from `w` is exactly
  giving the same beings at every accessible world where the giver exists; and
  a fixed giver existing at `w` is set-up necessitated from `w`.

**What it excludes and what it leaves.** Each sense excludes a necessitating
source of contingent effects **whether personal or not** (the set-up sense only
at a source with an invariant set-up): a necessitated will is excluded as well
(laws 8 and 10 do not mention `Rational`). So part A removes the necessitating impersonal source (Spinozist
emanation of the actual contingents) *only by the same step that requires the
theist's will to be non-necessitating toward creatures* (q.19 a.3). It does
not discriminate will from impersonality. The surviving impersonal rival is the
non-necessitating, chancy source (part B). A necessitarian who denies P5 is not
refuted (#1897 §5, rival 2).

## 3. Fixed meanings (part B)

The agency overlay `AgencyFrame` adds primitives to the shared
`CausalityFrame` (#1784): `StateAt` (intrinsic states), `ConditionOf` (external
conditions of a giving), `PowerOf`, `Rational` and `Exercises`. No relation
between fields, or with the frame, is assumed; every bridge is a premise.

| Term | Definition | Meaning |
| --- | --- | --- |
| Rational power | DEF `b8061228` | an inclination following intellectual apprehension of the good; primitive classification |
| Same set-up | DEF `69d8aef9` | same intrinsic states and same external conditions in two worlds |
| Invariant set-up | DEF `b4bb7bb4` | same set-up at every accessible world where the giver exists: the surrogate of a simple, patientless source |
| Giving by a power | DEF `582f44c3` | `GivesTo` plus the exercise of a power |
| One power | DEF `fdeb7757` | all powers of the being are one (q.19 a.4 ad 4) |
| CHANCE_1 / _2 / _3 | DEFs `e0179074`, `0fe412ef`, `a2840d96`; disambiguation `c18f084e` | incidental (varying concurring condition); varying set-up; indeterministic propensity of a non-rational power |
| Willed two-way giving | DEF `de24ce2e`; sense WILL_CAPACITY_VERSUS_WILLED_GIVING_2 of `8b3d47bc` | CHANCE_3's profile with a rational power: an exercise-level sense, unbridged to HAS_WILL_1 and to the `Wills` relation of `a94c5dfc` |
| Power for a proposition / active power | disambiguation POWER_FOR_VERSUS_ACTIVE_POWER `e5417243` | `PowerFor` (DEF `bf7eddca`) picks out #1897's holder; `PowerOf` (DEF `582f44c3`) is an active power. Separate primitives; nothing identifies them. One power and `Rational` concern `PowerOf` only; argument B lists the one-power holder premise as its sense bridge |

**Semantic grounding of the new relations.** *Set-up sameness* is an
equivalence on worlds for a fixed giver (reflexive, symmetric, transitive by
its biconditionals). *Exercise* is a world-indexed relation between a giving and
a power; no structural property is assumed. *Invariant set-up* is an
accessible-world universal; it does not entail one power (the intellectual
chancer). Examples and non-examples are in each definition. The generalization
from ordinary agents and coins to a first source is an explicit bridge in each
case (the holder premises below), never a definition.

**Source read for this slice** (navigation, no claim record): ST I q.19 a.4,
materialized from passage `74e86e1a` (SCTA witness). The respondeo gives three
arguments that God acts by will and not by necessity of nature: (1) from the
order of agents, since a natural agent's end is predetermined by a higher
intellect; (2) a natural agent "habet esse determinatum" and "uno et eodem modo
operatur, nisi impediatur", while divine being is not determined, so determinate
effects proceed "secundum determinationem voluntatis et intellectus"; (3) effects
pre-exist in the cause according to its mode, and divine being is its
understanding. Ad 4: knowledge directing, will commanding and power executing
"in Deo unum sunt". Argument (2) is a dichotomy of nature and will; per se
chance is not among its options (for Aquinas chance is per accidens,
CHANCE_1). Arguments (1) and (3) pass through intellect.

## 4. Results

| Arg. | Result | Theorem | Premises → conclusion | Axioms |
| --- | --- | --- | --- | --- |
| A | `b5b84276` | `oneIntellectualPowerGivesWilledGiving` | `090be689`, will is a rational power `71fc097b`, giving exercises a power `495a40ad` → every giving by a one-power intellectual being exercises a rational power `5c1aba17` | none |
| B | `963e9689` | `actualAbsenceHolderGivesByWill` | withholding `b8a2a9e1`, P5 `c76b6e2c`, holder invariance `a065c332`, holder intellect `813a9181`, holder one power `9856239a`, A's conclusion → some holder is a willed two-way giver `fdd2b1cf` | none |
| C | `51ea3a40` | `thetaFiveBridgeGivesWill` | DNP_inv `55892476`, `495a40ad`, rational power is will `65e0179f` → invariant two-way givers have will `a9776d21` | none |
| D | `bc4d81f6` | `godHasWillByThetaFive` | GOD_4 holds the power `0050b6ed`, P2′ `906f5c39`, creator reading `9f7b1778`, factive giving `3ef41442`, P5, holder invariance, C's conclusion → **`66aecdd7`** | none |
| E | `16002747` | `sameSetupVariationIsRationalWeakens` | DNP′ `6e4b519b` → DNP_inv (backs `strengthens` DNP′ → DNP_inv) | none |
| F | `ec6627bf` | `willVersusChanceControls` | premise-free laws and models | Mathlib three |

**Laws** (`Model.Laws`): (1) an invariant set-up excludes CHANCE_1 and
CHANCE_2; (2) VG excludes invariant two-way giving, willed or chancy; (3) VG ⇒
DNP′; (4) DNP′ ⇒ no CHANCE_3; (5) the flip: reclassifying powers exchanges
willed two-way giving and CHANCE_3 with the same set-up; (6) one power and will
exclude CHANCE_3 for a being with will, whatever the warrant for its will (only
the bridge "whatever has will has a rational power" is used); (7) both are
two-way giving; (8)–(10) part A above; (11) with excluded middle, DNP′ is
exactly the absence of CHANCE_3 at `w`, and DNP_inv exactly its absence at
invariant beings; (12) with excluded middle and giving as exercise, an invariant
two-way giver is willed or CHANCE_3, and not both given one power; (13) the
chance core: one power, CHANCE_3, intellect, will following intellect and will
as a rational power are jointly inconsistent; (14) set-up necessitation and
fixed giving (part A above).

**Models.** Theist nonvacuity of A–D (`theistG`, `simpleRational`); the chance
rival (same frame, set-up, giving and one power, power non-rational: DNP′ and
DNP_inv fail; the conclusions of B, C, D fail); the intellectual chancer (two
powers); each member of the chance core needed (five deletion models); omission
models of every premise of A (3), B (6), C (3) and D (7); DNP′ strictly
stronger than DNP_inv (three worlds: a chancy being whose set-up varies at a
third world); VG and chance-sense nonvacuity, including one giver with
CHANCE_2 and CHANCE_3 at the same world (the senses are not exclusive). `truth
countermodel` does not
handle `CausalityFrame` parameters (#1897 gap 9), so all models are hand-written.

## 5. What discriminates will from chance

**Formal finding.** In this overlay nothing but `Rational` separates a willed
two-way giver from a CHANCE_3 giver (law 5), consistent with #742 at the will
step.
The Θ.5 premise in either strength is, with excluded middle, *exactly* the
denial of CHANCE_3 in its scope (law 11). So argument C/D is a valid support
option whose only discriminating content against the chance rival is DNP_inv
itself: as evidence against that rival it begs the question unless DNP_inv has
warrant of its own. Different presentations of one assumption are not
additional evidence.

**A discriminating route found here.** At a source with one power, intellect
with will following intellect (`090be689`) and "whatever has will has a rational
power" (`71fc097b`) suffices to make the giving willed (arguments A, B), and the
chance rival must deny the source's intellect (law 13). Law 13's core has four
members besides CHANCE_3 itself: one power, intellect, `090be689` and
`71fc097b`; a one-power chancy source must deny at least one of them, and its
natural choice is intellect. Giving as exercise (`495a40ad`) is not a member of
that core (CHANCE_3 already contains an exercised power); it is needed separately
for arguments A and B and for the dichotomy of law 12: without it a source can
give without exercising any power and is then neither willed nor CHANCE_3 (the
`powerless` model). The converse is **not** proved: `Rational` has no content,
so nothing here shows that a source without intellect is not willed, and other
warrants for will at the source that are independent of DNP_inv (e.g. the Fifth
Way and governor routes, given the holder–root identification) would
discriminate equally (law 6). Argument D is not such a warrant: its will comes
from DNP_inv, which is exactly the denial of CHANCE_3 (law 11), and it concludes
will of GOD_4, not of the holder. So the case for willed giving at the source,
by this route, is at most as strong as the conjunction of intellect at the
source, one power and the holder-root identification (#1897 gap 2). Intellect
has its own arguments and its own impersonal rival
(`docs/notes/causal-perfection-transfer.md`, "Emergence and comparison under
the same standard"; `docs/immaterial-intellect-reception.md`, rival 9). This is
horizontal support from another argument family and shares its dependencies.

**Warrant of DNP′ and DNP_inv** (Substantive Objection Standard applied both
ways).

- *Positive warrant for DNP′.* The Aristotelian-Thomist principle that a
  natural (non-rational) agent acts in one way unless impeded (Θ.5; q.19 a.4
  co., second argument), supported by the success of deterministic laws in
  ordinary experience.
- *Objection to DNP′.* Target: the universal premise DNP′. Mechanism: an
  indeterministic non-rational power (CHANCE_3). Independent justification:
  stochastic dynamics in collapse and Copenhagen-type readings of quantum
  mechanics, which are developed, empirically adequate positions. (Navigation
  only, not support: Pruss allows his first cause to be "perhaps
  non-deterministic".) Relevance: one such power falsifies
  DNP′ (law 11). Status: **live, not established**: deterministic readings
  (Bohmian, Everettian) are equally adequate, so the evidence is
  interpretation-dependent.
- *DNP_inv escapes the counterexample, on an assumption.* Assumption: every
  physical propensity bearer has a set-up that differs at some accessible world
  where it exists, under broad metaphysical access (a nucleus can exist in other
  environments and states). Then physical propensities fall outside DNP_inv's
  scope (the strictness model has this shape), and the evidence of physics bears
  on the general principle, not on beings with an invariant set-up.
- *But its positive warrant is undercut.* DNP_inv inherited its support from
  the general natural-necessity principle; if per se chance exists among
  natural powers, that inductive base no longer supports the restricted
  instance. No independent reason was found why an invariant, patientless
  being could not have a non-rational propensity. Candidate reasons examined
  and not adopted: (i) "chance requires a varying set-up" is CHANCE_2, not
  CHANCE_3, and would beg the question; (ii) q.19 a.4's determination argument
  (a determinate effect from an undetermined being needs intellect) is an
  argument about specifying determinate outcomes, which is the intellect /
  exemplar question (C4 in `causal-perfection-transfer.md`), not a separate
  warrant for DNP_inv; (iii) *Physics* II.6, that chance and spontaneity are
  posterior to intellect and nature (navigation), concerns incidental chance
  (CHANCE_1), which an invariant set-up already excludes (law 1), so it does not
  bear on CHANCE_3.
- *No substantive objection* was identified to the inferences of A–E, to
  giving as exercise, or to the will bridges (`71fc097b`, `65e0179f`) beyond
  their being primitives. The omission models show only that each premise is
  needed.

**Warrant of the other central premises of B and D.**

- *Holder invariance* (`a065c332`, used by B and D). Positive warrant: the
  classical arguments for divine immutability and simplicity (a pure act has no
  intrinsic state that could differ), and patientlessness of a source that gives
  being to every actual contingent (no pre-existing patient or concurring cause
  of that giving). Contested on the theist side too: theists who take divine
  decrees to be contingent intrinsic states deny it (DEF `b4bb7bb4`). Both the
  theist and the chance-rival models accept it, so it does not discriminate;
  it decides whether law 12's dichotomy applies. If it fails, varying intrinsic
  states (CHANCE_2-type variation) carry the difference and the question moves
  to what explains those states. Provisional judgment: prima facie plausible
  for a first source on the simplicity routes, open, not assessed further here.
- *One power* (`9856239a`, B). Positive warrant: simplicity at the level of
  powers (q.19 a.4 ad 4: knowledge, will and executing power "in Deo unum
  sunt"). The chance rival's natural reply is a source with two powers (the
  intellectual chancer, Pruss's "non-unitary cause"). Provisional judgment: as
  strong as the simplicity case for the source, which this slice does not
  reassess; it is the premise the intellectual chancer denies.
- *GOD_4 holds the power* (`0050b6ed`, D). PowerFor (DEF `bf7eddca`) is a
  power whose exercise would initiate a chain issuing in the proposition, while
  God's joint absence of creatures is realized by non-exercise (withholding;
  q.104 a.3 ad 3). On #1897's two-way reading of PowerFor for an outcome
  realized by withholding (#1897 §4, confirmed only conditionally on P2δ's
  warrant), the bridge follows from q.19 a.3 (God could have refrained from
  creating) and q.104 a.3 (God could cease to give existence). Its open parts
  are that reading and GOD_4's existence at `w`. Directional, not uniqueness.
  Provisional judgment: a plausible direct option on classical theism, as
  strong as the two-way reading of PowerFor.

## 6. The strongest standing rival and its price

**Rival.** A necessary, simple (one non-rational power, invariant set-up),
patientless source that gives the actual contingents being by an
indeterministic propensity (CHANCE_3), and could have withheld them. Model:
`Model.ChanceRival`. It accepts every premise of #1897's withholding route.

**Price.** Items 1, 2 and the first sentence of 3 are derived under the
stated premises; the rest are recorded commitments.

1. It denies DNP′ and DNP_inv (law 11), i.e. it posits per se chance at a
   necessary, simple being.
2. It denies VG (shared with the theist; law 2).
3. Given one power, `090be689` and `71fc097b`, it denies intellect at the
   source (law 13). Imported, not derived here: if the source gives being to
   intellectual beings, it must then deny the perfection-transfer premises for
   intellect or the totality of its existential supply (the emergence reply of
   `causal-perfection-transfer.md`).
4. Recorded, not derived, and symmetric: both sides owe an account of how a
   simple source settles determinate outcomes. The chancy source owes a
   non-cognitive specification of outcome weights; the willing source owes the
   account of determinate ideas in a simple intellect (the exemplar question).
   This is the C4 / intellect question of `causal-perfection-transfer.md`, not
   a separate cost of chance.

None of these is shown to conflict with an accepted floor item; each is a
substantive commitment, not a refutation. Unusualness is not counted as a cost.

## 7. Matched-scope comparison (same explanandum)

Explanandum: a necessary source with an invariant set-up and one power gives
the actual contingent concreta being and withholds them at an accessible world.
(Without one power, the intellect rows do not apply: a source with two powers
can have intellect and give by chance, the intellectual chancer.)

| Criterion | Willing source | Chancy impersonal source |
| --- | --- | --- |
| Two-way profile, invariant set-up | yes (theist model) | yes (chance-rival model) |
| Contrastive explanation of which effects | none typed (luck objection open) | none (propensity) |
| Structural marks (#742; flip law) | identical | identical |
| What decides the variation | a rational power, primitive | a non-rational propensity, primitive |
| Extra commitments | `Rational` and the will bridges; intellect at the source (route A/B) | per se chance at a necessary simple being; denial of intellect at the source (law 13) |
| Fit with independent families | coheres with the intellect routes (perfection transfer, Fifth Way); inherits their open premises | coheres with emergence accounts of intellect; must reject the intellect routes at the source |
| Good-directed order of the effects | not tested here | not tested here |

**Verdict at this scope: parity** on every structural criterion of the will
step itself. The rows that differ are commitments, not discriminating evidence:
each side pays a primitive (a rational power; a non-rational propensity), and
which side's further commitment is better warranted is the intellect question,
not a will-step question. Whether the effects' order favours a source directed
to the good is a teleological test (horizontal family) not run here; it is
listed as a next test, not scored.

## 8. Overall provisional judgment

- **Part A:** settled conditionally on the stated frames and already recorded
  in three vocabularies: a necessitating source of contingent effects is
  excluded in each fixed sense (in the set-up sense only at a source with an
  invariant set-up), together with a necessitated will. High
  confidence in the consequence; it decides nothing between will and an
  impersonal non-necessitating source.
- **Part B, Θ.5 route (C, D):** a valid new support option for `66aecdd7`, but
  **it does not discriminate will from chance** beyond DNP_inv's own warrant,
  which is weakened (its parent principle meets a live objection) and not
  independently supported. The chance rival stands at this step.
- **Part B, intellect route (A, B):** discriminating, conditional on the
  source's intellect and one power. At a source with one power, intellect (with
  `090be689` and `71fc097b`) suffices to make the giving willed, and the chance
  rival must deny the source's intellect. By this route the case for willed
  giving at the source is at most as strong as the conjunction of intellect,
  one power and the holder identification; other warrants for will at the
  source that are independent of DNP_inv (e.g. the Fifth Way and governor
  routes, given the holder–root identification) would discriminate equally
  (law 6).
- **Overall:** the Θ.5 bridge is not a separate warrant against chance; in this
  slice, will at the first source is supported horizontally, through intellect,
  or through other routes to will.

**Revision conditions.** For the will side: an independent argument that an
invariant, patientless being cannot have a non-rational propensity (it would
warrant DNP_inv without begging the question); strong evidence for
deterministic fundamental dynamics (restoring DNP′'s inductive base); the
holder-root identification together with the intellect routes. Against: a
defended account of non-cognitive outcome specification at a simple being
(answering the determination point); a defence of per se chance that applies to
beings with invariant set-ups; a successful objection to the intellect routes'
perfection-transfer premise for a total existential source.

## 9. Claim versus type

| Record | Prose | Lean type | Check |
| --- | --- | --- | --- |
| `495a40ad` | giving exercises a power of the giver | `∀ v y x, GivesTo F v y x → ∃ p, PowerOf y p ∧ Exercises v y x p` | all worlds |
| `71fc097b` / `65e0179f` | will ⇒ some rational power / rational power ⇒ will | `∀ y, HasWill y → ∃ p, PowerOf y p ∧ Rational p`; `∀ y p, PowerOf y p → Rational p → HasWill y` | capacity level, both directions separate |
| `6e4b519b` DNP′ | same-set-up withheld giving ⇒ rational power, every being | `∀ y p x v, ExistsAt w y → access w v → ExistsAt v y → PowerOf y p → SetupSameIn y w v → GivesBy w y x p → ¬ GivesTo v y x → Rational p` | universal over beings at `w` |
| `55892476` DNP_inv | as DNP′, invariant beings only | as DNP′ with `SetupInvariantAt w y` replacing `SetupSameIn y w v` | weak version; strengthens relation registered |
| `a065c332`, `813a9181`, `9856239a` | holders invariant / intellectual / one power | `∀ y, PowerFor w y q → …` | holders at `w` only; not existence |
| `0050b6ed` | every GOD_4 exists at `w` and holds the power | `∀ g, IsGod g → ExistsAt w g ∧ PowerFor w g q` | not uniqueness; not every holder is GOD_4 |
| `5c1aba17` | every giving of a one-power intellectual being is by a rational power | `∀ y, HasIntellect y → OnePower y → ∀ v x, GivesTo v y x → ∃ p, PowerOf y p ∧ Rational p ∧ Exercises v y x p` | all worlds |
| `fdd2b1cf` | some holder is a willed two-way giver | `∃ y, PowerFor w y q ∧ WilledTwoWayAt w y` | existence at `w` inside `WilledTwoWayAt`; exercise-level "willed", unbridged to HAS_WILL_1; no contrastive explanation |
| `a9776d21` | invariant two-way givers have will | `∀ y, SetupInvariantAt w y → TwoWayGiverAt w y → HasWill y` | capacity |
| `66aecdd7` (reused) | God has will | `∀ g, IsGod g → HasWill g` | world-free conclusion from premises at one `w` |
| `ff9c8158` | laws and models | `Model.Controls` | surrogates only; links FixedGiver because law 14 relates it to set-up necessitation |

Every hypothesis of each theorem is a listed premise (bind-check). No source is
attributed; no claim record is added.

## 10. Remaining gaps and next tests

1. **Independent warrant for DNP_inv** (the decisive open test for the Θ.5
   route): a reason specific to invariant, patientless beings.
2. **Holder-root identification** (#1897 gap 2), needed to carry the intellect
   routes' HAS_INTELLECT_1 to the holder (premise `813a9181`) and for argument
   B's connection to the root. Built conditionally in
   [holder-root-identification.md](holder-root-identification.md): `813a9181`
   is derived from `0c27f65a` through the premise that NECESSARY_2 actual
   concreta are underived (NAR), which is the crux; argument B gets a consumer
   at `66aecdd7` that shares only the will-follows-intellect premise
   `090be689` with `571e36f0` and takes its intellect from `0c27f65a`.
3. **Root consumer of argument B:** a bridge from exercising a rational power in
   giving to the `Wills` relation of the q.19 a.4 node `a94c5dfc`.
4. **Certified difference** for the `strengthens` registration DNP′ → DNP_inv
   (#1598): DELTA would be DNP′ at beings without an invariant set-up; the
   equivalence needs excluded middle on invariance.
5. **Good-directed order** as a matched-scope discriminator (teleology family):
   not formalized here.
6. Probabilistic propensities with a measure (Mathlib Markov kernels) were not
   needed: only the same-set-up, different-outcome profile is used.

## 11. Edits outside the batch

- Existing records: DEF `7bc1d667` (FixedGiver) relabelled with its sense tag
  NECESSITATE_2; `docs/notes/pruss-power-premises.md` §6 and §7 point here.
  (Adding the willed sense to the audited disambiguation `941efd70` was tried
  and reverted: its bundle audit pins it; a separate disambiguation is used.)
- Generated: `TruthCore/Imports/Causality.lean`,
  `TruthCore/Imports/Results/Causality.lean`.
- New: the two Lean modules (Challenge generated), the spec and its generated
  records, ten definitions, disambiguations CHANCE `c18f084e`, NECESSITATE
  `5836e1f6`, POWER_FOR_VERSUS_ACTIVE_POWER `e5417243` and
  WILL_CAPACITY_VERSUS_WILLED_GIVING `8b3d47bc`, this note and three
  attempt records.

## Would selection that tracks a good identify an intellectual and willing source?

Fix the proposed ultimate bearer, its productive exercise and the order produced. Entertaining an intelligible end, possessing a power of will, and exercising that will in producing this order are three claims about that bearer. An agent can understand both alternatives and entrust their selection to a lottery. Conversely, a selector can reliably produce a beneficial result under a standing physical rule. The conditional [holder identification](holder-root-identification.md) prevents transferring predicates between different bearers only when its actual-root and modal premises hold, including the disputed necessary-actual-concreta-are-roots bridge. It supplies no new evidence that the common root is intellectual. Given the holder's intellect, one power and the stated will/power bridges, the registered willed-giving argument B already applies.

**A matched good-directed probe.** Two feasible routes supply a destination; which route delivers more of a needed resource depends on an independently inspected blockage. Assign equal costs and keep the destination and supply fixed. The favoring fact is thus specified before looking at the selection. An agent might understand the blockage as a reason, adopt a route and use its own power to implement it. A weighted mechanical diverter can favor an open route from a pressure signal upstream of the junction, without evidence that it apprehends either route *as a means to that end*. A merely incidental correlation with pressure and a mechanism responsive to the actual obstruction are different rivals. The diverter is an example of a realizable selection rule, not an argument for a designer-free ultimate mechanism; being built by an engineer would bear on the engineer's authorship and need not make the valve intellectual. The actual pressure can also be sensed by an agent. The hypothesis being compared fixes how each uses it.

In the following diagnostic, true selects route A; the Boolean fact indicates which route is favored. Four equiprobable tickets give transparent conditional likelihoods. A stipulated responsive policy selects the favored route on three tickets, and an insensitive fair selector on two. A pressure-guided policy has precisely the responsive table when pressure tracks the fact. Reverse the pressure indication while keeping the blockage fixed, and the pressure-guided selector succeeds on only one ticket. A chooser with independent accurate information about the blockage who retains the purpose and the responsive policy still succeeds on three. A chooser relying entirely on the misleading gauge might fare just like the valve. Equally, an impersonal detector which tracks the obstruction itself would retain three successes too. These are predictions for the specified information channels. No premise assigns independent repeated trials or prior probabilities to world creation.

```lean
namespace ChoiceEvidence
-- Four equally weighted tickets in the order listed. True selects plan A.
def tickets (a b c d : Bool) := [a,b,c,d]
def responsive (favoursA : Bool) := tickets favoursA favoursA favoursA (!favoursA)
def neutral := tickets true true false false
def matchCount (fact : Bool) (xs : List Bool) := (xs.filter (· == fact)).length
theorem discriminate (fact : Bool) :
    matchCount fact (responsive fact) = 3 ∧ matchCount fact neutral = 2 ∧
    matchCount fact (responsive (!fact)) = 1 := by cases fact <;> decide
-- Under aligned inputs even the ordered plan outputs match, ticket by ticket.
theorem aligned (fact cue : Bool) (h : fact = cue) :
    responsive fact = responsive cue := by rw [h]
#print axioms discriminate
#print axioms aligned
end ChoiceEvidence
```

Both checks elaborate locally without axioms. A favored result in the calibrated comparison has likelihood ratio (3/4)/(1/2) = 3/2 against the fair policy, and ratio 1 against the aligned responsive policy. Thus good-directed order can carry *relative* evidence against a specific indifferent propensity. Renaming the responsive distribution “will” adds no evidence against an equally responsive impersonal source. Nor does a single actual order establish either likelihood at a patientless invariant source. The two route settings serve as comparative probes; the computation makes no claim that God has external inputs, that the probes correspond to accessible worlds of a divine agent, or that authorship requires stochastic action.

**Provisional judgment.** The positive case gains content where evidence identifies both an end whose fulfillment conditions can be assessed independently of success and this source's apprehension and adoption of that end guiding the actual production. This can explain why a suitable order was produced *for the sake of* a good, over and above its being selected by a good-sensitive tendency. In familiar agents, uptake of a corrected account of the blockage, use of the same end to devise previously unavailable means, and traced practical control of execution give defeasible grounds for attributing those roles. A new cue test can disfavor a particular physical proxy; behavioral flexibility alone does not establish ownership of reasons. A mechanism meeting a defensible functional account of apprehension and practical control would itself be a candidate for agency. [Existing authorship tests and limits](optimal-creation-choice.md#rational-authorship-versus-brute-selection-2026-11-23)

Applied to the ultimate source, the impersonal rival pays for a productive propensity with the relevant ordering, and the personal account pays for intrinsic intelligible content and directed exercise with an appropriate fulfillment condition. Contingent production and order alone leave the first rival standing. Evidence independently grounding intentional content in this very source and tracing realization to its exercise would favor the personal account. An independent derivation of the common root's intellect followed by the holder and will bridges would also discriminate. The diagnostic establishes neither the root intellect premise `0c27f65a` nor `55892476` (every invariant-set-up withheld giving uses a rational power); the primitive rational-power classification in the latter carries a further application burden. Even will as capacity leaves the token exercise question open without an exercise bridge such as `5c1aba17`. This adds no graph edge or claim about historical authors.
## End requirement, policy requirement and productive fixity (2026-11-25)

**Draft research checkpoint, not a new certified argument.** Continues #1737,
#1941, #1944, #1947, #1953, #1955, #1962 and #1963. It specifically tests the
WN rivals left open by #1963 and the connection between reason-guided exercise
and contingent recipients. It does not replace #1962's operative-direction
investigation or #1955's effect/action/perfection comparison. Reuse
[the NAR note](nar-derivation.md), [the graft map](orphan-graft-map.md),
[holder identification](holder-root-identification.md), and
[the selected-effect note](optimal-creation-choice.md). #1962 at
`9a4265d0aee3c1b7e684d54ce4cd04cd78c7dcdb` is external PR evidence, not a
patch included here. Its formative-governance and composition discriminator is
retained. No new source attribution is made; historical formulations in the
earlier notes are not additional premises.

### 1. Fix the explanatory target before comparing accounts

Grant one necessary, invariant, productive n, the actual effect, genuine
contingent exercise, objectively good-directed propensity, and the same
productive efficacy and admissible alternatives on both sides. The rival is
not indifferent CHANCE_3: it can discriminate goods, exclude bad outcomes and
produce its effect directly. CHANCE_3 is a classification of giving by a
non-rational power, not a denial of all teleology. Its necessity is the
bearer's necessity, not a rigid act or a fixed complete effect.

There are four questions about this very n: (i) what makes the recipient
actually exist; (ii) why this exercise is intelligible under an independently
specified end or good; (iii) whether the good is actually apprehended and
operative as a practical reason of n; (iv) what settles the exact exercise
rather than every other permitted one. The first two can be answered by a
genuine impersonal teleology. The third supplies a different explanandum,
intentional authorship, not automatically a stronger explanation of (i).
The fourth remains open for either nonnecessitating account if the demand is
a further determining explanation. Neither a primitive selection rule nor
the phrase "free choice" settles it. A direct reason-guided productive
exercise is a substantive candidate for stopping under nonnecessitating PSR,
just as a direct objective propensity is; grant or challenge the adequacy of
both at the same scope.

### 2. A new application of the WN fork: requirement by a good versus by a policy

WN `0266eac2` is `RationalFixedGivingIsRequired`, not a normative
maximization theorem: for every y,p,x, if y owns rational p, exercises p
toward x at w and is `FixedTowardAt` from w, then `EndRequires y x`.
Fixity requires giving at w and at all accessible worlds where y exists.
`EndRequires` is the means-to-end relation, not modal co-existence.
SS `85f3fea2` says no being distinct from an actual root is required by
its end. The latter is not a theorem that every creative policy is optional.

Compare independently specified complete outputs S and three different
sources of a constraint on them:

* E: without x, the giver cannot attain its own end (the intended WN sense).
* P: a proposed norm or policy admits no complete decision omitting x.
  Such a policy can concern communication of the end, not attainment of it.
* F: all actual/accessibly realized givings include x (the existing fixity
  sense, restricted to a source which gives x here).

E and P must not be defined using F. Even a norm P that is actually binding
does not entail F without a bridge from obligation to invariant compliance.
If the compliance is granted, P can account for F without E. Conversely
absence of P does not imply absence of F: a rational or impersonal source can
invariably supply something it has no duty to supply. Multiple distinct
complete outputs can all share x. This is the exact reason that free exercise
toward some effect is weaker than WN/SS and cannot answer #1963's selective
rival. The issue is a normative and productive bridge, not the already known
unique-optimum collapse.

**A discriminating strict-improvement criterion for the world-level rival.**
Use the actual `ActualRootsGiveOptimalCompleteOutputs` of
`TruthCore.Causality.NarGrafts`: fixed feasible sets of beings and a fixed
partially ordered quality; at w and each accessible v where the actual root
exists, its exact giving set is optimal. Take an actual root n and a being d
distinct from n. Suppose every feasible complete output S omitting d has
some feasible T strictly better than S. Then no optimal complete output can
omit d: if S were optimal, T would contradict its greatest-quality status (`Optimal` is membership in the feasible set
and `IsGreatest (quality '' feasible) (quality S)`, not merely being
undominated). Consequently the optimizer is fixed toward d in the giving sense.
This uses neither a unique optimum nor an exhaustive order. With factive
giving and a necessary root it also yields d's existence throughout the
specified worlds, but not d's ungroundedness. To conclude a counterinstance
to WN additionally require rational exercise at w and that d is not
end-required; to instantiate the recorded selective-diffusion rival
`ea1425c0` further require two-way giving toward some being. The optimizer
alone asserts neither. This is an analyst argument, not a Lean result or
refutation of either rival.

Conversely, **given an existing optimum**, if every optimal complete output
includes d, choose any optimal T. For any feasible S omitting d,
quality(S) ≤ quality(T); equality would make S optimal, contrary to its
omitting d. Hence quality(S) < quality(T). Thus the strict-improvement
criterion characterizes the common recipient core given existence of a
greatest feasible quality, without assuming linearity or injectivity. It
is not equivalent without the existence condition: two incomparable
quality values on the feasible outputs ∅ and {d} have no greatest value,
so the universal claim about optima is vacuous but the improvement test
fails. An actually existing root subject to the optimizer at w has an
optimum by the rival's own condition. This is a bridge to test using the
existing `Optimal` vocabulary, not a registered consequence.

The relevant stronger hypothesis is strict improvement of *complete*
decisions without d, not the isolated goodness of d. It may be motivated by
benefit to another recipient if the additional good is compatible with every
relevant cost and good, and with the same full-world feasibility constraints.
It is not licensed by the mere fact that d could be good. Strict
improvability of every decision (not merely those omitting d) would instead
leave no optimal decision at all, as already tested in #1737. The rival
does not need that stronger thesis. It also need not count the source's own
intrinsic perfection as increasing with the quality of its effects.

**Structural nonvacuity target.** Use the full powerset of {d,a,b}, including
omission, and a quality with two units for the presence of d, plus one for
exactly one of a and b being present. The two tied optima {d,a} and {d,b}
share d. At one situation give {d,a}, at another {d,b}; n exists throughout
and each output is supplied by it. Stipulate a distinct intrinsic end of n
requiring none of d,a,b. These assignments realize the output/quality
structure, including d's invariant presence and a's two-way giving.
No identity of these assignments with a complete CausalityFrame or a
metaphysically possible strict-simple source is claimed; the quality and
end assignments are stipulated, and no rational power or genuine intellect
is represented. The positive quality of d is not derived from its presence;
the example tests the logical relationship between policy and end
requirement. It is an independently specified comparison with an objective
ranking, not indifferent randomness.

### 3. Due perfection as a positive alternative to mandatory maximization

The personal case should not rely on a blanket principle that the will is
free precisely because it chooses. Consider instead two distinct normative
grounds: a perfection due to an existent bearer (or a role actually adopted
in exercising its own power), and an antecedent obligation to adopt that
role or bring that bearer into existence. These are different. If a
producer adopts an end of giving a recipient a certain good, faithfully
realizing the recipient-directed end is an intelligible excellence in the
actual exercise. The producer's goodness does not thereby require adoption
of every compatible beneficial end. Due perfection is more than mere
absence of a defect in execution: a good independently specified end,
genuine practical governance, and adequate realization together provide a
positive reason for the act, not just permission to act. But the act's
excellence and moral permissibility remain distinct.

A concrete positive policy: if a producer undertakes to create a recipient
of type R, it must provide what is due to R, and if it undertakes a
relationship with a determinate beneficiary it must respect that
relationship. It has no obligation *on the basis of these conditional
requirements alone* to create all possible R or to undertake that
relationship. This policy permits an omission and two differently excellent
complete outputs if they all meet these constraints. An independent
antecedent duty to potential recipients, a norm of obligatory
self-communication, a promise, or an overall moral dominance relation can
override that permissibility. Such duties cannot be ruled out by saying
the recipients do not yet exist; duties concerning future persons are a
serious counterexample to an unrestricted denial. Nor does the root's
intrinsic self-sufficiency imply that the moral quality of its exercise
cannot be compared. These are the policy premises that need warrant.
The classical account's positive candidate is voluntary communication of
a possessed good, not a good to be acquired by the producer. A recipient's
perfection can genuinely matter without increasing the producer's intrinsic
perfection. The policy is a philosophical candidate, not a new definition
of the corpus's `00e962ae` or a conclusion from it.

For an actual giving of d that does not serve an indispensable means to the
root's own end, distinguish these tests:

1. End-preserving feasibility: a complete alternative omitting d is feasible
   while the source's own end remains attained.
2. Due-perfection permissibility: some such alternative is permissible under
   the same independently justified requirements, with all actual obligations
   and incompatible goods accounted for.
3. Real exercise: at some accessible situation with n present, n actually
   gives according to such an alternative.

The third plus actual rational giving of d suffices to rule out fixity of d;
the first two give positive reasons to seek it, but are not that bridge.
To obtain WN on the scope of actual root givings, one needs this accessible
omission for each non-end-required recipient, not realization of every
possible complete output. Claiming availability by the definition of
freedom would just restate WN on that scope. The genuine warrant would
come from a defensible specific nonnecessitating exercise principle,
coupled with the first two tests, and not from moral permission alone.
Even two options sharing d may both be permissible and realized. This
pinpoints why the #1947 mixed-mode model is not defeated by the positive
argument for nonmaximizing goodness.

### 4. Same-source formative governance, not another output discriminator

The approved prior comparisons establish that extensional responsiveness
does not distinguish an apprehended reason from an objective propensity.
The positive intentional hypothesis adds a truth-evaluable practical
understanding of the relevant good as a good and of the effect as its
realization, together with the exercise's being governed by that
understanding. A fit between an actual result and a good-sensitive rule
is not enough. A rule can instantiate the same independently justified
norm, and a functional account that actually realizes understanding and
practical control receives the same agential credit. There is no
in-principle output test against a rival matched on all of these extensional
consequences.

The next ontological challenge from #1962 is more precise than counting
intellect and productive power as two descriptions. Compare:

* One intrinsic intellectual actuality, productive in virtue of the
  intelligible form it actually adopts as the measure of this exercise.
  The norm of correct realization is not invented after the output, and
  no prior selecting event or passive cognitive reception is posited.
* One intrinsic noncognitive productive actuality with a good-sensitive
  profile; the actual effect is genuinely supplied by it. This has no
  apprehension of the good as a reason, but can have an objective end.
* One purportedly simple source that actually understands the good, yet
  has a blind selective character explanatorily sufficient for its exercise.
  If the understood content is only speculative, neither one power nor
  identity of the bearer establishes that cognition governs production.

For the third case, a route to exclusion would show that its blind
selective character must be a really distinct intrinsic productive
principle in addition to its intrinsic understanding. To warrant this,
show that the **constitutive ground of the exercise** contains an intrinsic
actual determination whose explanatory role cannot be realized by the
source's intellectual actuality; and that the asserted independence is
one of real intrinsic principles, not merely non-equivalent descriptions,
logical independence, two extrinsic termini, or independent modeling
parameters. Given an independently warranted strict simplicity constraint
against that real distinction, the conjunction would be inadmissible.
Merely observing that the production could be modeled without a cognition
variable does not show such an intrinsic constituent. Conversely merely
identifying both principles with n's esse does not show that the productive
role is intellectual *as such*. An exclusively intellectual active
principle which actually forms this exercise could satisfy the proposed
constitutive condition, but the exclusively intellectual and formative
interpretation are substantive commitments. A second selector is not
posited just to solve the problem.

This identifies a conditional explanatory advantage without requiring a
determining reason: if the actual apprehended reason is constitutively
operative, it explains why this productive act is intentionally directed
toward an independently intelligible good, not merely why an outcome fits
a rule. Reasons for giving under a recipient role can be nonnecessitating
and real even when more than one particular recipient or complete order
would realize that role. A role under which a particular recipient is
actually, nondeviantly supplied explains production of that recipient
under that role; it does not establish a prior rigid individual choice,
all details, or the recipient's own existence-good as explicitly willed
for it. Do not replace the latter by coarse purpose in `a94c5dfc`.
This extends the same-source case only conditional on actual formative
governance, not on an arbitrary Rational flag.

Simplicity and immutability allow a candidate one-act account with stable
intellectual nature and distinct contingent productive termini. Their
compatibility with actual directed exercise, not just stable possibility
knowledge, remains open. If the exercise's formative actuality depends
on the product and is identical with esse, #1961's grounding-promotion
problem applies under its explicit calibration; a true relational
description of completed production does not give this premise. Neither
side gets to manufacture a direction of existential dependence by
renaming the outcome. The particular recipient must actually be produced,
not supply the truthmaker of a retrospective attribution of intent in
place of the productive principle.

### 5. Matched rival assessment and graph connections

| Account | Positive resources at the same explanandum | Discriminating remaining price |
| --- | --- | --- |
| Necessitarian source | Stable productive law; determinate effect explained by fixed efficacy | Incompatible with granted genuine contingency only under the already established rigid necessity/efficacy bundle. Not a personality test. |
| Objective propensity | Direct supply; a nonnecessitating invariant tendency favoring independently grounded goods | Actual exercise can be primitive; no actual apprehension as a reason. The personal account must meet the same stopping standard. |
| Impersonal teleology | Genuine ends, independently specified fulfillment, productive directedness | Explain the ground of directedness and actual exercise. Not defeated by good-directed order or normative policy alone. |
| Selective necessary diffusion | Positive reason for an invariant core of gifts and contingent exercise toward others | Must ground invariant communication or its necessary policy rather than infer it from the source's having a good. Not defeated by one power, SS or freedom toward another effect alone. |
| Complete-output optimizer | Objective whole-decision ranking; ties allow contingency; strict improvement can fix individual recipients | Needs warranted feasibility, ranking, existence of an optimum, a binding maximizing norm and invariant compliance. Due-perfection permission does not prove metaphysical withholding. |
| Noncognitive productive powers | Intrinsic power produces intelligent or purposive effects, including mediated production | Intrinsic intellectual adequacy is a distinct open causal-perfection question, not resolved by either output intelligence or labels of power. |
| Rational direct authorship | Actual intellectual content, nondeviant practical governance and existential supply; good-directed finite exercise not requiring self-improvement | Same-source intellect and formative bridges, exact-exercise sufficiency, defensible policy and compatibility with strict simplicity. A uniquely determining reason is not assumed. |

Existing connections, not new proof edges:

* `29818edd` is GOD_4 HAS_INTELLECT_1 (`GodHasIntellect`); `66aecdd7`
  is GOD_4 HAS_WILL_1 (`GodHasWill`). Existing `571e36f0` uses intellect
  plus `090be689`. #1941 A (`b5b84276`) uses `090be689`, rational-power
  bridge `71fc097b` and actual exercise `495a40ad` to reach `5c1aba17`
  in the one-power setting. B (`963e9689`) reaches `fdd2b1cf` under its
  withholding, actual contingency, invariance, holder-intellect and one-power
  premises plus A's conclusion. #1944 `834ddcfa` connects `fdd2b1cf`,
  `0050b6ed`, `5f93d4f0`, `65e0179f` to `66aecdd7`; holder/root
  identification and the sense bridges remain required. These are capacity
  and exercise classifications, not an established formative-governance
  theorem. `29818edd` alone does not identify the holder with the root
  or establish actual intellect-directed production.
* The new policy analysis concerns the **root-restricted** use of WN
  `0266eac2` in #1947 N3 `d6588ea7`. That theorem also uses EM, common
  intellectual root `0c27f65a`, `5c1aba17`, root one power `06145e71`,
  root giving bridge (b1) `2dd1f217`, and SS `85f3fea2`. N1 then
  requires its own common-root and (b2) premises to derive NAR; none is
  discharged here. The #1963 narrow being-level refutation does not
  resolve either complete-output or selective diffusion.
* Existential PSR `608a262d`, BX1 and BX2 lead to B2 `8a8d00e9` through
  `7bf9cb77`. Rational authorship is a candidate concrete productive
  explanation; neither partial contrastive coverage nor the source's
  necessary existence establishes universal PSR, those bridges, or
  determining closure of the actual decision. Keep giving, grounding,
  and existential causation distinct.
* Goodness `00e962ae`, intrinsic-perfection/transfer `64498e7e`,
  `f8ba2429` and the prior recipient-directed will results retain their
  original scopes. Positive goodness as due perfection and the freedom
  policy require their own normative and modal application. A superior
  created effect does not alone show an intrinsically superior source or
  more morally excellent decision.

**Scoped provisional assessment.** Actual rational guidance has positive
explanatory content beyond conformity with an objective good where the
explanandum is intentional production. Under that very interpretation it
is not a bare label. For the thinner explanandum of contingent intelligible
productive order, the impersonal good-sensitive rival remains on parity
unless independent evidence connects n's intrinsic intellectual actuality
to this exercise. The policy analysis sharpens a live rival of WN: a common
core of gifts may be fixed by a substantive maximizing or diffusion policy,
even where no such gift is required to attain the source's own end and other
gifts are contingent. A due-perfection policy can license a good-preserving
omission without obliging the source to maximize created goods. Its actual
necessity, permissibility and accessibility are separate questions.
No new warrant is assigned to any registered premise as established and
no rival is defeated. The strongest standing package is a necessary
noncognitive productive source with intrinsic invariant, objective
good-directed nonnecessitating powers and a still-to-be-defended rule fixing some
positive communications; the purely impersonal case need not grant the
rational-exercise conjunct of the registered selective rival.

**Reopening conditions.** (1) Derive formative relevance from a defended
account of the same source's intrinsic active principle or construct a
positive strict-simple intellectual-but-blind rival preserving actual
cognition, actual supply, recipient and the same end. Inspect real
composition, not descriptions. (2) Defend the normative antecedent duty
to maximize or diffuse (including complete-decision opportunity costs),
or an independent due-perfection permission argument covering omission.
(3) Provide an actual accessible exercise bridge omitting each selected
non-end-required being without weakening the admitted metaphysics.
(4) Establish the relevant recipient's existence-good as intentionally
willed, or delimit the weaker role-intention result. If the remaining
proposal merely stipulates an invariant output or names the selection
Rational, the known comparison is repeated rather than advanced.

Verification boundary: the present checkpoint adds prose only. No new
registered proof, claim, definition, sense, source or frontier edge.
The local checkout/Lean/Rust toolchain and fresh independent semantic
worker are unavailable in this execution environment. Related, dossier,
novelty, semantics and computed frontier-diff have therefore not been
run; direct GitHub record/definition inspection and the stated PR evidence
are not substitutes. An independent challenge of the actual draft and
applicable CI remain required before reliance as reviewed support.


### 6. Reproduced analyst controls (unregistered)

Executed the following dependency-free Python 3 diagnostic on this checkpoint.
Its finite integer rankings are a test of the abstract quality argument,
not a metaphysical measure of goodness, a Lean model or a substitute for
the existing kernel checks.

```python
from itertools import product

X = tuple(frozenset(i for i in range(3) if mask & (1 << i))
          for mask in range(8))
d, a, b = 0, 1, 2
quality = lambda s: 2 * (d in s) + int((a in s) != (b in s))
opt = [s for s in X if all(quality(t) <= quality(s) for t in X)]
assert opt == [frozenset((d, a)), frozenset((d, b))]
assert all(any(quality(t) > quality(s) for t in X)
           for s in X if d not in s)
assert all(d in s for s in opt) and any(a not in s for s in opt)
assert frozenset() in X and frozenset((a,)) in X

checked = triggered = 0
for q in product(range(3), repeat=len(X)):
    highest = max(q)
    improvement = all(
        any(q[j] > q[i] for j in range(len(X)))
        for i, s in enumerate(X) if d not in s
    )
    winners = [s for i, s in enumerate(X) if q[i] == highest]
    core = all(d in s for s in winners)
    assert improvement == core
    checked += 1
    triggered += improvement
print(checked, triggered)
```

Result: two tied optima; all 6,561 rank assignments pass, 1,055
satisfy the improvement condition. The enumeration only covers a
nonempty finite, totally ordered quality image with an optimum.
The partial-order argument above is separate.

**Omission controls (scope only).** Retain the same feasible outputs.
A due-perfection policy admitting all the outputs after actual recipient
duties are satisfied permits ∅ and {a}; realizing only {d,a} and {d,b}
still leaves d fixed. Thus permission to omit d without an accessible
exercise omitting it does not suffice. Realize {a} instead of {d,b} at
the alternative situation: d is no longer fixed, although the actual
giving at w and the due-perfection policy remain the same. The
world-level optimizer under the original quality would no longer hold;
it is the actual accessible omission, not the label of the policy, that
breaks fixity. No claim about metaphysical feasibility or intrinsic
constitution follows.

**Author's self-sweep (not independent review).** These are output
surrogates, not instances of the full ontology; both personal and
impersonal proposals receive the same productive/coverage credit;
no new historical reading is attributed; WN's actual and accessible
giving, rational exercise and end-requirement quantifiers are preserved;
the quality/feasibility assignments and absence of intrinsic constitution
are explicit; the root-restricted WN application is distinguished from
the unrestricted theorem and the other sense bridges are retained;
the actual delivery remains a draft pending independent review and CI.
No new stating claim or formal theorem is proposed, so no new claim/type
pair or proof certificate is represented. The full repository self-sweep
and CLI validation remain outstanding.


## Can the same intrinsic actuality understand and produce blindly? (2026-11-25)

Continuation of the preceding checkpoint and #1962's concrete real-composition
test. Target `29818edd`, `66aecdd7`, the actual giving classified by
`5c1aba17`, and the registered contemplative-intellect rival
`2537adb1` to `090be689`. This is a semantic and warrant investigation,
not a new power ontology or a mechanically certified consequence.

### 1. The strongest standing intellectual rival must be distinguished from the wholly impersonal one

First grant the same necessary n, actual existential supply, intrinsic
invariance and genuinely alternative realizations. Then **add actual
intellectual apprehension** of n's own goodness to both sides of this
conditional test. The purely noncognitive rival is not thereby defeated:
its denial of this addition is still a separate challenge to the intellect
routes. See [causal perfection and the cognitive first source](causal-perfection-transfer.md)
and [teleology and the common root](teleology-first-mover.md).

Distinguish three claims:

1. n's actual giving exercises an owned power classified as rational;
2. n's actual giving is performed for an apprehended good, in virtue of
   the actual exercise of its intellectual inclination toward that good;
3. the particular identity and every detail of the actual recipient are
   specifically determined by that practical apprehension.

The existing theorem `oneIntellectualPowerGivesWilledGiving` (result
`b5b84276`, conclusion `5c1aba17`) gives (1), not (2) or (3).
Inspect its actual proof: it obtains a rational power from
`WillFollowsIntellectReading` (`090be689`) and `WillIsRationalPower`
(`71fc097b`), an owned exercised power from
`GivingExercisesOwnPower` (`495a40ad`), and identifies those powers by
`OnePower`. The conclusion is
`∀ y, HasIntellect y → OnePower A y → ∀ v x, GivesTo F v y x →
∃ p, A.PowerOf y p ∧ A.Rational p ∧ A.Exercises v y x p`.
No end, apprehended content, occasion of adoption or constitutive mode of
actual exercise is in that conclusion. The argument validly excludes
the two-power chancer of #1941 under its premises, not every account of
nonoperative cognition.

The rival denying `090be689` (some intellect without will,
`2537adb1`) differs from a source granting actual rational self-love
but denying that creation proceeds from it. The first rejects the
capacity conclusion; the second can grant it and reject (2).
A third, genuinely purposive source grants (2) but leaves the exact
recipient-selection contrast unsettled. It is not a wholly noncognitive
producer. Accordingly a failure to explain x rather than y does not
establish the absence of rational governance.

### 2. Positive rationale: exercise *qua* an intellectual inclination

Reopen the existing semantic calibration of `AgencyFrame.Exercises`,
not the formal proof. `Rational` (DEF `b8061228`) is intended to name
an inclination following intellectual apprehension of a good;
HAS_WILL_1 (DEF `7c64b499`) is also an inclination toward an
intelligibly apprehended good. An actual exercise **as that inclination**
is more specific than the occurrence of an effect through a power
which also has a rational classification. The latter does not say
which aspect of its owner supplies the formative measure of this
actual production.

A substantive source-based motivation for the stronger interpretation:
Aristotle, [Metaphysics Θ.2 (1046b4–15) and Θ.5 (1047b31–1048a24)](https://classics.mit.edu/Aristotle/metaphysics.9.ix.html),
explains rational powers by the account possessed in knowledge. Medical
art can produce health or disease because it understands the relation
of the positive state and its privation; the appropriate desire
determines its actual employment. A mere range of possible contrary
effects is not the distinctive explanatory feature of the art.
The one-way manifestation thesis for non-rational powers in Θ.5 is
exactly what #1941's CHANCE_3 discussion disputes. Do not infer its
universal applicability from this passage; noncognitive powers may
have multiple possible manifestations. The useful feature of the
contrast is the role of the understood account, not the number of
outputs.

Aquinas, [ST I q.25 a.1 co., ad 3–4 and a.5 ad 1](https://www.newadvent.org/summa/1025.htm),
distinguishes the actual productive principle from a passive capacity
or a principle distinct from the divine action; ad 4 identifies
knowledge, will and execution in reality while distinguishing their
accounts. Article 5 ad 1 separates the scope of divine power from what
is actually done under foreknowledge and preordination. The latter
claim supports actual practical governance, not the inference that
identity of power and cognition alone yields such governance.
These are readings of the linked primary translations, consulted for
the argument, not new pinned attributions or a proof of the classical
account. The previously read q.19 a.4 and q.14 a.8 retain their
respective formative and appetite conditions.

**Independent ordinary-case test of the semantic bridge.** A physician
produces a beneficial outcome either by deploying a correctly understood
treatment because it will restore health, or by carrying out an
independently imposed prescription that she correctly understands but
does not follow for that therapeutic reason. In the latter case a
different reason may actually govern her action; it is not necessarily
nonintentional. A noncognitive dispenser can also achieve the same
therapeutic outcome under an objectively appropriate rule. In each case
the end's independent success conditions and the productive outcome may
coincide. The first action is an exercise of medical expertise as
practical knowledge; the second may exercise it in execution without
the therapeutic end itself guiding adoption; the third is not an
exercise of intellectual expertise unless an independent account
establishes cognition. The diagnostic is not a test based on observing
a successful treatment. Its warrant comes from actually tracing the
agent's uptake and use of the therapeutic reason. Implicit or tacit
practical cognition can satisfy this, without conscious deliberation
or verbal report. This example concerns familiar composite producers;
it is not evidence of a simple-source world.

This provides direct defeasible warrant for a **qua-exercise
calibration**: when a giving truly exercises the rational inclination
in its formative mode, at least some apprehended good is operative in
that giving under an independently interpretable description. This
is a restricted claim about the nature of exercising an intellectual
inclination. It is close to constitutive of that stronger sense,
not an independent theorem that all acts originating in an intelligent
subject have this character. The difficult substantive premise is
that the existing existential giving is an exercise **in this sense**
rather than an effect of a differently specified productive aspect.
A proof that merely renames `Exercises` would be a transcription.
Do not strengthen the frozen dictionary or theorem.

There is a useful conditional consequence: if the actual giving is
indeed the exercise of n's unique power *qua rational inclination*,
a wholly blind account of that very exercise fails. No separate
argument that an unknown blind constituent must exist is required in
this conditional case. The objective rule may still govern residual
realization within what is adopted; the result is only (2).

### 3. Test the alternative: real constitution, not numerical labels or explanatory isolation

Return to #1962's challenge. There are at least two genuinely different
ways to develop the intellectual-but-blind account.

**Independent intrinsic constituent.** The rival says an actual
productive determination p is sufficient as the blind formative
principle independently of the source's actual intellectual
determination k, and that p and k are really distinct internal
constituents (not merely distinct concepts or termini). Then the
combination is incompatible with a simplicity principle excluding
those constituents. In particular if p is an actual intrinsic
ground of k as an actuality, and strict simplicity identifies both
with n's esse, an irreflexive actual-grounding interpretation would
give self-grounding; this is an application of the #1961
identity/dependence boundary, not a new cycle proof. It does not follow
if p grounds a truth about k, provides the content it knows, or is
just another description of k. Establishing actual constitutive
dependence or real plurality is the burden; two individually
indispensable explanatory descriptions of one actuality do not suffice.

**One actuality, different explanatory aspects.** The strongest
remaining intellectual rival identifies the intrinsic principle of
production and the actual principle of cognition with a single
actuality. It has a positive objective directedness to good, and knows
itself, including the character of that directedness. Its knowing
is contemplative; the actual choice of a permitted manifestation
proceeds from its primitive propensity, not from an apprehended reason.
No extra inner selecting event or new intrinsic state is stipulated.
A fixed self-content about the necessary source avoids a claim of
contingent intrinsic foreknowledge; explaining the particular
contingent truth in that knowledge remains a further #1737 obligation.
This is a proposed ontological explanation, not a demonstrated model
of strict simplicity. It can even include an actual inward rational
orientation to its own good, while rejecting creative exercise *qua*
that orientation. Whether it can give a satisfactory unitary
constitution of these roles is a real unresolved question.

The identity of the actuality designated by p and k allows
substitution in an extensional causal relation. It does **not**
license substitution in a claim of productive relevance under a
particular explanatory aspect. If n acts, and n has actual
self-understanding identical with its actuality, it follows that
the actor is the self-understanding being; it does not follow that
apprehension of the good explains the exercise *as a reason*.
Conversely the failure of that explanatory substitution does not
entail that the aspects have distinct real bearers or parts.
Necessary co-presence of aspects would not establish identity, and
an independently describable aspect is not thereby a constituent.
Thus a proposed inference from the blind role's explanatory isolation
to ontological composition needs a defended bridge in the existing
composition analysis (`ca07cae9` is a causal claim about composites,
not that criterion).

For the personal account a positive unifying interpretation is
available: what n actually understands as a good supplies the
intelligible measure of its own active exercise, and the productive
actuality just is that intellectual inclination in effective exercise.
It gives one constitutive explanation of the correspondence between
the recognized end and practical direction without making the
cognition a second efficient cause or adding a separate choice-event.
This earns comparative credit **if** the formative relation is
independently warranted as an actual relation of n, not merely
specified in the hypothesis. The unified impersonal account can
provide its own common-nature explanation of objective direction
and self-knowledge, and the fully noncognitive account does not
owe an explanation of n's cognition unless cognition is established.
Do not rank the theories by counting primitive descriptions. The
relevant contrast is whether the recognized end has the specified
productive role; coherence of the one-act personal and one-act
contemplative accounts remains to be warranted.

### 4. Narrow the bypass test to what is actually explained

An independently specified end E might be fulfilled by x or by y.
Suppose this source apprehends E, actually exercises its power for E,
and directly supplies x as a realization of E. Suppose that the
propensity among E-realizations leaves x rather than y
nonnecessitated. This is a **partially specified rational exercise**:
the actuality of production under E and the remaining selection
contrast need not have the same explanation. No internal mechanism
distinct from n is inferred from the two explanatory scopes.
It is not a demonstration that such a source is possible under
strict simplicity or that a reason can fail to necessitate an
identical rigid act while retaining all #555 premises.

Compare the bypass challenge under matched actual supply:

* If the noncognitive propensity accounts for the occurrence and
  direction of the complete exercise even without the supposed
  practical governance, and the latter merely tracks the effect,
  then the offered practical explanation has not been shown to be
  operative.
* If it only accounts for which eligible realization occurs **given**
  an actually end-directed giving, it does not provide a replacement
  explanation of the actual giving's end-directedness. If the
  apprehended end governs that giving, the residual indeterminacy
  cannot on its own turn the entire act into blind production.

These are alternative positive dependence interpretations, not
interventions which switch an essential cognitive feature off in a
world where the same simple necessary source exists. Mere modal
availability of a different route to the same effect is not actual
bypass. A rival could defend the first interpretation by locating
the actual formative principle in a blind nature; the personal
account could defend the second by establishing exercise *qua*
the intellectual appetite. The matching standard is actual
explanatory responsibility, not a requirement that one account
uniquely determine the result while the other need only produce it.

Application to `a94c5dfc`: producing an actual x for E may still
mean producing x as a means or as a foreseen concomitant rather
than willing x's own existence-good to x. For example, purposefully
making a habitat may also deliberately create a support organism
for the benefit of other inhabitants without that organism's own
good being the producer's object. This is an intentional-scope
test, not a claim that such a producer is perfectly good or that the
support organism is not good in being. The existing recipient-specific
willing bridge still needs positive warrant. Nor does an actual
creative exercise require that the source seek an unpossessed good.
The [own-good exercise analysis](causal-perfection-transfer.md#from-self-understanding-to-love-of-ones-own-good)
gives separate conditional grounds for actual inward love, not
an argument that every external gift is a communication of it.
This preserves `00e962ae`, self-love and recipient-directed
goodness as distinct commitments.

### 5. Assessment, graph destination and next discriminating evidence

The narrow semantic step from actual exercise **qua will** to
direction by an apprehended good has a substantive rationale from
the nature of intellectual inclination and practical knowledge.
It need not demand a further intentional event mediating the
one source's production. The main application burden has moved
from an unqualified appeal to real composition to the actual
individuation of the productive exercise. The two-power rival is
already conditionally excluded by #1941; the proposed one-actuality
contemplative rival is not excluded by the same identity proof.
Even granting intellect and self-love, actual governance of
external production remains open. This is a scoped interpretive
assessment, not a change of warrant or status of an existing
registered premise.

The existing graph route to `29818edd` supplies the intellect
predicate, not actual uptake of any particular end. `090be689`
and `71fc097b`, with `495a40ad` and the one-power hypothesis,
give `5c1aba17` through `b5b84276`. The additional qua-exercise
calibration would interpret this giving as actual rational
production under a good. #1944's same-holder/root identification
and `834ddcfa` continue to connect the willed holder to
`66aecdd7`, with their registered premises and sense bridges.
The qualifier does not add a Lean conclusion, identify
`GivesTo` with `CausesIn`, or resolve NAR, WN, actual
accessible omission or policy-level optimality. A genuinely
operative end can supply a candidate nonnecessitating
explanation of an actual existential gift, not a proof of
`608a262d` over its whole domain or of BX1/BX2. No claim of
overall personal superiority follows for thin productive-order
explananda. The candidate personal account has a conditional
advantage for the richer intentional explanandum; warrant for
including that explanandum in the actual case is still needed.

**Reopening conditions, in priority order.**
(1) Find a positive reason why a source whose intrinsic essence is
actual understanding supplies the *formative specification of its
actual productive exercise* through that understanding, rather than
merely owning or cognizing the effective principle. Test the actual
source's self-content, the independent intelligible measure of the
productive end, and the exercise of its own will in the same giving.
A criterion for genuinely exercising a power qua its essential
formative mode can advance the case without a new real-distinction
argument. (2) If the rival gives a unitary, strictly simple
contemplative-propensity account, demand the same constitutive
explanation of its intrinsic roles and actual exercise as of the
personal one; if it instead asserts actual distinct intrinsic
grounds, check the existing composition and identity-dependence
principles at those exact relata. (3) Independently warrant the
actual adoption/communication of the owned good, and then the
recipient-specific willing required for `a94c5dfc`. A normative
permission or a match in outcomes is insufficient.
These conditions exclude another exercise of the same reclassification
or collapse proofs as useful next work.

**Verification/disposition.** This delivery changes the note and a
new scoped attempt, not definitions, proof inputs, source claims or
graph edges. Directly inspected the current `WillVersusChance`
definitions, solution A, the intellect/will definitions and
recipient-good records; read the linked Θ.2/5 and q.25 articles
in their relevant context. Author's semantic sweep: ordinary cases
and rival sketches explicitly not strict-simplicity models; matched
efficacy and stopping standards; no attribution registered; exact
type and witness distinguished from formative interpretation;
no counterfactual intervention on a necessary intrinsic state;
Rational/HAS_WILL_1/recipient-good senses retained. Previous
#1971 head `65b78691b29b68ae25bb6cb6335ed3eb19646b04` CI passed
([run 45509424903](https://github.com/moritzbrantner/formal-logos/actions/runs/45509424903));
automated review found one P1, the overstated defense of invariant
communication, corrected at `83865fdff2b494bea9331aea688a6ddf389f9b30`.
That review does not constitute the independent semantic challenge
of this new assessment or certify this changed head. No local
checkout, Lean/Rust CLI or independent reviewer worker is available
here; final applicable CI, computed premise comparison and
independent semantic review remain outstanding.
