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
