# Will versus chance at a necessary, patientless source (#1926 phase 3)

Outcome label (rigor contract 6): **a new bridge**, conditional. Part A is
**already established** elsewhere and is only connected here; part B adds a
verified, non-transcription support option for STMT-GOD-HAS-WILL (`66aecdd7`)
whose crux is shown to be the chance rival's exact denial, and a second,
intellect-based route that discriminates without restating that denial.

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
| Strict efficacy of one rigid act token | #555 `OutputProfile` | `StrictEfficacy`, DEF `01b44013` | `SimplicityCollapse.rigid_core`; `ModalSenseSupport.RivalNegations` derives `¬ NecessaryActStrictlyYieldsContingent` from it |
| Fixed giving (same beings wherever the giver exists) | #1897 `CausalityFrame` | `FixedGiver`, DEF `7bc1d667` | #1897 laws 3 and 4 |
| Set-up necessitation (same set-up ⇒ same giving) | this batch, agency overlay on the same frame | `SetupNecessitatedAt`, DEF `ca00e246` | controls law 8 |
| Necessitating reason | #755 `Arena` | `PSRStrength.Necessitating`, DEF `3055e6f1` | `PSRStrength.necessitating_reason_contingent` |

**The brief's first test is already answered.** Joint satisfiability of the
route premises with `NecessaryActStrictlyYieldsContingent` fails: that bundle is
refuted by `SimplicityCollapse.Core`, which `rigid_core` proves
(`ModalSenseSupport.RivalNegations`, second clause). The core fact is K-closure
on the access relation: a necessary source, a strict implication from it to the
effect, hence a necessary effect. Nothing new was proved for it.

**What this batch adds (laws 8–10, premise-free).**

- Law 8: with factive giving, a necessary giver whose set-up is invariant and
  whose giving is set-up necessitated gives being at `w` only to necessary
  beings. With an invariant set-up, set-up necessitation coincides with fixed
  giving at accessible worlds.
- Law 9: with excluded middle, VG (variation needs a varying set-up) is exactly
  set-up necessitation of every being at `w`.
- Law 10: #1897's withholding holder, with P5 and an invariant set-up, is a
  two-way giver and is **not** set-up necessitated, whatever its power.

**What it excludes and what it leaves.** Every sense excludes a necessitating
source of contingent effects **whether personal or not**: a necessitated will
is excluded as well (law 2: VG excludes willed and chancy two-way giving
alike). So part A removes the necessitating impersonal source (Spinozist
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
| Willed two-way giving | DEF `de24ce2e` | CHANCE_3's profile with a rational power |

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
willed two-way giving and CHANCE_3 with the same set-up; (6) will as a rational
power and one power exclude CHANCE_3 for a being with will; (7) both are
two-way giving; (8)–(10) part A above; (11) with excluded middle, DNP′ is
exactly the absence of CHANCE_3 at `w`, and DNP_inv exactly its absence at
invariant beings; (12) with excluded middle and giving as exercise, an invariant
two-way giver is willed or CHANCE_3, and not both given one power; (13) the
chance core: one power, CHANCE_3, intellect, will following intellect and will
as a rational power are jointly inconsistent.

**Models.** Theist nonvacuity of A–D (`theistG`, `simpleRational`); the chance
rival (same frame, set-up, giving and one power, power non-rational: DNP′ and
DNP_inv fail; the conclusions of B, C, D fail); the intellectual chancer (two
powers); each member of the chance core needed (five deletion models); omission
models of every premise of A (3), B (6), C (3) and D (7); DNP′ strictly
stronger than DNP_inv (three worlds: a chancy being whose set-up varies at a
third world); VG and chance-sense nonvacuity. `truth countermodel` does not
handle `CausalityFrame` parameters (#1897 gap 9), so all models are hand-written.

## 5. What discriminates will from chance

**Formal finding.** In this overlay nothing but `Rational` separates a willed
two-way giver from a CHANCE_3 giver (law 5), confirming #742 at the will step.
The Θ.5 premise in either strength is, with excluded middle, *exactly* the
denial of CHANCE_3 in its scope (law 11). So argument C/D is a valid support
option whose only discriminating content against the chance rival is DNP_inv
itself: as evidence against that rival it begs the question unless DNP_inv has
warrant of its own. Different presentations of one assumption are not
additional evidence.

**The discriminating route.** At a source with one power, the dichotomy of law
12 is decided by whether that one power is rational, and intellect with the two
will bridges decides it (arguments A, B; law 13). The chance rival is therefore
consistent only if it denies one of: the source's intellect, its one power,
will following intellect (`090be689`), will as a rational power, or giving as
exercise. Its natural choice is to deny intellect at the source. The will-step
question at a simple source **reduces to the intellect question**, which has
its own arguments and its own impersonal rival
(`docs/notes/causal-perfection-transfer.md`, "Emergence and comparison under
the same standard"; `docs/immaterial-intellect-reception.md`, rival 9). This is
horizontal support from another argument family; it shares the dependency on
those intellect routes and the holder-root identification (#1897 gap 2).

**Warrant of DNP′ and DNP_inv** (Substantive Objection Standard applied both
ways).

- *Positive warrant for DNP′.* The Aristotelian-Thomist principle that a
  natural (non-rational) agent acts in one way unless impeded (Θ.5; q.19 a.4
  co., second argument), supported by the success of deterministic laws in
  ordinary experience.
- *Objection to DNP′.* Target: the universal premise DNP′. Mechanism: an
  indeterministic non-rational power (CHANCE_3). Independent justification:
  stochastic dynamics in collapse and Copenhagen-type readings of quantum
  mechanics, which are developed, empirically adequate positions; Pruss's own
  first cause "perhaps non-deterministic". Relevance: one such power falsifies
  DNP′ (law 11). Status: **live, not established**: deterministic readings
  (Bohmian, Everettian) are equally adequate, so the evidence is
  interpretation-dependent.
- *DNP_inv escapes the counterexample.* The specific difference: physical
  propensities belong to beings whose set-up varies across the worlds where
  they exist (they are embedded in changing conditions), so they fall outside
  DNP_inv's scope (the strictness model has this shape). The evidence of
  physics bears on the general principle, not on beings with an invariant
  set-up.
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
  warrant for DNP_inv.
- *No substantive objection* was identified to the inferences of A–E, to
  giving as exercise, or to the two will bridges beyond their being
  primitives. The omission models show only that each premise is needed.

## 6. The strongest standing rival and its price

**Rival.** A necessary, simple (one non-rational power, invariant set-up),
patientless source that gives the actual contingents being by an
indeterministic propensity (CHANCE_3), and could have withheld them. Model:
`Model.ChanceRival`. It accepts every premise of #1897's withholding route.

**Price, derived under the stated premises:**

1. It denies DNP′ and DNP_inv (law 11), i.e. it posits per se chance at a
   necessary, simple being.
2. It denies VG (shared with the theist; law 2).
3. Given one power and the will bridges, it denies intellect at the source (law
   13). If the source gives being to intellectual beings, it must therefore
   deny the perfection-transfer premises for intellect, or mediate the
   intellect of its effects through causes it does not totally supply (the
   emergence reply of `causal-perfection-transfer.md`).
4. It owes a non-cognitive specification of determinate outcome-weights at a
   simple being (the q.19 a.4 determination point; the C4 exemplarity
   question). It is not shown that this is impossible.

None of these is shown to conflict with an accepted floor item; each is a
substantive commitment, not a refutation. Unusualness is not counted as a cost.

## 7. Matched-scope comparison (same explanandum)

Explanandum: a necessary source with an invariant set-up gives the actual
contingent concreta being and withholds them at an accessible world.

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
  excluded, in every fixed sense, together with a necessitated will. High
  confidence in the consequence; it decides nothing between will and an
  impersonal non-necessitating source.
- **Part B, Θ.5 route (C, D):** a valid new support option for `66aecdd7`, but
  **it does not discriminate will from chance** beyond DNP_inv's own warrant,
  which is weakened (its parent principle meets a live objection) and not
  independently supported. The chance rival stands at this step.
- **Part B, intellect route (A, B):** discriminating, conditional on the
  source's intellect and one power. The will-versus-chance question at a simple
  source is the intellect question; the case for will at the source is as
  strong as the case for intellect at the source (the existing intellect routes
  and their impersonal rival), and no stronger.
- **Overall:** the Θ.5 bridge is not a separate warrant for will; will at the
  first source is supported horizontally, through intellect.

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
| `fdd2b1cf` | some holder is a willed two-way giver | `∃ y, PowerFor w y q ∧ WilledTwoWayAt w y` | existence at `w` inside `WilledTwoWayAt`; no contrastive explanation |
| `a9776d21` | invariant two-way givers have will | `∀ y, SetupInvariantAt w y → TwoWayGiverAt w y → HasWill y` | capacity |
| `66aecdd7` (reused) | God has will | `∀ g, IsGod g → HasWill g` | world-free conclusion from premises at one `w` |
| `ff9c8158` | laws and models | `Model.Controls` | surrogates only |

Every hypothesis of each theorem is a listed premise (bind-check). No source is
attributed; no claim record is added.

## 10. Remaining gaps and next tests

1. **Independent warrant for DNP_inv** (the decisive open test for the Θ.5
   route): a reason specific to invariant, patientless beings.
2. **Holder-root identification** (#1897 gap 2), needed to carry the intellect
   routes' HAS_INTELLECT_1 to the holder (premise `813a9181`) and for argument
   B's connection to the root.
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

None to existing records or modules. New: the two Lean modules (Challenge
generated), the spec and its generated records, ten definitions, the CHANCE
disambiguation `c18f084e`, this note and attempt records. A NECESSITATE
disambiguation joining the four senses of §2 was drafted and dropped: adding the
existing definitions `01b44013`, `7bc1d667` and `3055e6f1` as its senses would
have required re-tagging the labels of existing records, and no argument uses
two of the senses.
