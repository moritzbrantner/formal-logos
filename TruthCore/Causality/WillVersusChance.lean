module

public import TruthCore.Modal.PrussPowerPremises
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Logic.ExcludedMiddle

/-!
# Choice versus chance at a necessary, patientless source (stage two, `66aecdd7`)

Analyst formulations, attribution deferred (logic first). Merged #1897
(`TruthCore.Modal.PrussPowerPremises`) showed that, granting P1′ and P2δ on one
of its warrants, the holder of the power for the joint absence of the actual
contingent concreta is a necessary being whose giving of being varies across
worlds where it exists, in the withholding form (`TwoWayGiverAt`). Its planned
step to will (the "Θ.5 bridge") is blocked by the **chance rival**: an
indeterministic non-rational power has the same two-way profile without choice.
This module asks two questions (#1926 phase 3):

1. **A necessitating impersonal source.** Does a necessary root with contingent
   effects exclude a source that necessitates them? The core fact is already
   established elsewhere: #555 `SimplicityCollapse.rigid_core` (the first
   clause of `Core`; `ModalSenseSupport.RivalNegations` refutes
   `NecessaryActStrictlyYieldsContingent`), #1897 laws 3 and 4 and, as a
   fact-level analogue, `PSRStrength.necessitating_reason_contingent`. Here it
   is restated only in the will step's own sense, SET-UP NECESSITATION
   (`SetupNecessitatedAt`), at a source with an invariant set-up (law 8), and
   connected to #1897's withholding holder (laws 8–10; #1897 law 6 lies behind
   law 10). The exclusion does not use impersonality: it excludes a
   set-up-necessitated will equally.
2. **What discriminates choice from chance** at a source with an invariant
   set-up. In this overlay the answer is: only the classification `Rational`
   (law 5, the flip), and the Θ.5 principle restricted to invariant sources
   (DNP_inv) is, with excluded middle, exactly the denial of CHANCE_3 at such
   sources (law 11). A route found here that discriminates without restating
   the rival's denial passes through intellect and one power at the source
   (arguments A and B): at a source with one power, intellect with will
   following intellect and will as a rational power suffices to make the
   giving willed, and the chance rival must deny the source's intellect
   (law 13). The converse is not proved (`Rational` has no content): other
   warrants for will at the source would discriminate equally (law 6).

**What is new.** One overlay of agency primitives on the shared
`CausalityFrame` (`AgencyFrame`): intrinsic states, external conditions of a
giving, powers, a classification of powers as rational, and the exercise of a
power in a giving. With them: three senses of *chance* (incidental coincidence,
variation of the set-up, indeterministic propensity) and a willed two-way
profile, each typed on the same giving relation `GivesTo` (#1897, frame
primitive `GivesAt`); the variation-ground principle (VG); the Θ.5 principle
restricted to non-rational powers in a strong (DNP′) and a weak, invariant-source
(DNP_inv) version.

**Relation to existing work.** #742 (`ExplanatorySymmetry`, note
`explanatory-symmetry-742.md`) found that four structural marks do not
separate personal choice from an indeterministic set-up and that a personal
flag would be circular. `Rational` here is a primitive classification of
powers, not a discharge of that finding: the results below locate *which
premises* mention it, and the flip law shows that nothing else in the overlay
separates a willed from a chancy two-way giver. #1737 (`OptimalCreationChoice`)
found that extensional output tracking is not an intentional explanation; no
tracking relation is used here.

`Rational p` has a stated meaning (an inclination following intellectual
apprehension of the good; Θ.5's "desire or will"), but Lean gives it no content
beyond the premises that mention it. HAS_WILL_1 (`HasWill`, DEF `7c64b499`)
stays the existing primitive predicate; its passage to and from having a
rational power is an explicit bridge premise in each direction.

Every model in the Solution is a finite structural surrogate on #1897's
frames, never a certificate of metaphysical possibility.
See `docs/notes/will-versus-chance.md`.
-/

@[expose] public section

namespace TruthCore.Causality.WillVersusChance

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Modal.PrussPowerPremises (GivesTo GivingSameIn TwoWayGiverAt GivenExists
  ActualAbsenceHoldersGiveEach ActualAbsenceByWithholding FixedGiver)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn SomeContingentConcreteAt
  ActualAbsenceInitiatorPresent)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (WillFollowsIntellectReading)
open TruthCore.Case.Catholicism (GodHasWill)

variable {W B T R S P : Type}

/-! ## The agency overlay -/

/-- Agency primitives over worlds `W`, beings `B`, intrinsic states `S` and
powers `P`. Every field is a primitive; no relation between fields, or between
a field and the `CausalityFrame`, is assumed. Bridges are explicit premises. -/
structure AgencyFrame (W B S P : Type) where
  /-- `StateAt v y s`: in world `v`, `y` has the intrinsic (non-relational)
  state `s`: a quality, a disposition, a propensity value or a mental state.
  Example: a coin's bias; an agent's present intention. Non-example: a relation
  to what `y` gives being (an extrinsic denomination). -/
  StateAt : W → B → S → Prop
  /-- `ConditionOf v y z`: in world `v`, the being `z` is an external condition
  of `y`'s giving: a patient, an occasion, a concurring cause. Example: the
  fuel on which fire acts. Non-example: what `y` gives being (the effect). -/
  ConditionOf : W → B → B → Prop
  /-- `PowerOf y p`: `p` is an active power of `y`, a principle of its
  operation. World-independent. -/
  PowerOf : B → P → Prop
  /-- `Rational p`: `p` is a rational power, an inclination that follows
  intellectual apprehension of the good (Met. Θ.5's "desire or will"; HAS_WILL_1's
  "inclination of an intellectual nature toward the good apprehended"). A
  classification of powers with no further content in Lean. Example: a
  craftsman's will to build. Non-examples: fire's heating; a radioactive
  nucleus's propensity to decay. -/
  Rational : P → Prop
  /-- `Exercises v y x p`: in world `v`, `y`'s giving `x` being is an exercise
  of the power `p`. -/
  Exercises : W → B → B → P → Prop

/-- The same overlay with powers reclassified by `Q`: every other field is
unchanged. Used by the flip law. -/
def AgencyFrame.reclassify (A : AgencyFrame W B S P) (Q : P → Prop) : AgencyFrame W B S P :=
  { A with Rational := Q }

/-! ## Set-up, exercise and one power -/

/-- The SET-UP of `y`'s giving is the same in worlds `u` and `v`: the same
intrinsic states of `y`, and the same external conditions of its giving. -/
def SetupSameIn (A : AgencyFrame W B S P) (y : B) (u v : W) : Prop :=
  (∀ s, A.StateAt u y s ↔ A.StateAt v y s) ∧ (∀ z, A.ConditionOf u y z ↔ A.ConditionOf v y z)

/-- INVARIANT SET-UP at `w`: at every world accessible from `w` where `y`
exists, the set-up of its giving is the same as at `w`. The frame surrogate for
a simple (no varying intrinsic state) and patientless (no varying external
condition) source. Example: an immutable being with no patient. Non-examples: a
die (its initial conditions vary); an agent who changes its mind. -/
def SetupInvariantAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B) :
    Prop :=
  ∀ v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y → SetupSameIn A y w v

/-- `GivesBy F A v y x p`: in world `v`, `y` gives `x` being (`GivesTo`, DEF
`62dfa893`) by exercising its power `p`. -/
def GivesBy (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (v : W) (y x : B) (p : P) :
    Prop :=
  GivesTo F v y x ∧ A.Exercises v y x p

/-- ONE POWER: all powers of `y` are one. The power-level aspect of simplicity
(ST I q.19 a.4 ad 4, read in the materialized witness: knowledge directing, will
commanding and power executing, "Sed haec omnia in Deo unum sunt"; navigation,
no claim). Example: on Aquinas's account, God. Non-example: a human, whose
intellect, will and nutritive powers differ. -/
def OnePower (A : AgencyFrame W B S P) (y : B) : Prop :=
  ∀ p q, A.PowerOf y p → A.PowerOf y q → p = q

/-- SET-UP NECESSITATION of `y`'s giving from `w` (the sense of "necessitate"
fixed for the will step): at every world accessible from `w` where `y` exists
with the same set-up as at `w`, `y` gives being to exactly the same beings as at
`w`. A deterministic (necessitating) power is one whose giving is fixed by its
set-up. Example: fire heating the same fuel under the same conditions.
Non-examples: a CHANCE_3 propensity; a willed two-way giving. With an
invariant set-up it is the accessible-world form of #1897's `FixedGiver`
(DEF `7bc1d667`) and the frame counterpart of #555's strict efficacy of one
rigid act: what the set-up fixes is given wherever the source is (law 14 proves
the coincidence with an invariant set-up; without one, a giver whose set-up
varies is vacuously set-up necessitated and law 8 does not apply). -/
def SetupNecessitatedAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B) :
    Prop :=
  ∀ v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y → SetupSameIn A y w v →
    GivingSameIn F y w v

/-! ## Three senses of chance, and willed two-way giving

All four are refinements of the two-way or varying profile of #1897. -/

/-- CHANCE_1, INCIDENTAL (surrogate for Aristotle's chance, *Physics* II.5–6,
navigation): `y`'s giving differs between `w` and an accessible world where it
exists, and some other being is an external condition of the giving at one of
the two worlds and not at the other. It types only a necessary condition of
incidental causation (a concurring cause that varies); "for the sake of
something" and "not always or for the most part" are not typed. Example: a
debt repaid because the creditor happened to go to the market. -/
def IncidentalVariationAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W)
    (y : B) : Prop :=
  F.history.ontic.ExistsAt w y ∧ ∃ v, F.history.ontic.frame.access w v ∧
    F.history.ontic.ExistsAt v y ∧ ¬ GivingSameIn F y w v ∧
    ∃ z, z ≠ y ∧ ¬ (A.ConditionOf w y z ↔ A.ConditionOf v y z)

/-- CHANCE_2, VARYING SET-UP (deterministic or statistical chance): `y`'s
giving differs between `w` and an accessible world where it exists, and the
set-up differs there too. Example: a coin toss, whose outcome tracks varying
initial conditions. It does not require that the difference in set-up
determines the outcome. -/
def SetupVariationAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B) :
    Prop :=
  F.history.ontic.ExistsAt w y ∧ ∃ v, F.history.ontic.frame.access w v ∧
    F.history.ontic.ExistsAt v y ∧ ¬ GivingSameIn F y w v ∧ ¬ SetupSameIn A y w v

/-- CHANCE_3, INDETERMINISTIC PROPENSITY: `y` exists at `w` and gives some `x`
being at `w` by a non-rational power `p`, and at an accessible world where `y`
exists with the same set-up, `y` does not give `x` being. Example (on
indeterministic readings of quantum mechanics): a nucleus that decays in one
course of events and not in another from the same state. Pruss's "perhaps
non-deterministic" first cause, read impersonally. No probability measure is
typed: only the same-set-up, different-outcome profile of a non-rational
power. -/
def PropensityChanceAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B) :
    Prop :=
  F.history.ontic.ExistsAt w y ∧ ∃ p x v, A.PowerOf y p ∧ ¬ A.Rational p ∧
    F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v y ∧ SetupSameIn A y w v ∧
    GivesBy F A w y x p ∧ ¬ GivesTo F v y x

/-- WILLED TWO-WAY GIVING (choice): as `PropensityChanceAt`, with a rational
power. Example: on Aquinas's account, God giving a creature being by his will,
which "determinat seipsam" to an object to which it has a non-necessary
relation (ST I q.19 a.3 ad 5; navigation). It differs from CHANCE_3 only in
`Rational` (flip law). It does not say that the exercise is explained
contrastively: the luck objection to undetermined choice is not answered by
this definition. -/
def WilledTwoWayAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B) :
    Prop :=
  F.history.ontic.ExistsAt w y ∧ ∃ p x v, A.PowerOf y p ∧ A.Rational p ∧
    F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v y ∧ SetupSameIn A y w v ∧
    GivesBy F A w y x p ∧ ¬ GivesTo F v y x

/-! ## Premises (all OPEN) -/

/-- OPEN (VG, variation needs a varying set-up): if `y` exists at `w` and at an
accessible world `v` and gives being otherwise there, the set-up of its giving
differs between `w` and `v`. The frame analogue of the difference-making demand
in ST I q.19 a.3 obj. 5 ("ab eo quod est ad utrumlibet, non sequitur aliqua
actio, nisi ab aliquo alio inclinetur ad unum"); the objection names an
external determiner, VG also accepts an intrinsic difference. Not attributed.
It applies to every power alike, rational or not: with excluded middle it says
that every being at `w` is set-up necessitated (law 9). -/
def VariationNeedsVaryingSetup (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) :
    Prop :=
  ∀ y v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt w y →
    F.history.ontic.ExistsAt v y → ¬ GivingSameIn F y w v → ¬ SetupSameIn A y w v

/-- OPEN (DNP′, Θ.5 restricted to non-rational powers, contrapositive form;
STRONG version): if `y` exists at `w` and gives `x` being there by its power
`p`, and at an accessible world where `y` exists with the same set-up it does
not give `x` being, then `p` is rational. Met. Θ.5 (1048a, Ross, navigation):
for non-rational potencies, "when the agent and the patient meet ... the one
must act", for rational ones "something else ... decides; I mean by this,
desire or will"; ST I q.19 a.4 co. (read in the materialized witness,
navigation): "natura uno et eodem modo operatur, nisi impediatur". With
excluded middle, exactly the denial of CHANCE_3 at `w` (law 11). Its universal
scope meets the indeterministic-propensity objection (note §5). -/
def SameSetupVariationIsRational (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) :
    Prop :=
  ∀ y p x v, F.history.ontic.ExistsAt w y → F.history.ontic.frame.access w v →
    F.history.ontic.ExistsAt v y → A.PowerOf y p → SetupSameIn A y w v →
    GivesBy F A w y x p → ¬ GivesTo F v y x → A.Rational p

/-- OPEN (DNP_inv, the WEAK version of DNP′): as DNP′, only for beings whose
set-up is invariant at `w` (simple, patientless sources). The weakest version
that the Θ.5 route uses. With excluded middle, exactly the denial of CHANCE_3 at
beings with an invariant set-up (law 11). The physical propensities that tell
against DNP′ are not counterexamples to it *on the assumption* that every
physical propensity bearer has a set-up that differs at some accessible world
where it exists (under broad metaphysical access); they do undercut the
inductive warrant it inherited from DNP′ (note §5). -/
def InvariantSetupVariationIsRational (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (w : W) : Prop :=
  ∀ y p x v, SetupInvariantAt F A w y → F.history.ontic.ExistsAt w y →
    F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y → A.PowerOf y p →
    GivesBy F A w y x p → ¬ GivesTo F v y x → A.Rational p

/-- OPEN (giving is an operation of the giver): whenever `y` gives `x` being in a
world, that giving is the exercise of some power of `y`. -/
def GivingExercisesOwnPower (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) : Prop :=
  ∀ v y x, GivesTo F v y x → ∃ p, A.PowerOf y p ∧ A.Exercises v y x p

/-- OPEN bridge (HAS_WILL_1 to a rational power): whatever has will has some
rational power. HAS_WILL_1 is "the inclination of an intellectual nature toward
the good apprehended" (DEF `7c64b499`); this reads having that inclination as
having a power of the rational class. -/
def WillIsRationalPower (A : AgencyFrame W B S P) (HasWill : B → Prop) : Prop :=
  ∀ y, HasWill y → ∃ p, A.PowerOf y p ∧ A.Rational p

/-- OPEN bridge (a rational power to HAS_WILL_1): whatever has a rational power
has will. The converse direction of `WillIsRationalPower`; near-definitional
under DEF `7c64b499`, as `b7b10ad2` is for inclination following an
intelligible form. -/
def RationalPowerIsWill (A : AgencyFrame W B S P) (HasWill : B → Prop) : Prop :=
  ∀ y p, A.PowerOf y p → A.Rational p → HasWill y

/-- OPEN (the holder's set-up is invariant): whatever has at `w` a power for the
joint absence of the concrete beings contingent at `w` has an invariant set-up
at `w`: no intrinsic state or external condition of its giving differs at an
accessible world where it exists. The simplicity-and-patientlessness reading of
#1897's holder; not derived from its necessity. -/
def ActualAbsenceHoldersSetupInvariant (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) → SetupInvariantAt F A w y

/-- OPEN (the holder has intellect): whatever has at `w` a power for the joint
absence of the concrete beings contingent at `w` has intellect (HAS_INTELLECT_1).
The connection to the existing intellect routes, which conclude HAS_INTELLECT_1
of GOD_4 or of the perfect root, needs the identification of the holder with
that root (#1897 note, gap 2). -/
def ActualAbsenceHoldersHaveIntellect (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (HasIntellect : B → Prop)
    (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) → HasIntellect y

/-- OPEN (the holder has one power): whatever has at `w` a power for the joint
absence of the concrete beings contingent at `w` has one power (`OnePower`), the
power-level aspect of simplicity. Not derived from the invariant set-up: an
invariant being may have two powers (the intellectual-chancer model). -/
def ActualAbsenceHoldersOnePower (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∀ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) → OnePower A y

/-- OPEN bridge (GOD_4 holds the power): every GOD_4 exists at `w` and has at `w`
a power for the joint absence of the concrete beings contingent at `w`. The
directional identification needed to bring #1897's holder premises to GOD_4:
not uniqueness, not that every holder is GOD_4. On classical theism God could
have refrained from creating (ST I q.19 a.3; navigation). -/
def GodsHoldActualAbsencePower (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod : B → Prop) (w : W) :
    Prop :=
  ∀ g, IsGod g → F.history.ontic.ExistsAt w g ∧
    PowerFor w g (NoActualContingentConcreteIn F concrete w)

/-! ## Conclusions -/

/-- No being with an invariant set-up at `w` is a two-way giver at `w`. Covers
willed and chancy two-way giving alike. -/
def NoTwoWayGiverWithInvariantSetup (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (w : W) : Prop :=
  ∀ y, SetupInvariantAt F A w y → ¬ TwoWayGiverAt F w y

/-- Every giving, in any world, by an intellectual being all of whose powers are
one is the exercise of a rational power of it. -/
def OnePowerIntellectualGivingWilled (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (HasIntellect : B → Prop) : Prop :=
  ∀ y, HasIntellect y → OnePower A y → ∀ v x, GivesTo F v y x →
    ∃ p, A.PowerOf y p ∧ A.Rational p ∧ A.Exercises v y x p

/-- Every two-way giver at `w` with an invariant set-up there has will
(HAS_WILL_1, the capacity). -/
def InvariantSetupTwoWayGiversWill (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (HasWill : B → Prop) (w : W) : Prop :=
  ∀ y, SetupInvariantAt F A w y → TwoWayGiverAt F w y → HasWill y

/-- Some holder at `w` of a power for the joint absence of the concrete beings
contingent at `w` is, at `w`, a willed two-way giver (`WilledTwoWayAt`): it gives
some being by a rational power and withholds it at an accessible world with the
same set-up. Not CHANCE_3, given one power (law 12). -/
def ActualAbsenceHolderGivesByWill (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W) : Prop :=
  ∃ y, PowerFor w y (NoActualContingentConcreteIn F concrete w) ∧ WilledTwoWayAt F A w y

/-! ## Laws and models -/

namespace Model

open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 Bg.forall_iff Bg.exists_iff V3.forall_iff
  V3.exists_iff theistG inertG nonFactiveG
  necessitarianG gFrame allC onlyCD uni gcEx gcAlways givesCHere givesCAlways noGiving gPower noPower)

/-- General laws.

1. **Simple, patientless sources exclude two senses of chance.** With an
   invariant set-up at `w`, `y` has neither incidental (CHANCE_1) nor
   set-up (CHANCE_2) variation at `w`.
2. **VG is symmetric.** With VG and an invariant set-up at `w`, `y` is not a
   two-way giver, neither a chancy (CHANCE_3) nor a willed one.
3. **VG strengthens DNP′.** VG at `w` gives DNP′ at `w`.
4. **DNP′ excludes propensity chance.** DNP′ at `w` gives that no being has
   CHANCE_3 at `w`.
5. **The flip.** Reclassifying every power as non-rational turns a willed
   two-way giver into a CHANCE_3 giver, and reclassifying every power as
   rational does the converse; the set-up relation is unchanged by
   reclassification.
6. **One power and will exclude chance.** If whatever has will has a rational
   power (only this direction of the will bridges is used), a being with will
   and one power has no CHANCE_3 at any world, whatever the warrant for its
   will.
7. Willed two-way giving and CHANCE_3 are both two-way giving (#1897).
8. **Set-up collapse (part A).** With factive giving, a being necessary at `w`
   whose set-up is invariant and whose giving is set-up necessitated gives
   being at `w` only to beings necessary at `w`. The will step's counterpart of
   #555 `rigid_core` and #1897 law 3.
9. **VG is set-up necessitation everywhere.** With excluded middle, VG at `w`
   holds exactly when every being at `w` is set-up necessitated from `w`.
10. **The withholding holder is not set-up necessitated (part A).** The joint
    absence realized by withholding, P5 and the holder's invariant set-up give
    a holder at `w` that is a two-way giver and is not set-up necessitated,
    whatever its power.
11. **DNP is the denial of CHANCE_3.** With excluded middle, DNP′ at `w` holds
    exactly when no being has CHANCE_3 at `w`, and DNP_inv exactly when no being
    with an invariant set-up has it.
12. **The dichotomy at a simple source.** With excluded middle and giving as
    exercise, an invariant two-way giver is a willed two-way giver or a CHANCE_3
    giver; with one power, not both.
13. **The chance core.** One power, CHANCE_3, intellect, will following
    intellect and will as a rational power are jointly inconsistent. So a
    one-power chancy source lacks intellect, given will following intellect
    and will as a rational power.
14. **Set-up necessitation and fixed giving.** At a being with an invariant
    set-up, set-up necessitation from `w` is exactly giving the same beings at
    every accessible world where it exists; and a fixed giver (#1897
    `FixedGiver`) existing at `w` is set-up necessitated from `w`. -/
def Laws : Prop :=
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    SetupInvariantAt F A w y → ¬ IncidentalVariationAt F A w y ∧ ¬ SetupVariationAt F A w y) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W),
    VariationNeedsVaryingSetup F A w → NoTwoWayGiverWithInvariantSetup F A w ∧
      ∀ y, SetupInvariantAt F A w y → ¬ PropensityChanceAt F A w y ∧ ¬ WilledTwoWayAt F A w y) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W),
    VariationNeedsVaryingSetup F A w → SameSetupVariationIsRational F A w) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W),
    SameSetupVariationIsRational F A w → ∀ y, ¬ PropensityChanceAt F A w y) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    (WilledTwoWayAt F A w y → PropensityChanceAt F (A.reclassify fun _ => False) w y) ∧
    (PropensityChanceAt F A w y → WilledTwoWayAt F (A.reclassify fun _ => True) w y) ∧
    (∀ Q u v, SetupSameIn (A.reclassify Q) y u v ↔ SetupSameIn A y u v)) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
      (HasWill : B → Prop) (w : W) (y : B),
    WillIsRationalPower A HasWill → HasWill y → OnePower A y → ¬ PropensityChanceAt F A w y) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    (WilledTwoWayAt F A w y → TwoWayGiverAt F w y) ∧
    (PropensityChanceAt F A w y → TwoWayGiverAt F w y)) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    GivenExists F → NecessaryAt F.history.ontic w y → SetupInvariantAt F A w y →
    SetupNecessitatedAt F A w y → ∀ x, GivesTo F w y x → NecessaryAt F.history.ontic w x) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W),
    TruthCore.Logic.ExcludedMiddle →
    (VariationNeedsVaryingSetup F A w ↔
      ∀ y, F.history.ontic.ExistsAt w y → SetupNecessitatedAt F A w y)) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
      (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W),
    ActualAbsenceByWithholding F PowerFor concrete w → SomeContingentConcreteAt F concrete w →
    ActualAbsenceHoldersSetupInvariant F A PowerFor concrete w →
    ∃ y, F.history.ontic.ExistsAt w y ∧ PowerFor w y (NoActualContingentConcreteIn F concrete w) ∧
      TwoWayGiverAt F w y ∧ ¬ SetupNecessitatedAt F A w y) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W),
    TruthCore.Logic.ExcludedMiddle →
    (SameSetupVariationIsRational F A w ↔ ∀ y, ¬ PropensityChanceAt F A w y) ∧
    (InvariantSetupVariationIsRational F A w ↔
      ∀ y, SetupInvariantAt F A w y → ¬ PropensityChanceAt F A w y)) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    (TruthCore.Logic.ExcludedMiddle → GivingExercisesOwnPower F A → SetupInvariantAt F A w y →
      TwoWayGiverAt F w y → WilledTwoWayAt F A w y ∨ PropensityChanceAt F A w y) ∧
    (OnePower A y → ¬ (WilledTwoWayAt F A w y ∧ PropensityChanceAt F A w y))) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
      (HasIntellect HasWill : B → Prop) (w : W) (y : B),
    OnePower A y → PropensityChanceAt F A w y → HasIntellect y →
    WillFollowsIntellectReading HasIntellect HasWill → WillIsRationalPower A HasWill → False) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    (SetupInvariantAt F A w y → (SetupNecessitatedAt F A w y ↔
      ∀ v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y →
        GivingSameIn F y w v)) ∧
    (FixedGiver F y → F.history.ontic.ExistsAt w y → SetupNecessitatedAt F A w y))

/-! ### Overlays on #1897's two-world frames (`Bg`: `g`, `c`, `d`) -/

/-- `g` alone has a state (one constant state), no external conditions, one
power, rational, exercised in all of `g`'s giving. The simple, rational source. -/
def simpleRational : AgencyFrame Bool Bg Unit Unit where
  StateAt := fun _ y _ => y = .g
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y = .g
  Rational := fun _ => True
  Exercises := fun _ y _ _ => y = .g

/-- As `simpleRational`, with the one power non-rational: the simple chancy
source. -/
def simpleChancy : AgencyFrame Bool Bg Unit Unit :=
  simpleRational.reclassify fun _ => False

/-- `g` has two powers: `true` rational, `false` non-rational; its giving
exercises the non-rational one. The intellectual chancer. -/
def twoPowerChancer : AgencyFrame Bool Bg Unit Bool where
  StateAt := fun _ y _ => y = .g
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y = .g
  Rational := fun p => p = true
  Exercises := fun _ y _ p => y = .g ∧ p = false

/-- `g` has one rational power, which no giving exercises. -/
def idleRational : AgencyFrame Bool Bg Unit Unit where
  StateAt := fun _ y _ => y = .g
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y = .g
  Rational := fun _ => True
  Exercises := fun _ _ _ _ => False

/-- No powers and no exercise. -/
def powerless : AgencyFrame Bool Bg Unit Unit where
  StateAt := fun _ y _ => y = .g
  ConditionOf := fun _ _ _ => False
  PowerOf := fun _ _ => False
  Rational := fun _ => True
  Exercises := fun _ _ _ _ => False

/-- `g`'s intrinsic state is the world's label: it varies. One non-rational
power, exercised in all of `g`'s giving. -/
def varyingState : AgencyFrame Bool Bg Bool Unit where
  StateAt := fun v y s => y = .g ∧ s = v
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y = .g
  Rational := fun _ => False
  Exercises := fun _ y _ _ => y = .g

/-- As `varyingState`, with the one power rational: an intellectual source that
changes its intrinsic state between worlds. -/
def varyingRational : AgencyFrame Bool Bg Bool Unit :=
  varyingState.reclassify fun _ => True

/-- `d` is an external condition of `g`'s giving at `false` only; one
non-rational power. -/
def concurrence : AgencyFrame Bool Bg Unit Unit where
  StateAt := fun _ y _ => y = .g
  ConditionOf := fun v y z => y = .g ∧ z = .d ∧ v = false
  PowerOf := fun y _ => y = .g
  Rational := fun _ => False
  Exercises := fun _ y _ _ => y = .g

/-- Only `g`. -/
def onlyG (x : Bg) : Prop := x = .g

/-- Nothing. -/
def nobody (_ : Bg) : Prop := False

/-- `g` and `c` only at `false`; nothing at `true`: the holder `g` is absent from
the world lacking `c`. -/
def gcHereOnlyEx (v : Bool) (x : Bg) : Prop := (x = .g ∨ x = .c) ∧ v = false

/-- The theist giving with the holder present only at the actual world: P2′
fails for `g`. -/
def holderHereOnlyG : CausalityFrame Bool Bg Unit Bool := gFrame uni gcHereOnlyEx givesCHere

/-- The flag of the third world of the strictness model. -/
def zFlag : V3 → Bool
  | .z => true
  | _ => false

/-- Three worlds `a`, `b`, `z`, universal access: `g` everywhere, `c` at `a`
only; `g` gives `c` being at `a` only. -/
def threeWorldG : CausalityFrame V3 Bg Unit Bool :=
  gFrame (fun _ _ => True) (fun v x => x = .g ∨ (x = .c ∧ v = .a))
    (fun v y x => y = .g ∧ x = .c ∧ v = .a)

/-- On `threeWorldG`: `g`'s intrinsic state is the same at `a` and `b` and
different at `z`; one non-rational power, exercised in all of `g`'s giving. So
`g` has the same set-up at `a` and `b` (CHANCE_3 between them) but no invariant
set-up at `a`. -/
def threeWorldChancy : AgencyFrame V3 Bg Bool Unit where
  StateAt := fun v y s => y = .g ∧ s = zFlag v
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y = .g
  Rational := fun _ => False
  Exercises := fun _ y _ _ => y = .g

/-- **Theist nonvacuity** (`theistG`, `simpleRational`, actual world `false`;
`g` is GOD_4 and has intellect and will): every premise of arguments A–D and
every conclusion hold; `g` has an invariant set-up, one power and a willed
two-way profile, and is not set-up necessitated; VG fails. A structural
surrogate of creation by will: it has only the frame's beings, giving and the
overlay's primitives, none of the further content of classical theism. -/
def TheistNonvacuity : Prop :=
  WillFollowsIntellectReading onlyG onlyG ∧
  WillIsRationalPower simpleRational onlyG ∧
  GivingExercisesOwnPower theistG simpleRational ∧
  OnePowerIntellectualGivingWilled theistG simpleRational onlyG ∧
  ActualAbsenceByWithholding theistG gPower allC false ∧
  SomeContingentConcreteAt theistG allC false ∧
  ActualAbsenceHoldersSetupInvariant theistG simpleRational gPower allC false ∧
  ActualAbsenceHoldersHaveIntellect theistG gPower allC onlyG false ∧
  ActualAbsenceHoldersOnePower theistG simpleRational gPower allC false ∧
  ActualAbsenceHolderGivesByWill theistG simpleRational gPower allC false ∧
  SameSetupVariationIsRational theistG simpleRational false ∧
  InvariantSetupVariationIsRational theistG simpleRational false ∧
  RationalPowerIsWill simpleRational onlyG ∧
  InvariantSetupTwoWayGiversWill theistG simpleRational onlyG false ∧
  GodsHoldActualAbsencePower theistG gPower allC onlyG false ∧
  ActualAbsenceInitiatorPresent theistG gPower allC false ∧
  ActualAbsenceHoldersGiveEach theistG gPower allC false ∧
  GivenExists theistG ∧
  GodHasWill onlyG onlyG ∧
  SetupInvariantAt theistG simpleRational false .g ∧ OnePower simpleRational .g ∧
  WilledTwoWayAt theistG simpleRational false .g ∧
  ¬ PropensityChanceAt theistG simpleRational false .g ∧
  ¬ SetupNecessitatedAt theistG simpleRational false .g ∧
  ¬ VariationNeedsVaryingSetup theistG simpleRational false

/-- **The chance rival** (`theistG`, `simpleChancy`; nothing has intellect or
will; `g` is GOD_4 in the slot of the bridge): the same frame, set-up and giving
as the theist model, with the one power non-rational. Giving exercises a power,
the will bridges hold vacuously, the holder's set-up is invariant, it has one
power, and the joint absence is realized by withholding; DNP′ and DNP_inv fail,
`g` has CHANCE_3, and the conclusions of arguments B, C and D fail. VG fails
here too. A structural surrogate of a necessary non-rational source with an
indeterministic propensity (Pruss's "non-deterministically produces", read
impersonally); no probability or propensity value is represented. -/
def ChanceRival : Prop :=
  GivingExercisesOwnPower theistG simpleChancy ∧
  RationalPowerIsWill simpleChancy nobody ∧
  WillIsRationalPower simpleChancy nobody ∧
  WillFollowsIntellectReading nobody nobody ∧
  ActualAbsenceByWithholding theistG gPower allC false ∧
  SomeContingentConcreteAt theistG allC false ∧
  ActualAbsenceHoldersSetupInvariant theistG simpleChancy gPower allC false ∧
  ActualAbsenceHoldersOnePower theistG simpleChancy gPower allC false ∧
  GodsHoldActualAbsencePower theistG gPower allC onlyG false ∧
  ¬ SameSetupVariationIsRational theistG simpleChancy false ∧
  ¬ InvariantSetupVariationIsRational theistG simpleChancy false ∧
  PropensityChanceAt theistG simpleChancy false .g ∧
  ¬ ActualAbsenceHolderGivesByWill theistG simpleChancy gPower allC false ∧
  ¬ InvariantSetupTwoWayGiversWill theistG simpleChancy nobody false ∧
  ¬ GodHasWill onlyG nobody ∧
  ¬ VariationNeedsVaryingSetup theistG simpleChancy false

/-- **The intellectual chancer** (`theistG`, `twoPowerChancer`; `g` has
intellect and will): will follows intellect, will is a rational power, giving
exercises a power, and a rational power is will; `g` has will and, with two
powers, gives being by the non-rational one (CHANCE_3). One power fails, the
conclusion of argument A with the one-power condition dropped fails, and DNP′
fails, while the conclusion of argument C holds (`g` has will). So HAS_WILL_1
at the capacity level does not exclude chancy giving; one power does (law 6).
A structural surrogate of a necessary being with two powers (compare Pruss's
"non-unitary cause"). -/
def IntellectualChancer : Prop :=
  WillFollowsIntellectReading onlyG onlyG ∧
  WillIsRationalPower twoPowerChancer onlyG ∧
  GivingExercisesOwnPower theistG twoPowerChancer ∧
  RationalPowerIsWill twoPowerChancer onlyG ∧
  ¬ OnePower twoPowerChancer .g ∧
  ¬ (∀ v x, GivesTo theistG v .g x →
      ∃ p, twoPowerChancer.PowerOf .g p ∧ twoPowerChancer.Rational p ∧
        twoPowerChancer.Exercises v .g x p) ∧
  PropensityChanceAt theistG twoPowerChancer false .g ∧ onlyG .g ∧
  ¬ SameSetupVariationIsRational theistG twoPowerChancer false ∧
  InvariantSetupTwoWayGiversWill theistG twoPowerChancer onlyG false

/-- **The chance core, each member needed** (law 13; all on `theistG`, at
`false`, for `g`). Deleting each member in turn, the other four hold:

1. one power: `twoPowerChancer`, intellect and will for `g`;
2. CHANCE_3: `simpleRational`, intellect and will for `g` (the theist);
3. intellect: `simpleChancy`, intellect and will for nobody (the impersonal
   chancy source);
4. will following intellect: `simpleChancy`, intellect for `g`, will for nobody;
5. will as a rational power: `simpleChancy`, intellect and will for `g`. -/
def ChanceCoreDeletions : Prop :=
  (¬ OnePower twoPowerChancer .g ∧ PropensityChanceAt theistG twoPowerChancer false .g ∧
    onlyG .g ∧ WillFollowsIntellectReading onlyG onlyG ∧ WillIsRationalPower twoPowerChancer onlyG) ∧
  (OnePower simpleRational .g ∧ ¬ PropensityChanceAt theistG simpleRational false .g ∧
    onlyG .g ∧ WillFollowsIntellectReading onlyG onlyG ∧ WillIsRationalPower simpleRational onlyG) ∧
  (OnePower simpleChancy .g ∧ PropensityChanceAt theistG simpleChancy false .g ∧
    ¬ nobody .g ∧ WillFollowsIntellectReading nobody nobody ∧ WillIsRationalPower simpleChancy nobody) ∧
  (OnePower simpleChancy .g ∧ PropensityChanceAt theistG simpleChancy false .g ∧
    onlyG .g ∧ ¬ WillFollowsIntellectReading onlyG nobody ∧ WillIsRationalPower simpleChancy nobody) ∧
  (OnePower simpleChancy .g ∧ PropensityChanceAt theistG simpleChancy false .g ∧
    onlyG .g ∧ WillFollowsIntellectReading onlyG onlyG ∧ ¬ WillIsRationalPower simpleChancy onlyG)

/-- **Omission models of argument A** (intellect and one power make every
giving willed; `theistG`, intellect for `g`):

1. without will following intellect (`simpleChancy`, will for nobody);
2. without will as a rational power (`simpleChancy`, will for `g`): HasWill and
   `Rational` are independent primitives;
3. without giving as exercise (`idleRational`, will for `g`): `g` gives `c`
   being and exercises no power. Encoding artifact: `Exercises` emptied. -/
def OmissionsIntellectRoute : Prop :=
  (GivingExercisesOwnPower theistG simpleChancy ∧ WillIsRationalPower simpleChancy nobody ∧
    ¬ WillFollowsIntellectReading onlyG nobody ∧
    ¬ OnePowerIntellectualGivingWilled theistG simpleChancy onlyG) ∧
  (WillFollowsIntellectReading onlyG onlyG ∧ GivingExercisesOwnPower theistG simpleChancy ∧
    ¬ WillIsRationalPower simpleChancy onlyG ∧
    ¬ OnePowerIntellectualGivingWilled theistG simpleChancy onlyG) ∧
  (WillFollowsIntellectReading onlyG onlyG ∧ WillIsRationalPower idleRational onlyG ∧
    ¬ GivingExercisesOwnPower theistG idleRational ∧
    ¬ OnePowerIntellectualGivingWilled theistG idleRational onlyG)

/-- **Omission models of argument B** (the withholding holder gives by will;
actual world `false`):

1. without the holder's intellect: the chance rival (`theistG`, `simpleChancy`,
   intellect for nobody);
2. without the holder's one power: `theistG`, `twoPowerChancer`, intellect for
   `g` (argument A's conclusion holds vacuously);
3. without argument A's conclusion: `theistG`, `simpleChancy`, intellect for `g`;
4. without the holder's invariant set-up: `theistG`, `varyingRational`,
   intellect for `g`;
5. without withholding: `inertG`, `simpleRational`, intellect for `g`;
6. without P5: `inertG`, `simpleRational`, nothing concrete (withholding holds
   vacuously; the holder premises and argument A's conclusion hold). -/
def OmissionsHolderWill : Prop :=
  (ActualAbsenceByWithholding theistG gPower allC false ∧ SomeContingentConcreteAt theistG allC false ∧
    ActualAbsenceHoldersSetupInvariant theistG simpleChancy gPower allC false ∧
    ActualAbsenceHoldersOnePower theistG simpleChancy gPower allC false ∧
    OnePowerIntellectualGivingWilled theistG simpleChancy nobody ∧
    ¬ ActualAbsenceHoldersHaveIntellect theistG gPower allC nobody false ∧
    ¬ ActualAbsenceHolderGivesByWill theistG simpleChancy gPower allC false) ∧
  (ActualAbsenceHoldersSetupInvariant theistG twoPowerChancer gPower allC false ∧
    ActualAbsenceHoldersHaveIntellect theistG gPower allC onlyG false ∧
    OnePowerIntellectualGivingWilled theistG twoPowerChancer onlyG ∧
    ¬ ActualAbsenceHoldersOnePower theistG twoPowerChancer gPower allC false ∧
    ¬ ActualAbsenceHolderGivesByWill theistG twoPowerChancer gPower allC false) ∧
  (ActualAbsenceHoldersHaveIntellect theistG gPower allC onlyG false ∧
    ¬ OnePowerIntellectualGivingWilled theistG simpleChancy onlyG ∧
    ¬ ActualAbsenceHolderGivesByWill theistG simpleChancy gPower allC false) ∧
  (ActualAbsenceHoldersOnePower theistG varyingRational gPower allC false ∧
    OnePowerIntellectualGivingWilled theistG varyingRational onlyG ∧
    ¬ ActualAbsenceHoldersSetupInvariant theistG varyingRational gPower allC false ∧
    ¬ ActualAbsenceHolderGivesByWill theistG varyingRational gPower allC false) ∧
  (SomeContingentConcreteAt inertG allC false ∧
    ActualAbsenceHoldersSetupInvariant inertG simpleRational gPower allC false ∧
    ActualAbsenceHoldersHaveIntellect inertG gPower allC onlyG false ∧
    ActualAbsenceHoldersOnePower inertG simpleRational gPower allC false ∧
    OnePowerIntellectualGivingWilled inertG simpleRational onlyG ∧
    ¬ ActualAbsenceByWithholding inertG gPower allC false ∧
    ¬ ActualAbsenceHolderGivesByWill inertG simpleRational gPower allC false) ∧
  (ActualAbsenceByWithholding inertG gPower nobody false ∧
    ActualAbsenceHoldersSetupInvariant inertG simpleRational gPower nobody false ∧
    ActualAbsenceHoldersHaveIntellect inertG gPower nobody onlyG false ∧
    ActualAbsenceHoldersOnePower inertG simpleRational gPower nobody false ∧
    OnePowerIntellectualGivingWilled inertG simpleRational onlyG ∧
    ¬ SomeContingentConcreteAt inertG nobody false ∧
    ¬ ActualAbsenceHolderGivesByWill inertG simpleRational gPower nobody false)

/-- **Omission models of argument C** (the restricted Θ.5 bridge; `theistG`,
actual world `false`):

1. without DNP_inv: the chance rival (`simpleChancy`, will for nobody);
2. without giving as exercise (`powerless`, will for nobody): DNP_inv and the
   rational-power bridge hold vacuously; `g` is an invariant two-way giver
   without will;
3. without the rational-power bridge (`simpleRational`, will for nobody). -/
def OmissionsThetaFive : Prop :=
  (GivingExercisesOwnPower theistG simpleChancy ∧ RationalPowerIsWill simpleChancy nobody ∧
    ¬ InvariantSetupVariationIsRational theistG simpleChancy false ∧
    ¬ InvariantSetupTwoWayGiversWill theistG simpleChancy nobody false) ∧
  (InvariantSetupVariationIsRational theistG powerless false ∧ RationalPowerIsWill powerless nobody ∧
    ¬ GivingExercisesOwnPower theistG powerless ∧
    ¬ InvariantSetupTwoWayGiversWill theistG powerless nobody false) ∧
  (InvariantSetupVariationIsRational theistG simpleRational false ∧
    GivingExercisesOwnPower theistG simpleRational ∧ ¬ RationalPowerIsWill simpleRational nobody ∧
    ¬ InvariantSetupTwoWayGiversWill theistG simpleRational nobody false)

/-- **Omission models of argument D** (GOD_4 has will by the restricted Θ.5
bridge; `g` is GOD_4, will for nobody, actual world `false`):

1. without the GOD_4 bridge: `inertG`, `simpleRational`, no powers;
2. without P2′: `holderHereOnlyG` (the holder is absent from the world lacking
   `c`), only `c` concrete;
3. without the creator reading: `inertG`, `simpleRational`;
4. without factive giving: `nonFactiveG`, `simpleRational`;
5. without P5: `inertG`, `simpleRational`, nothing concrete;
6. without the holder's invariant set-up: `theistG`, `varyingState`;
7. without argument C's conclusion: `theistG`, `simpleRational`. -/
def OmissionsGodWill : Prop :=
  (ActualAbsenceInitiatorPresent inertG noPower allC false ∧
    ActualAbsenceHoldersGiveEach inertG noPower allC false ∧ GivenExists inertG ∧
    SomeContingentConcreteAt inertG allC false ∧
    ActualAbsenceHoldersSetupInvariant inertG simpleRational noPower allC false ∧
    InvariantSetupTwoWayGiversWill inertG simpleRational nobody false ∧
    ¬ GodsHoldActualAbsencePower inertG noPower allC onlyG false ∧ ¬ GodHasWill onlyG nobody) ∧
  (GodsHoldActualAbsencePower holderHereOnlyG gPower onlyCD onlyG false ∧
    ActualAbsenceHoldersGiveEach holderHereOnlyG gPower onlyCD false ∧
    GivenExists holderHereOnlyG ∧ SomeContingentConcreteAt holderHereOnlyG onlyCD false ∧
    ActualAbsenceHoldersSetupInvariant holderHereOnlyG simpleRational gPower onlyCD false ∧
    InvariantSetupTwoWayGiversWill holderHereOnlyG simpleRational nobody false ∧
    ¬ ActualAbsenceInitiatorPresent holderHereOnlyG gPower onlyCD false) ∧
  (GodsHoldActualAbsencePower inertG gPower allC onlyG false ∧
    ActualAbsenceInitiatorPresent inertG gPower allC false ∧ GivenExists inertG ∧
    SomeContingentConcreteAt inertG allC false ∧
    ActualAbsenceHoldersSetupInvariant inertG simpleRational gPower allC false ∧
    InvariantSetupTwoWayGiversWill inertG simpleRational nobody false ∧
    ¬ ActualAbsenceHoldersGiveEach inertG gPower allC false) ∧
  (GodsHoldActualAbsencePower nonFactiveG gPower allC onlyG false ∧
    ActualAbsenceInitiatorPresent nonFactiveG gPower allC false ∧
    ActualAbsenceHoldersGiveEach nonFactiveG gPower allC false ∧
    SomeContingentConcreteAt nonFactiveG allC false ∧
    ActualAbsenceHoldersSetupInvariant nonFactiveG simpleRational gPower allC false ∧
    InvariantSetupTwoWayGiversWill nonFactiveG simpleRational nobody false ∧
    ¬ GivenExists nonFactiveG) ∧
  (GodsHoldActualAbsencePower inertG gPower nobody onlyG false ∧
    ActualAbsenceInitiatorPresent inertG gPower nobody false ∧
    ActualAbsenceHoldersGiveEach inertG gPower nobody false ∧ GivenExists inertG ∧
    ActualAbsenceHoldersSetupInvariant inertG simpleRational gPower nobody false ∧
    InvariantSetupTwoWayGiversWill inertG simpleRational nobody false ∧
    ¬ SomeContingentConcreteAt inertG nobody false) ∧
  (GodsHoldActualAbsencePower theistG gPower allC onlyG false ∧
    ActualAbsenceInitiatorPresent theistG gPower allC false ∧
    ActualAbsenceHoldersGiveEach theistG gPower allC false ∧ GivenExists theistG ∧
    SomeContingentConcreteAt theistG allC false ∧
    InvariantSetupTwoWayGiversWill theistG varyingState nobody false ∧
    ¬ ActualAbsenceHoldersSetupInvariant theistG varyingState gPower allC false) ∧
  (ActualAbsenceHoldersSetupInvariant theistG simpleRational gPower allC false ∧
    ¬ InvariantSetupTwoWayGiversWill theistG simpleRational nobody false)

/-- **DNP′ strictly strengthens DNP_inv** (`threeWorldG`, `threeWorldChancy`,
actual world `a`): `g` has the same set-up at `a` and `b`, gives `c` being at
`a` and not at `b` by a non-rational power, so DNP′ fails (CHANCE_3 at `a`);
`g`'s state differs at `z`, so its set-up is not invariant, and DNP_inv holds
(no being with an invariant set-up gives anything). A chancy being whose set-up
varies elsewhere: the shape of the physical propensities of note §5. -/
def DNPStrictness : Prop :=
  InvariantSetupVariationIsRational threeWorldG threeWorldChancy .a ∧
  ¬ SameSetupVariationIsRational threeWorldG threeWorldChancy .a ∧
  PropensityChanceAt threeWorldG threeWorldChancy .a .g ∧
  ¬ SetupInvariantAt threeWorldG threeWorldChancy .a .g

/-- **VG and the chance senses, nonvacuity.**

1. VG with its conclusion, trivially (`necessitarianG`: `g` gives `c` being in
   both worlds, so no giving differs); `g` is set-up necessitated.
2. VG with varying giving (`theistG`, `varyingState`): `g`'s giving and state
   vary together (CHANCE_2), and no being is an invariant two-way giver.
3. CHANCE_1 (`theistG`, `concurrence`): `g`'s giving varies with a concurring
   condition `d`.
4. Without VG, the theist and chance-rival models have an invariant two-way
   giver.
5. The chance senses are not exclusive: on `threeWorldG`, `threeWorldChancy`,
   `g` has CHANCE_2 (against `z`) and CHANCE_3 (against `b`) at `a`. -/
def SenseModels : Prop :=
  (VariationNeedsVaryingSetup necessitarianG simpleChancy false ∧
    NoTwoWayGiverWithInvariantSetup necessitarianG simpleChancy false ∧
    SetupNecessitatedAt necessitarianG simpleChancy false .g) ∧
  (VariationNeedsVaryingSetup theistG varyingState false ∧
    NoTwoWayGiverWithInvariantSetup theistG varyingState false ∧
    TwoWayGiverAt theistG false .g ∧ SetupVariationAt theistG varyingState false .g) ∧
  IncidentalVariationAt theistG concurrence false .g ∧
  (¬ NoTwoWayGiverWithInvariantSetup theistG simpleRational false ∧
    ¬ NoTwoWayGiverWithInvariantSetup theistG simpleChancy false) ∧
  (SetupVariationAt threeWorldG threeWorldChancy .a .g ∧
    PropensityChanceAt threeWorldG threeWorldChancy .a .g)

/-- The certificate: laws and models. -/
def Controls : Prop :=
  Laws ∧ TheistNonvacuity ∧ ChanceRival ∧ IntellectualChancer ∧ ChanceCoreDeletions ∧
    OmissionsIntellectRoute ∧ OmissionsHolderWill ∧ OmissionsThetaFive ∧ OmissionsGodWill ∧
    DNPStrictness ∧ SenseModels

end Model

end TruthCore.Causality.WillVersusChance
