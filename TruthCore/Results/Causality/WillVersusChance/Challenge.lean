import TruthCore.Causality.WillVersusChance
import TruthCore.Results.Modal.PrussPowerPremises.Solution

/-! Choice versus chance at a necessary, patientless source (stage two,
`66aecdd7`): intellect and one power make every giving willed, and so make the
withholding holder a willed two-way giver; the Θ.5 principle restricted to
sources with an invariant set-up turns an invariant two-way giver into a being
with will, and with the GOD_4 bridge and #1897's creator premises gives GOD_4
will; the strong Θ.5 principle implies the restricted one. Analyst
reconstructions; attribution deferred. -/

namespace TruthCore.Results.Causality.WillVersusChance
open TruthCore.Causality.WillVersusChance
open TruthCore.Causality.WillVersusChance.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Modal.PrussPowerPremises (GivesTo GivingSameIn TwoWayGiverAt GivenExists
  ActualAbsenceHoldersGiveEach ActualAbsenceByWithholding)
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 Bg.forall_iff Bg.exists_iff V3.forall_iff
  V3.exists_iff theistG inertG nonFactiveG
  necessitarianG gFrame allC onlyCD uni gcEx gcAlways givesCHere givesCAlways noGiving gPower noPower)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt NoActualContingentConcreteIn
  ActualAbsenceInitiatorPresent)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (WillFollowsIntellectReading)
open TruthCore.Case.Catholicism (GodHasWill)

/-- Argument A, the intellect route to willed giving. An intellectual `y` has
will (will follows intellect, `090be689`), hence a rational power `q`; each
giving of `y` exercises some power `p` of `y`; with one power, `p = q`, so the
giving exercises a rational power. Constructive. -/
theorem oneIntellectualPowerGivesWilledGiving {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (HasIntellect HasWill : B → Prop)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hRat : WillIsRationalPower A HasWill)
    (hEx : GivingExercisesOwnPower F A) :
    OnePowerIntellectualGivingWilled F A HasIntellect := by
  sorry

/-- Argument B, the withholding holder gives by will. Withholding gives a holder
`y` at `w` that gives each actual contingent concretum being at `w` and none of
them at an accessible world `v` where it exists; P5 supplies one, `x`. The
holder has intellect and one power, so by argument A's conclusion its giving of
`x` at `w` exercises a rational power; its invariant set-up makes `v` a world
with the same set-up. Constructive. -/
theorem actualAbsenceHolderGivesByWill {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (HasIntellect : B → Prop) (w : W)
    (hWith : ActualAbsenceByWithholding F PowerFor concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hInv : ActualAbsenceHoldersSetupInvariant F A PowerFor concrete w)
    (hInt : ActualAbsenceHoldersHaveIntellect F PowerFor concrete HasIntellect w)
    (hOne : ActualAbsenceHoldersOnePower F A PowerFor concrete w)
    (hWilled : OnePowerIntellectualGivingWilled F A HasIntellect) :
    ActualAbsenceHolderGivesByWill F A PowerFor concrete w := by
  sorry

/-- Argument C, the Θ.5 bridge, restricted. A two-way giver `y` with an invariant
set-up gives `x` being at `w` by some power `p`, and does not give it at an
accessible `v` where it exists; DNP_inv makes `p` rational, and a being with a
rational power has will. Constructive. -/
theorem thetaFiveBridgeGivesWill {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (HasWill : B → Prop) (w : W)
    (hD : InvariantSetupVariationIsRational F A w)
    (hEx : GivingExercisesOwnPower F A)
    (hRW : RationalPowerIsWill A HasWill) :
    InvariantSetupTwoWayGiversWill F A HasWill w := by
  sorry

/-- Argument D, GOD_4 has will by the restricted Θ.5 bridge. Each GOD_4 `g`
exists at `w` and holds the power for the joint absence of the actual
contingent concreta (bridge); P2′ puts `g` at an accessible world `v` where they
are all absent; P5 gives one, `x`; by the creator reading `g` gives `x` being at
`w`, and by factive giving not at `v`. So `g` is a two-way giver at `w`; its
set-up is invariant (holder premise); argument C's conclusion gives it will.
Constructive. -/
theorem godHasWillByThetaFive {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod HasWill : B → Prop)
    (w : W)
    (hGod : GodsHoldActualAbsencePower F PowerFor concrete IsGod w)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hGive : ActualAbsenceHoldersGiveEach F PowerFor concrete w)
    (hFact : GivenExists F)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hInv : ActualAbsenceHoldersSetupInvariant F A PowerFor concrete w)
    (hWill : InvariantSetupTwoWayGiversWill F A HasWill w) :
    GodHasWill IsGod HasWill := by
  sorry

/-- Argument E, the strength order: DNP′ implies DNP_inv (an invariant set-up
gives the same set-up at the withholding world). Constructive. -/
theorem sameSetupVariationIsRationalWeakens {W B T R S P : Type}
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W)
    (hD : SameSetupVariationIsRational F A w) :
    InvariantSetupVariationIsRational F A w := by
  sorry

/-! ## Laws and models -/

macro "wc_unfold" : tactic => `(tactic|
  simp only [WillFollowsIntellectReading, WillIsRationalPower, GivingExercisesOwnPower,
    OnePowerIntellectualGivingWilled, SameSetupVariationIsRational, RationalPowerIsWill,
    InvariantSetupVariationIsRational, InvariantSetupTwoWayGiversWill,
    ActualAbsenceHoldersSetupInvariant, ActualAbsenceHoldersHaveIntellect,
    ActualAbsenceHoldersOnePower, ActualAbsenceHolderGivesByWill, GodsHoldActualAbsencePower,
    GodHasWill, SetupInvariantAt, SetupNecessitatedAt, OnePower, WilledTwoWayAt,
    PropensityChanceAt, VariationNeedsVaryingSetup, NoTwoWayGiverWithInvariantSetup,
    SetupVariationAt, IncidentalVariationAt, SetupSameIn, GivesBy,
    ActualAbsenceByWithholding, SomeContingentConcreteAt, NoActualContingentConcreteIn,
    ActualAbsenceInitiatorPresent, TruthCore.Modal.ModalGrounding.InitiatorPresentFor,
    ActualAbsenceHoldersGiveEach, GivenExists,
    TwoWayGiverAt, GivingSameIn, GivesTo, TruthCore.German.Kant.CosmologicalInference.ContingentAt,
    AgencyFrame.reclassify, simpleRational, simpleChancy, twoPowerChancer, idleRational,
    powerless, varyingState, varyingRational, concurrence, onlyG, nobody, onlyCD,
    gcHereOnlyEx, holderHereOnlyG, threeWorldG, threeWorldChancy, zFlag,
    theistG, inertG, nonFactiveG, necessitarianG, gFrame, allC, uni, gcEx, gcAlways, givesCHere,
    givesCAlways, noGiving, gPower, noPower])

/-- Argument F, the certificate of laws and models. Premise-free. -/
theorem willVersusChanceControls : Controls := by
  sorry

/-- Numerical completion, calibration, symmetry and choice-partition controls. -/
theorem distributionGroundingControls : DistributionGroundingControls := by
  sorry

end TruthCore.Results.Causality.WillVersusChance
