import TruthCore.Modal.PrussPowerPremises
import TruthCore.Results.Modal.ModalGroundingActualAbsence.Solution

/-! The power premises of the route with Pruss's own premise (#1887,
continued): the transfer from the collective power to powers over each actual
contingent's esse, the one-way/two-way profile of the holder's giving, and
Pruss's own direction. Analyst reconstructions; attribution deferred. Excluded
middle enters only as the explicit premise `TruthCore.Logic.ExcludedMiddle`. -/

namespace TruthCore.Results.Modal.PrussPowerPremises
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.PrussPowerPremises
open TruthCore.Modal.PrussPowerPremises.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsse)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)

/-- Argument 1, the transfer. A concrete `x` is contingent at `w`, so the joint
absence `q` fails at `w`, while P4′ gives an accessible world where it holds;
P1′ gives a being `y` at `w` with a power for `q`; the transfer gives `y`
POWER_OVER_ESSE_1 over each concrete being contingent at `w`. Constructive. -/
theorem transferGivesPowerOverEachActualContingent {W B T R : Type}
    (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (PowerOver : B → B → R → Prop) (concrete : B → Prop) (w : W)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hTransfer : ActualAbsencePowerIsPowerOverEsse F PowerFor PowerOver concrete w) :
    SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w := by
  sorry

/-- Argument 2, the holder is a necessary varying giver. P2δ gives P2′, so the
route `prussActualAbsenceNecessaryPowerHolder` (#1889) gives a necessary
concrete holder `y` of a power for `q`; P2δ applied to `y` gives an accessible
world where `y` exists and gives being otherwise than at `w`. -/
theorem actualAbsenceHolderIsNecessaryVaryingGiver {W B T R : Type}
    (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop)
    (w : W) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hDiff : ActualAbsenceExerciseDiffers F PowerFor concrete w)
    (hConcrete : ActualAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w) :
    NecessaryVaryingGiverWithActualAbsencePower F PowerFor concrete w := by
  sorry

/-- Argument 3, projection onto the route's conclusion `b90ee2de`: forget the
varying giving. An assembly. -/
theorem varyingGiverGivesNecessaryPowerHolder {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (h : NecessaryVaryingGiverWithActualAbsencePower F PowerFor concrete w) :
    NecessaryConcreteActualAbsencePowerAt F PowerFor concrete w := by
  sorry

/-- Argument 4, the joint absence realized by withholding. P1′ gives a holder
`y` at `w`; P2′ an accessible world `v` where `q` holds and `y` exists. By the
creator reading `y` gives each actual contingent concretum being at `w`; at `v`
each is absent, so by factive giving `y` gives none of them being there.
Constructive. -/
theorem actualAbsenceRealizedByWithholding {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hGive : ActualAbsenceHoldersGiveEach F PowerFor concrete w)
    (hFactive : GivenExists F) :
    ActualAbsenceByWithholding F PowerFor concrete w := by
  sorry

/-- Argument 5, the transfer's conclusion without the transfer: a holder that
gives each actual contingent concretum being at `w` and withholds each at an
accessible world where it exists has, by the withheld-giving bridge,
POWER_OVER_ESSE_1 over each. -/
theorem withholdingGivesPowerOverEachActualContingent {W B T R : Type}
    (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (PowerOver : B → B → R → Prop) (concrete : B → Prop) (w : W)
    (hWith : ActualAbsenceByWithholding F PowerFor concrete w)
    (hBridge : WithheldGivingIsPowerOverEsse F PowerOver w) :
    SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w := by
  sorry

/-- Argument 6, Pruss's own direction. P4′ gives an accessible world `v`
lacking every actual contingent concretum; P5's witness shows `v ≠ w`;
symmetric access gives `v`'s access to `w`; grounding at `v` gives a being `y`
at `v` with a power for `w`'s obtaining; initiator presence puts `y` at `w`; `y`
is concrete. Were `y` absent at some world accessible from `w`, it would be an
actual contingent concretum, hence absent at `v`, where it exists. Excluded
middle gives `y`'s existence at every world accessible from `w`. Only the B
part (symmetry) of S5 is used. -/
theorem prussDirectionNecessaryHolder {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hSym : TruthCore.Modal.Symmetric F.history.ontic.frame)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w)
    (hGround : ActualityGroundedAtAbsenceWorlds F PowerFor concrete w)
    (hInit : ActualityInitiatorPresentAtAbsenceWorlds F PowerFor concrete w)
    (hConcrete : ActualityPowerHoldersConcreteAtAbsenceWorlds F PowerFor concrete w) :
    NecessaryConcreteHolderOfActualityPower F PowerFor concrete w := by
  sorry

/-- Argument 7, projection of Pruss's direction onto the stage-one node:
forget the power and the absence world. An assembly. -/
theorem prussDirectionNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W) (h : NecessaryConcreteHolderOfActualityPower F PowerFor concrete w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  sorry

/-- Argument 9, the transfer's conclusion at the foundational case. A concrete
foundational being `f` at `w` (statement `c5da5e62`) is under no being's
POWER_OVER_ESSE_1; were it absent at a world accessible from `w`, it would be a
concrete being contingent at `w`, over whose esse the holder has power. So,
with excluded middle, `f` exists at every accessible world and witnesses the
stage-one node. PGP's verdict at the foundational case, reproduced through the
distributive powers, without PGP and without a Euclidean premise. -/
theorem powerOverEachGivesNecessaryConcrete {W B T R P : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (PowerOver : B → B → R → Prop)
    (concrete : B → Prop) (grounds : W → B → B → Prop) (w : W) (essenceOf esseOf : B → P)
    (Received : B → P → Prop) (ComposedOfMatterAndForm : B → Prop)
    (CanFailToBe : B → R → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hEach : SomeHolderHasPowerOverEachActualContingent F PowerFor PowerOver concrete w)
    (hFound : SomeConcreteFoundationalAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver concrete) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  sorry

/-! ## Laws and models -/

macro "pp_unfold" : tactic => `(tactic|
  simp only [ActualAbsenceGrounded, ActualAbsenceInitiatorPresent, ActualAbsencePowerHoldersConcrete,
    PossiblyNoActualContingentConcrete, SomeContingentConcreteAt, NoActualContingentConcreteIn,
    AristotelianGroundingFor, InitiatorPresentFor, PowerHoldersConcreteFor,
    ActualAbsenceExerciseDiffers, ActualAbsenceHoldersGiveEach, GivenExists,
    ActualAbsencePowerIsPowerOverEsse, WithheldGivingIsPowerOverEsse,
    ActualityGroundedAtAbsenceWorlds, ActualityInitiatorPresentAtAbsenceWorlds,
    ActualityPowerHoldersConcreteAtAbsenceWorlds, SomeHolderHasPowerOverEachActualContingent,
    NecessaryVaryingGiverWithActualAbsencePower, ActualAbsenceByWithholding,
    NecessaryConcreteHolderOfActualityPower, EachActualAbsenceGrounded,
    EachActualAbsenceInitiatorPresent, TwoWayGiverAt, GivingVariesAt, FixedGiver, GivingSameIn,
    GivesTo, PowerOverEsse, NecessaryAt, ContingentAt, TruthCore.Modal.Symmetric,
    theistG, nonFactiveG, replacementG, inertG, necessitarianG, forwardG, absentHolderG, mutualG,
    vanCleveG, gFrame, allC, onlyCD, uni, forwardOnly, gcEx, gcAlways, replEx, gOnlyThereEx,
    givesCHere, givesCAlways, givesDThere, noGiving, gPower, gPowerThere, noPower,
    positivePower, gOverC, gOverCD, gOverD, noOver, pairEx, annihilatorPower, vcEx, vcGives])

/-- Argument 8, the certificate of laws and models. Premise-free. -/
theorem prussPowerControls : Controls := by
  sorry

/-- Argument 10, collective without distributive with two members.
Premise-free. -/
theorem twoMemberCollective : TwoMemberCollective := by
  sorry

end TruthCore.Results.Modal.PrussPowerPremises
