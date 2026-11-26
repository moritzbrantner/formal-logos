import TruthCore.Modal.ModalPowerHolder
import TruthCore.Causality.ActualOnlyEuclidean

namespace TruthCore.Results.Modal.ModalPowerHolder
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ActualOnlyEuclidean (TransitiveAt)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AccessibleSuccessor)
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.ModalPowerHolder
open TruthCore.Modal.PrussPowerPremises

theorem jointAbsenceOfFiniteRoster {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (w : W)
    (hAccess : AccessibleSuccessor F.history.ontic.frame w)
    (hAmalgam : ActualRosterAmalgamates F concrete w)
    (hFinite : ActualRosterFinite F concrete w) :
    PossiblyNoActualContingentConcrete F concrete w := by sorry

theorem globalAbsenceOfRosterCoverage {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (w : W)
    (hTrans : TransitiveAt F.history.ontic.frame w)
    (hJoint : PossiblyNoActualContingentConcrete F concrete w)
    (hCover : ActualRosterCoversAtAbsence F concrete w) :
    PossiblyNoContingentConcrete F concrete w := by sorry

theorem differentGivingOfOneRecipient {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hGive : ActualAbsenceHoldersGiveSome F PowerFor concrete w)
    (hFactive : GivenExists F) :
    ActualAbsenceExerciseDiffers F PowerFor concrete w := by sorry

theorem controls : Model.Controls := by sorry

end TruthCore.Results.Modal.ModalPowerHolder
