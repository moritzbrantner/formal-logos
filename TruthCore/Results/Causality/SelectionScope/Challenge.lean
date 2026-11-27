import TruthCore.Causality.SelectionScope

namespace TruthCore.Results.Causality.SelectionScope

open TruthCore.Modal.STIT
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.SelectionScope
open TruthCore.Causality.SelectionScope.Model
open TruthCore.Modal.PrussPowerPremises (GivesTo FixedGiver ActualAbsenceByWithholding)
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 vanCleveG theistG allC gPower gFrame uni
  replEx givesCHere givesDThere vcEx)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn NoContingentConcreteIn)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.WillVersusChance (GodsHoldActualAbsencePower)

/-! ## Part A -/

theorem selectionRangeLaws : SelectionRangeLaws := by
  sorry

/-! ### The four-account table -/

theorem fourAccountTable : FourAccountTable := by
  sorry

/-! ## Part B -/

theorem omissionScopeTable : OmissionScopeTable := by
  sorry

/-! ### The complete-decision fork -/

theorem completeDecisionFork : CompleteDecisionFork := by
  sorry

/-! ## Part C -/

/-- `0050b6ed` from its total-refraining sibling, Euclidean access and monotone
powers. -/
theorem actualAbsencePowerOfTotal {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod : B → Prop) (w : W)
    (hTotal : GodsHoldTotalAbsencePower F PowerFor concrete IsGod w)
    (hEuclid : TruthCore.Modal.Euclidean F.history.ontic.frame)
    (hMono : PowerForMonotoneAt F PowerFor w) :
    GodsHoldActualAbsencePower F PowerFor concrete IsGod w := by
  sorry

theorem actualAbsencePowerScopeControls : ActualAbsencePowerScopeControls := by
  sorry

end TruthCore.Results.Causality.SelectionScope
