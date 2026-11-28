import TruthCore.Explanation.InertialActuality
import TruthCore.Results.Explanation.InducerFreePersistence.Solution
import TruthCore.Results.Explanation.LocationPersistence.Solution

namespace TruthCore.Results.Explanation.InertialActuality

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Explanation.InertialActuality
open TruthCore.Modal.TemporalHistory

theorem lawLeavesActualityOpen : LawLeavesActualityOpen := by
  sorry

theorem inertialReasonRequiresActuality : InertialReasonRequiresActuality := by
  sorry

theorem natureSelection {W B R : Type} (F : CausalityFrame W B Int R)
    (Essential : B → (W → Prop) → Prop) (φ : W → Prop) (x : B)
    (nature : NatureSuppliesActuality F Essential φ x) : NatureSelection F φ x := by
  sorry

theorem everlastingParity : EverlastingParity := by
  sorry

theorem otherBearerActualityOpen : OtherBearerActualityOpen := by
  sorry

theorem externalProtectionCompatible : ExternalProtectionCompatible := by
  sorry

theorem transferLocation {W B R : Type} (F : CausalityFrame W B Int R)
    (D : W → B → Int → Prop) (v : W) (x : B)
    (state : ExistenceStateWithoutProduction F D v x) :
    AnchoredExistenceWithoutProduction F D v x := by
  sorry

theorem locationDoesNotSupplyStateLaw : LocationDoesNotSupplyStateLaw := by
  sorry

theorem stateAndReceiptCompatible : StateAndReceiptCompatible := by
  sorry

end TruthCore.Results.Explanation.InertialActuality
