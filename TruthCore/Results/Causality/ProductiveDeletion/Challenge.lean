import TruthCore.Causality.ProductiveDeletion

namespace TruthCore.Results.Causality.ProductiveDeletion
open TruthCore.Causality.ProductiveDeletion
open TruthCore.Causality.JointGroups (Groups Exercise)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.AcquiredHistoryTransfer (CoveredAncestry)
open TruthCore.Causality.ExerciseContribution (Step)

/-- Transport the derivation unless it already contains a positive-length
selected branch. At a joint node the other inputs have original supply even
when only one of them continues the selected branch. -/
theorem pathOfLoss {h : Groups E G} {I : E → Prop} {selected : Set E} {v : E}
    (original : Supply h I v) (loss : ¬ Supply (withoutInputs h selected) I v) :
    ∃ u ∈ selected, Relation.TransGen (SuppliedStep h I) u v := by
  sorry

theorem selfInputSurvives {h : Groups E G} {I : E → Prop} {v : E}
    (original : Supply h I v) : Supply (withoutInputs h {v}) I v := by
  sorry

theorem ancestryFromLosses (m : Exercise B E G S) (covered : B → E → Prop)
    (I : E → Prop) (selected : B → E → Set E)
    (cuts : CoveredLosses m covered I selected) : CoveredAncestry m covered := by
  sorry

open TruthCore.Causality.ExerciseContribution.Press

theorem pressLoss : PressLoss := by
  sorry

end TruthCore.Results.Causality.ProductiveDeletion
