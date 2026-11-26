import TruthCore.Modal.CounterfactualSelectionControls

namespace TruthCore.Results.Causality.CounterfactualWitnessCoverage

open TruthCore.Causality.Frame
open TruthCore.Causality.CounterfactualDependence
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modal.CounterfactualSelection
open TruthCore.Modal.CounterfactualSelectionControls
open Replacement

theorem full_coverage_preserves_witnesses {W B T R : Type}
    (f : CausalityFrame W B T R) (select : Selector W) (w : W)
    (cover : CoversAccessibleAbsence f select w) :
    PreservesAccessibleAbsenceWitnesses f select w := by
  sorry

theorem dependence_excludes_being_without_of_witnesses {W B T R : Type}
    (f : CausalityFrame W B T R) (select : Selector W) (w : W)
    (CanBeWithout : B → B → Prop)
    (track : DependenceTracksSelectedAbsence f select w)
    (preserve : PreservesAccessibleAbsenceWitnesses f select w)
    (realize : BeingWithoutHasAccessibleWitness f w CanBeWithout) :
    DependenceExcludesBeingWithout f.DependsForBeing CanBeWithout := by
  sorry

theorem witness_coverage_strictness : WitnessCoverageStrictness := by
  sorry

end TruthCore.Results.Causality.CounterfactualWitnessCoverage
