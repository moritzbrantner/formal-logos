import TruthCore.Causality.CounterfactualDependence

namespace TruthCore.Results.Causality.CounterfactualDependence

open TruthCore.Causality.Frame
open TruthCore.Causality.CounterfactualDependence
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modal.CounterfactualSelection

theorem dependence_excludes_being_without {W B T R : Type}
    (f : CausalityFrame W B T R) (select : Selector W) (w : W)
    (CanBeWithout : B → B → Prop)
    (track : DependenceTracksSelectedAbsence f select w)
    (cover : CoversAccessibleAbsence f select w)
    (realize : BeingWithoutHasAccessibleWitness f w CanBeWithout) :
    DependenceExcludesBeingWithout f.DependsForBeing CanBeWithout := by
  sorry

end TruthCore.Results.Causality.CounterfactualDependence
