import TruthCore.Ontology.SpacetimeGroundingBridge

namespace TruthCore.Results.Ontology.SpacetimeGroundingBridge

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Causality.SameSourceWitness (UnderivedConcreteAt)
open TruthCore.Ontology.Spatiotemporal (Frame Located)
open TruthCore.Ontology.SpacetimeGroundingBridge

/-- The very same necessary underived candidate is not located, provided
the contingent whole is actual and grounds each distinct concrete occupant.
No geometric/physical-causal relation is substituted for existential grounding. -/
theorem selectedUnlocated {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : B) (hUnderived : UnderivedConcreteAt m w x)
    (hWhole : ActualConcreteWholeAt m w F)
    (hCont : ContingentWholeAt m w F)
    (hDep : OccupantsDependOnWholeAt m w F) :
    ¬ Located F x := by
  sorry

/-- Compose with the established root-route necessary-underived proposition.
The existential witness is the original underived witness, not an unrelated
spatial or God-naming witness. -/
theorem derive {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (hUnderived : NecessaryConcreteUnderivedAt m w)
    (hWhole : ActualConcreteWholeAt m w F)
    (hCont : ContingentWholeAt m w F)
    (hDep : OccupantsDependOnWholeAt m w F) :
    NecessaryUnderivedUnlocatedAt m w F := by
  sorry

/-- Countermodel with an actual grounding edge showing why geometrical
occupation and contingent spacetime do not entail the bridge. -/
theorem omission : OmissionControl := by
  sorry

end TruthCore.Results.Ontology.SpacetimeGroundingBridge
