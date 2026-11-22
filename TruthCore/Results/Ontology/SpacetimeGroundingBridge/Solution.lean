module

public import TruthCore.Ontology.SpacetimeGroundingBridge

@[expose] public section
namespace TruthCore.Results.Ontology.SpacetimeGroundingBridge

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Causality.SameSourceWitness (UnderivedConcreteAt)
open TruthCore.Ontology.Spatiotemporal (Frame Located)
open TruthCore.Ontology.SpacetimeGroundingBridge

/-- The root itself, not a second, unconnected individual, is unlocated under
the explicit contingent-whole and selected existential-grounding premises. -/
theorem selectedUnlocated {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : B) (hUnderived : UnderivedConcreteAt m w x)
    (hWhole : ActualConcreteWholeAt m w F)
    (hCont : ContingentWholeAt m w F)
    (hDep : OccupantsDependOnWholeAt m w F) :
    ¬ Located F x := by
  rcases hUnderived with ⟨hConcrete, hExists, hNecessary, hNoGround⟩
  have hDistinct : x ≠ F.whole := by
    intro hEq
    rcases hCont with ⟨_, v, hv, hAbsent⟩
    exact hAbsent (hEq ▸ hNecessary v hv)
  intro hLocated
  exact hNoGround w F.whole hWhole.1 hWhole.2
    (hDep x hDistinct ⟨hConcrete, hExists⟩ hLocated)

/-- Reuse the existing same-witness equivalence for the actual necessary
underived root; no independent spatial or divine bearer is introduced. -/
theorem derive {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (hUnderived : NecessaryConcreteUnderivedAt m w)
    (hWhole : ActualConcreteWholeAt m w F)
    (hCont : ContingentWholeAt m w F)
    (hDep : OccupantsDependOnWholeAt m w F) :
    NecessaryUnderivedUnlocatedAt m w F := by
  rcases (TruthCore.Causality.SameSourceWitness.underived_iff m w).mp hUnderived
    with ⟨x, hx⟩
  exact ⟨x, hx, selectedUnlocated m w F x hx hWhole hCont hDep⟩

/-- Both modal and existential profiles are populated, with an actual
grounding edge; the missing whole-to-occupant bridge is indispensable for
this model. Finite model adequacy is limited to the displayed predicates. -/
theorem omission : OmissionControl := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, Or.inr rfl⟩
  · refine ⟨Or.inr rfl, ⟨true, trivial, ?_⟩⟩
    intro h
    change true = false ∨ true = false at h
    cases h with
    | inl h => cases h
    | inr h => cases h
  · refine ⟨false, trivial, Or.inl rfl, ?_, ?_⟩
    · intro v _
      exact Or.inl rfl
    · intro v a _ _ h
      change a = false ∧ false = true ∧ v = false at h
      cases h.2.1
  · change false = false ∧ true = true ∧ false = false
    exact ⟨rfl, rfl, rfl⟩
  · intro h
    have hLoc : Located sampleFrame false := ⟨(), trivial⟩
    have hEdge := h false (by decide) ⟨trivial, Or.inl rfl⟩ hLoc
    change true = false ∧ false = true ∧ false = false at hEdge
    cases hEdge.1
  · rintro ⟨x, _, hNotLocated⟩
    exact hNotLocated ⟨(), trivial⟩

end TruthCore.Results.Ontology.SpacetimeGroundingBridge
