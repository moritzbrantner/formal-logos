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

/-- Joint satisfiability of the four premises of `derive`: a necessary
unlocated root, a contingent actual whole, and a distinct located occupant
grounded by the whole. Structural surrogate only. -/
theorem jointModel : JointModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨JointBeing.root, trivial, Or.inl rfl, fun _ _ => Or.inl rfl, ?_⟩
    intro v a _ _ h
    change v = false ∧ a = JointBeing.whole ∧ JointBeing.root = JointBeing.occupant at h
    cases h.2.2
  · exact ⟨trivial, Or.inr rfl⟩
  · refine ⟨Or.inr rfl, ⟨true, trivial, ?_⟩⟩
    intro h
    change JointBeing.whole = JointBeing.root ∨ true = false at h
    cases h with
    | inl h => cases h
    | inr h => cases h
  · intro x hx _ hLoc
    cases x with
    | root =>
      rcases hLoc with ⟨_, h⟩
      exact absurd rfl h
    | whole => exact absurd rfl hx
    | occupant =>
      change false = false ∧ JointBeing.whole = JointBeing.whole ∧
        JointBeing.occupant = JointBeing.occupant
      exact ⟨rfl, rfl, rfl⟩
  · refine ⟨JointBeing.occupant, ?_, ⟨trivial, Or.inr rfl⟩, ⟨(), ?_⟩, ?_⟩
    · intro h
      change JointBeing.occupant = JointBeing.whole at h
      cases h
    · intro h
      cases h
    · change false = false ∧ JointBeing.whole = JointBeing.whole ∧
        JointBeing.occupant = JointBeing.occupant
      exact ⟨rfl, rfl, rfl⟩

/-- Without the `Located F x` antecedent the bridge contradicts the other three
premises: the necessary root differs from the contingent whole, so the
unrestricted bridge would make the whole ground the underived root. -/
theorem unrestrictedInconsistent {W B : Type} (m : Profile W B) (w : W)
    (F : Frame B)
    (hUnderived : NecessaryConcreteUnderivedAt m w)
    (hWhole : ActualConcreteWholeAt m w F)
    (hCont : ContingentWholeAt m w F)
    (hPrior : UnrestrictedWholePriorityAt m w F) :
    False := by
  rcases hUnderived with ⟨x, hConcrete, hExists, hNecessary, hNoGround⟩
  have hDistinct : x ≠ F.whole := by
    intro hEq
    rcases hCont with ⟨_, v, hv, hAbsent⟩
    exact hAbsent (hEq ▸ hNecessary v hv)
  exact hNoGround w F.whole hWhole.1 hWhole.2
    (hPrior x hDistinct ⟨hConcrete, hExists⟩)

end TruthCore.Results.Ontology.SpacetimeGroundingBridge
