module

public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Logic.CogitoEsse

@[expose] public section

namespace TruthCore.Results.Causality.UnderivedConcreteness

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessarilyUnderived (NecessarilyUnderived)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)

/-- Calibrate the very underived witness at the selected world. Its exclusion
of existing supporters transfers to the concrete restriction of the exact same
world-indexed relation. -/
theorem underivedConcreteOfCalibration {W B : Type} (m : Profile W B) (w : W)
    (hUnderived : NecessarilyUnderived m.ontic m.grounds w)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    NecessaryConcreteUnderivedAt m w := by
  obtain ⟨n, hExists, hNecessary, hUnderived⟩ := hUnderived
  refine ⟨n, hConcrete n hExists, hExists, hNecessary, ?_⟩
  intro v source _ hSource
  exact hUnderived v source hSource

open TruthCore.Causality.NecessaryConcreteUnderived (witnessProfile)

/-- The existing two-world witness supplies a joint instance of both inputs. -/
theorem jointlySatisfied :
    NecessarilyUnderived witnessProfile.ontic witnessProfile.grounds false ∧
      EveryExistentConcreteAt witnessProfile.ontic witnessProfile.concrete false :=
  ⟨⟨false, Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ hEdge => Bool.noConfusion hEdge.2.1⟩, fun _ _ => trivial⟩

/-- Keeping the ontology and grounds fixed, classify only the contingent
candidate as concrete. The underived witness survives and no concretum is
necessary, although a concrete individual exists at the selected world. -/
theorem calibrationOmission :
    let m : Profile Bool Bool := { witnessProfile with concrete := (· = true) }
    NecessarilyUnderived m.ontic m.grounds false ∧
      m.concrete true ∧ m.ontic.ExistsAt false true ∧
      ¬ NecessaryConcreteUnderivedAt m false := by
  refine ⟨jointlySatisfied.1, rfl, Or.inr rfl, ?_⟩
  rintro ⟨x, hx, _, hNecessary, _⟩
  change x = true at hx
  subst x
  rcases hNecessary true trivial with hFalse | hFalse <;> exact Bool.noConfusion hFalse

end TruthCore.Results.Causality.UnderivedConcreteness
