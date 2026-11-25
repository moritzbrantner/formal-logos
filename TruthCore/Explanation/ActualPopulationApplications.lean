module

public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Results.Explanation.EmptyHistoryCausalAvailability.Solution

/-! Consequences of an actual concrete witness under explicit modal premises. -/

@[expose] public section

namespace TruthCore.Explanation.ActualPopulationApplications

open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

theorem possibleFromActual {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (w : W)
    (hActual : InhabitedConcreteAt A.ontic Concrete w)
    (hReflexive : ActualReflexive A.ontic w) :
    PossiblyInhabitedConcreteAt A Concrete w :=
  ⟨w, hReflexive, hActual⟩

open TruthCore.German.Kant.CosmologicalInference (NecessaryBeing)
open TruthCore.Modal (Euclidean)
open TruthCore.Logic (ExcludedMiddle)

/-- Use the actual individual as the population input on the very same arena. -/
theorem necessaryBeingFromActual {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (CauseFact : W → B → F → Prop) (w : W) (f : F)
    (hEM : ExcludedMiddle) (hEuclidean : Euclidean A.ontic.frame)
    (hReflexive : ActualReflexive A.ontic w) (hMeaning : NegativeFactMeaning A Concrete f)
    (hCoverage : AccessibleEmptyCoverage A Concrete CauseFact w)
    (hActual : InhabitedConcreteAt A.ontic Concrete w) : NecessaryBeing A.ontic w :=
  TruthCore.Results.Explanation.EmptyHistoryCausalAvailability.necessaryBeing
    A Concrete CauseFact w f hEM hEuclidean hReflexive hMeaning hCoverage
    (possibleFromActual A Concrete w hActual hReflexive)

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.ContingentBeingNode
open TruthCore.Logic.CogitoConcrete

theorem necessaryOrContingentFromActual {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w ∨ SomeActualContingentAt m w := by
  obtain ⟨x, hc, he⟩ := hPop
  rcases hEM (∃ v, m.ontic.frame.access w v ∧
      ¬ m.ontic.ExistsAt v x) with habs | hno
  · exact Or.inr ⟨x, hc, he, habs⟩
  · refine Or.inl ⟨x, hc, he, ?_⟩
    intro v hv
    rcases hEM (m.ontic.ExistsAt v x) with hx | hx
    · exact hx
    · exact False.elim (hno ⟨v, hv, hx⟩)

end TruthCore.Explanation.ActualPopulationApplications
