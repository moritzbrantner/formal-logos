module

public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.FinitePopulationCover
public import TruthCore.Causality.NecessarilyUnderived

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.AccessibleSuccessor

open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AccessibleSuccessor)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- The same selected world witnesses the local accessible-successor condition. -/
theorem accessibleSuccessorOfActualReflexive {W B : Type} (m : Ontic W B) (w : W)
    (h : ActualReflexive m w) : AccessibleSuccessor m.frame w := by
  exact ⟨w, h⟩

end TruthCore.Results.Case.Catholicism.AccessibleSuccessor
