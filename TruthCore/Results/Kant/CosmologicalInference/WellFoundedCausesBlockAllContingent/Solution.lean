module

public import TruthCore.Causality.GroundingRegress
public import TruthCore.Logic.RootDescent

@[expose] public section

namespace TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent
open TruthCore.Causality.GroundingRegress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic.RootDescent (not_of_inherited)

/-- Suppose every existing being is contingent. By well-founded induction on
the world's causal relation, no being exists: an existing being would be
contingent, so by the local causal principle it would have an existing cause,
which by the induction hypothesis does not exist. This contradicts the given
existent. No classical logic and no axiom is used. -/
theorem wellFoundedCausesBlockAllContingent : WellFoundedCausesBlockAllContingent := by
  intro World Entity m w hLocal hWF ⟨x, hx⟩ hAll
  exact not_of_inherited hWF (fun z hz =>
    let ⟨y, hy, hCauses, _⟩ := hLocal w z (hAll z hz); ⟨y, hCauses, hy⟩) x hx

end TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent
