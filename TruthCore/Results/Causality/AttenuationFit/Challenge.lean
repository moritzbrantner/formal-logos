import TruthCore.Causality.AttenuationFit
import TruthCore.Results.Causality.ConcreteRootAccess.Solution

/-! Fitting the quantitative reception witnesses to finite root access in the
same profile and world. Analyst construction, attribution deferred. -/

namespace TruthCore.Results.Causality.AttenuationFit

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.ClosedGroundingRoots
open TruthCore.Causality.ConcreteRootAccess (RootAccess)
open scoped BigOperators

/-- When the quantitative witnesses are existentially chosen, attenuation has
exactly the content of countability and closed-collection rootedness. -/
theorem attenuationIffCountableAndClosedRooted (m : Profile W B) (w : W) :
    AttenuationFitCriterion m w := by
  sorry

open TruthCore.Causality.ClosedGroundingRoots.FixedAmounts

/-- With positive amounts fixed first, the full reception constraints on this graph
admit a choice of weights, inputs and bounds exactly when the recipient has less. -/
theorem fixedAmountCriterion : FixedAmounts.FixedAmountCriterion := by
  sorry

end TruthCore.Results.Causality.AttenuationFit
