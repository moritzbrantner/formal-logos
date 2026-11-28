import TruthCore.Ethics.TrolleyRowe
import TruthCore.Results.Ethics.Trolley.Solution

/-! Which sense of "wholly good" yields Rowe's permission constraint
(analyst formulation; attribution deferred). -/

namespace TruthCore.Results.Ethics.TrolleyRowe
open TruthCore.Ethics.Trolley TruthCore.Ethics.TrolleyRowe TruthCore.English.Rowe
open TruthCore.Results.Ethics.Trolley (switch_notMeans chainMeans loop_means sideEffect_notMeans)

/-- WHOLLY_GOOD_1 with the outcome bridge yields Rowe's simplified permission
constraint: an unblocked preventable suffering would be strictly better prevented,
which an outcome-minimizing wholly good being does not permit. -/
theorem outcomeSenseYieldsPermissionConstraint (s : Sig) (W : PreventionWays s)
    (hO : OutcomeStandard s W) (hB : UnblockedPreventionBetter s W) :
    PermissionConstraintReading s := by
  sorry

/-- WHOLLY_GOOD_2 with the same bridge yields only the constraint-qualified
permission condition. -/
theorem constraintSenseYieldsQualifiedConstraint (s : Sig) (W : PreventionWays s)
    (hS : ConstraintStandard s W) (hB : UnblockedPreventionBetter s W) :
    ConstraintQualifiedPermission s W := by
  sorry

theorem controls : GoodnessSenseControls := by
  sorry

end TruthCore.Results.Ethics.TrolleyRowe
