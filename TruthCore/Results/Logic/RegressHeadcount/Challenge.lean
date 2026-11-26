import TruthCore.Logic.RegressHeadcount
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Logic.RegressHeadcount

open TruthCore.Logic.RegressHeadcount

theorem finiteAdditionCriterion (A B : Type) :
    SurvivesEveryFiniteAddition A B ↔ Finite A ∧ Infinite B := by
  sorry

/-- The cardinal reading applies to bearer headcount, or to distinct
independent posits when their assignment is injective along this regress. -/
theorem headcountCriterion : RegressHeadcountCriterion := by
  sorry

/-- Billing each pair together still incurs infinitely many distinct charges. -/
theorem pairedCharges :
    ¬ Function.Injective (fun n : ℕ => n / 2) ∧
      SurvivesEveryFiniteAddition Unit (Set.range (fun n : ℕ => n / 2)) := by
  sorry

end TruthCore.Results.Logic.RegressHeadcount
