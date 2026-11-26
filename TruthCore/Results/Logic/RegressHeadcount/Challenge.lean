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

/-- An infinite bill with finitely many positions per visited charge requires
infinitely many distinct charges, regardless of how large the finite groups are. -/
theorem finiteFibersChargeInfinitely {Position Posit Alternative : Type} [Infinite Position]
    (billing : Position → Posit)
    (finitePerCharge : ∀ posit ∈ Set.range billing, (billing ⁻¹' {posit}).Finite)
    (finiteAlternative : Finite Alternative) :
    SurvivesEveryFiniteAddition Alternative (Set.range billing) := by
  sorry

/-- An infinite group can coexist with infinitely many distinct visited charges. -/
theorem mixedChargeFibers :
    let billing := fun n : ℕ => if n % 2 = 0 then 0 else n
    (billing ⁻¹' {0}).Infinite ∧
      SurvivesEveryFiniteAddition Unit (Set.range billing) := by
  sorry

end TruthCore.Results.Logic.RegressHeadcount
