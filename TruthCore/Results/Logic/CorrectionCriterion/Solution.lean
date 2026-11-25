module

public import TruthCore.Logic.CorrectionCriterion
public import TruthCore.Logic.InformationInvariance

@[expose] public section

namespace TruthCore.Results.Logic.CorrectionCriterion
open TruthCore.Logic.CorrectionCriterion

/-- Exact extensional classification is equivalent to invariance under
identical data. Both nonconstant-norm controls are included. This proves no
criterion's justification and settles no private-language or truth theory. -/
theorem characterization : CriterionCharacterizationAndControls := by
  have factor : CriterionCharacterization := by
    intro State Evidence observe Correct
    exact TruthCore.Logic.InformationInvariance.factor_iff observe Correct
  refine ⟨factor, rfl, ?_, ?_⟩
  · intro h
    have invariant := (factor Bool (Bool × Bool)
      (fun _ => (true, true)) (fun s => s = true)).mp h
    have bad : false = true := (invariant false true rfl).mpr rfl
    cases bad
  · exact ⟨(fun s => s = true), fun _ => Iff.rfl⟩

end TruthCore.Results.Logic.CorrectionCriterion
