module

public import TruthCore.Causality.AppetitePowerExercise

/-! Removing appraisal as good from the possessed-love interpretation isolates one admission condition of an exercise. -/

@[expose] public section

namespace TruthCore.Causality.AppetiteAppraisal

open TruthCore.Causality.AppetitePowerExercise

def suitableOnly : Interpretation :=
  { possessedLove with apprehendsGood := fun _ _ _ => False }

def suitableOnlyCapacity : Capacity suitableOnly () where
  possible := fun _ _ r => r = .love
  apprehension := fun _ _ _ _ => Or.inl True.intro
  seeking := fun _ _ h => nomatch h
  loving := fun _ _ _ => True.intro
  delighting := fun _ _ h => nomatch h
  communicating := fun _ _ _ h => nomatch h

theorem signatureBoundary : suitableOnlyCapacity.Possessed ∧
    suitableOnly.apprehendsSuitable () () () ∧
    suitableOnly.possessed () () () ∧ suitableOnly.loves () () () ∧
    ¬ suitableOnly.apprehendsGood () () () ∧
    ¬ Nonempty (Exercise suitableOnly () () ()) := by
  refine ⟨⟨True.intro, (), (), .love, rfl⟩,
    True.intro, True.intro, True.intro, (fun h => h), ?_⟩
  rintro ⟨e⟩
  cases e with
  | seeking good _ _ => exact good
  | loving good _ _ => exact good
  | delighting good _ _ => exact good
  | communicating _ good _ _ _ => exact good

end TruthCore.Causality.AppetiteAppraisal
