module

public import TruthCore.History.DisclosureIdentification

@[expose] public section

namespace TruthCore.Results.History.DisclosureIdentification

open TruthCore.History.SelectiveDisclosure
open TruthCore.History.DisclosureIdentification
open TruthCore.Science.Identifiability

private theorem absenceCriterion {H E : Type} (observe : H → List E)
    (occurs : H → E → Prop) (sound : ∀ h e, e ∈ observe h → occurs h e) :
    (∀ h e, occurs h e → e ∈ observe h) ↔
      ∀ h e, e ∉ observe h ↔ ¬ occurs h e := by
  classical
  constructor
  · intro covers h e
    exact ⟨absence_of_complete (occurs h) (observe h) (covers h) e,
      fun absent member => absent (sound h e member)⟩
  · intro criterion h e happened
    by_contra missing
    exact ((criterion h e).mp missing) happened

theorem boundary : Boundary := by
  have same : disclose true = disclose false := rfl
  have happened : occurrence true 0 := by simp [occurrence, occurred]
  have absent : ¬ occurrence false 0 := by simp [occurrence]
  refine ⟨fun _ _ => absenceCriterion, ?_, same, happened, absent, ?_, ?_⟩
  · intro earlier event member
    cases earlier
    · simpa [disclose, fullRecord, occurrence, selected] using member
    · exact selectiveTruthControl.2.1 event member
  · intro classifier
    have identifies := (proposition_criterion_iff disclose
      (fun earlier => occurrence earlier 0)).mp classifier
    exact absent (Eq.mp (identifies true false same) happened)
  · apply (proposition_criterion_iff fullRecord (fun earlier => occurrence earlier 0)).mp
    refine ⟨fun rows => (0 : Event) ∈ rows, ?_⟩
    intro earlier
    cases earlier <;> simp [fullRecord, full, selected, occurrence, occurred]

end TruthCore.Results.History.DisclosureIdentification
