module

public import TruthCore.Causality.Round2ExistenceAct

/-! Selected-world existential import and a process that survives the loss of each individual regime. -/

@[expose] public section

namespace TruthCore.Causality.ActualityImportControls

open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

section
variable {World Being Respect : Type} {m : Ontic World Being}
  {InAct : Being → Respect → Prop} {esse : Respect} {w : World}

theorem beingFromExistentialImport
    (hExisting : ExistingInActAt m InAct esse w)
    (hImport : ∀ x r, InAct x r → m.ExistsAt w x) :
    ActualityOnlyInsofarAsBeingReading InAct esse :=
  fun x r h => hExisting x (hImport x r h)

theorem existentialImportFromBeing
    (hSuffices : ActOfEsseSufficesForExistenceAt m InAct esse w)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse) :
    ∀ x r, InAct x r → m.ExistsAt w x :=
  fun x r h => hSuffices x (hBeing x r h)

end

namespace ProfileChange

-- none denotes cessation; the two live states are different regimes.
def act (s : Option Bool) (_ : Unit) : Option Bool → Prop
  | none => s.isSome = true
  | some k => s = some k

theorem importAt (s : Option Bool) :
    ActualityOnlyInsofarAsBeingReading (act s) none := by
  intro x r h
  cases r with
  | none => exact h
  | some k =>
    change s = some k at h
    subst s
    rfl

theorem eachCanCease (k : Bool) :
    ∃ s, act s () none ∧ ¬ act s () (some k) := by
  cases k
  · exact ⟨some true, rfl, by intro h; cases h⟩
  · exact ⟨some false, rfl, by intro h; cases h⟩

theorem neverAllAbsent :
    ¬ ∃ s, act s () none ∧ ∀ k, ¬ act s () (some k) := by
  rintro ⟨s, live, absent⟩
  cases s with
  | none => cases live
  | some k => exact absent k rfl

end ProfileChange

end TruthCore.Causality.ActualityImportControls
