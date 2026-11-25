module

public import TruthCore.Results.Logic.CorrectionCriterion.Solution

/-! Location reports determine a coarse task norm; a chemical distinction can vary while those reports remain fixed. -/

@[expose] public section

namespace TruthCore.Logic.FinerContentCriterion

open TruthCore.Logic.CorrectionCriterion

-- First coordinate: task-relevant location. Second: finer chemical kind.
abbrev Situation := Bool × Bool

def taskData (r : Bool) (s : Situation) : Prop × Prop :=
  (r = s.1, (!r) ≠ s.1)

def fineMatch (r : Bool) (s : Situation) : Prop := r = s.1 ∧ s.2 = true

theorem sameLocationTest (r : Bool) (s : Situation) : (r = s.1) ↔ ((!r) ≠ s.1) := by
  obtain ⟨place, chemical⟩ := s
  cases r <;> cases place <;> cases chemical <;> decide

theorem locationAdmitsCriterion (r : Bool) : AdmitsCriterion (taskData r) (fun s => r = s.1) := by
  exact ⟨Prod.fst, fun _ => Iff.rfl⟩

theorem finerContentLacksCriterion (r : Bool) : ¬ AdmitsCriterion (taskData r) (fineMatch r) := by
  intro h
  have invariant :=
    (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
      Situation (Prop × Prop) (taskData r) (fineMatch r)).mp h
  have same : taskData r (r, false) = taskData r (r, true) := rfl
  have bad := (invariant (r, false) (r, true) same).mpr ⟨rfl, rfl⟩
  exact Bool.noConfusion bad.2

theorem finerDataAdmitCriterion (r : Bool) :
    AdmitsCriterion (fun s : Situation => (taskData r s, s.2)) (fineMatch r) := by
  exact ⟨fun data => data.1.1 ∧ data.2 = true, fun _ => Iff.rfl⟩

end TruthCore.Logic.FinerContentCriterion
