module

public import TruthCore.Case.Catholicism.StageOneQuartaVia

/-! The added-giver comparison tests causal coverage. The governor comparison locates corrective operation in the producer or its product. -/

@[expose] public section

namespace TruthCore.Causality.GiverPerfectionControls

open TruthCore.Case.Catholicism
namespace AdditionalGiver
variable {B R : Type} (act : B → R → Prop) (cause : B → B → R → Prop)
  (esse : R) (a x : B)

def added (c y : B) (r : R) := cause c y r ∨ (c = a ∧ y = x ∧ r = esse)

theorem transferAfter [DecidableEq R] (initial : CauseOfBeingCausesEveryPerfection act cause esse) :
    CauseOfBeingCausesEveryPerfection act (added cause esse a x) esse ↔
    ∀ r, r ≠ esse → act x r → cause a x r := by
  constructor
  · intro h r different actual
    obtain h | ⟨_, _, eq⟩ := h a x r (Or.inr ⟨rfl, rfl, rfl⟩) actual
    · exact h
    · exact False.elim (different eq)
  · intro coverage c y r incoming actual
    rcases incoming with old | ⟨rfl, rfl, _⟩
    · exact Or.inl (initial c y r old actual)
    · by_cases same : r = esse
      · exact Or.inr ⟨rfl, rfl, same⟩
      · exact Or.inl (coverage r same actual)

end AdditionalGiver

namespace Operative

-- Signed displacement, followed by the source's own correction command.
def governorCommand (error : Int) := -error

def sourceCommand (feedback : Bool) (error : Int) : Int :=
  if feedback then governorCommand error else 0

-- Both constructors release the same governor at each chosen setpoint.
def productCommand (_feedback : Bool) (setpoint actual : Int) :=
  governorCommand (actual - setpoint)

def hasCorrection (feedback : Bool) : Prop :=
  ∀ error, sourceCommand feedback error = -error

theorem sourceTest (feedback : Bool) : hasCorrection feedback ↔ feedback = true := by
  cases feedback
  · constructor
    · intro h
      have bad := h 1
      exact (by decide : (0 : Int) ≠ -1) bad |>.elim
    · intro h
      cases h
  · exact ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem noOutputTest (test : (Int → Int → Int) → Prop) :
    ¬ ∀ f, test (productCommand f) ↔ hasCorrection f := by
  intro h
  have yes := (h true).2 ((sourceTest true).2 rfl)
  have no := (sourceTest false).1 ((h false).1 yes)
  cases no

end Operative

end TruthCore.Causality.GiverPerfectionControls
