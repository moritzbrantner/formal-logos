module

public import Mathlib.Data.Rat.Defs

/-! An exact probability table for the evidence and incentive comparison.
The eight entries stipulate a truth, a signal and an independent bonus bit.
The force rule is the selected aim-relative stipulation. -/

@[expose] public section
namespace TruthCore.Logic.EvidenceAimTable

abbrev Row := Bool × Bool × Bool

def rows : List Row :=
  [false, true].flatMap fun w =>
    [false, true].flatMap fun s => [false, true].map fun b => (w, s, b)

def mass (r : Row) : ℚ := (if r.1 == r.2.1 then 3 else 1) / 16

def massOf (selected : Row → Bool) : ℚ :=
  ((rows.filter selected).map mass).sum

def posterior (selected : Row → Bool) : ℚ :=
  massOf (fun r => selected r && r.1) / massOf selected

theorem probabilities :
    massOf (fun _ => true) = 1 ∧ posterior (fun _ => true) = 1 / 2 ∧
    ∀ s b : Bool, posterior (fun r => r.2.1 == s && r.2.2 == b) = (if s then 3 else 1) / 4 ∧
      posterior (fun r => r.2.2 == b) = 1 / 2 := by
  decide +kernel

def merit (s answer : Bool) : Bool := s == answer
def force (aim s answer : Bool) : Bool := aim && merit s answer

theorem aimControls : ∀ aim s answer : Bool,
    (merit s answer = true ↔ answer = s) ∧
    (force aim s answer = true ↔ aim = true ∧ answer = s) := by
  decide +kernel

end TruthCore.Logic.EvidenceAimTable
