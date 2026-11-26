module

/-! Finite routing comparisons for one editorial, one booking-based and one
direct-readability implementation. Readability is stipulated for each version. -/

@[expose] public section
namespace TruthCore.Explanation.DispatchControls

abbrev Version := Bool

def select (readable : Version → Bool) (tie : Version) : Version :=
  if readable tie then tie else !tie

def dispatch (readable : Version → Bool) (booking tie : Version) (connected : Bool) :
    Option Version × Version × Version :=
  let instruction := select readable tie
  (if connected then some instruction else none, booking, select readable tie)

def only (v : Version) (w : Version) : Bool := v == w

def report (v : Version) (readable : Version → Bool) : Option Version :=
  if readable v then some v else none

theorem aligned : ∀ v,
    let sent := dispatch (only v) v v true
    sent = (some v, v, v) ∧
    sent.1.bind (report · (only v)) = some v ∧
    report sent.2.1 (only v) = some v ∧ report sent.2.2 (only v) = some v := by
  decide +kernel

theorem interventions :
    dispatch (only false) false false false = (none, false, false) ∧
    dispatch (only true) false false true = (some true, false, true) ∧
    dispatch (fun _ => true) false false true = (some false, false, false) ∧
    dispatch (fun _ => true) false true true = (some true, false, true) := by
  decide +kernel

end TruthCore.Explanation.DispatchControls
