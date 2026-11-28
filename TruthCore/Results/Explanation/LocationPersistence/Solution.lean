module

public import TruthCore.Explanation.LocationPersistence
public import TruthCore.Results.Explanation.PathRelocation.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.LocationPersistence

open TruthCore.Explanation.LocationPersistence
open TruthCore.Modal.TemporalHistory
open TruthCore.Results.Explanation.PathRelocation (constant_of_stationary)

theorem anchoredLocation : AnchoredLocation := by
  intro W B L h w x location s place sound stationary anchor t
  have constant := constant_of_stationary location stationary
  have report := (constant t).trans ((constant s).symm.trans anchor)
  exact ⟨report, sound t place report⟩

/-- A report of a place at either date supplies the presence presupposition
at that date. The stationarity calculation transports the report; it does
not provide its soundness. -/
theorem presenceAtBoth {W B L : Type} (h : History W B Int) (w : W) (x : B)
    (location : Int → Option L) (s t : Int) (place : L)
    (sound : Sound h w x location) (stationary : Stationary location)
    (anchor : location s = some place) : h.IsAt w x s ∧ h.IsAt w x t :=
  ⟨sound s place anchor, (anchoredLocation W B L h w x location s place sound stationary anchor t).2⟩

private def presentHistory : History Unit Unit Int where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun _ _ => True
             Causes := fun _ _ _ => False }
  IsAt := fun _ _ _ => True
  now := 0

/-- For the same everlasting bearer and the same initial location,
one sound trace stays and another changes position. -/
theorem samePresenceDifferentLocation : ReportedLocationContrast := by
  let stays : Int → Option Bool := fun _ => some true
  let moves : Int → Option Bool := fun t =>
    some (TruthCore.Explanation.PathRelocation.alt t)
  refine ⟨presentHistory, stays, moves, true, false, fun _ _ _ => trivial,
    fun _ _ _ => trivial, fun _ => rfl, rfl, by decide, rfl, by decide, by decide, ?_⟩
  exact fun t => (presenceAtBoth presentHistory () () stays 0 t true
    (fun _ _ _ => trivial) (fun _ => rfl) rfl).2

end TruthCore.Results.Explanation.LocationPersistence
