module

public import TruthCore.Explanation.PathRelocation

/-! A location trace for one designated bearer in one history. A reported
location requires presence. An unreported location leaves presence open.
The trace records position only and carries no giving or causal relation. -/

@[expose] public section

namespace TruthCore.Explanation.LocationPersistence

open TruthCore.Modal.TemporalHistory
open TruthCore.Explanation.PathRelocation (Follows)

variable {W B L : Type}

/-- A reported location is sound for the same bearer, world and moment. -/
def Sound (h : History W B Int) (w : W) (x : B) (location : Int → Option L) : Prop :=
  ∀ t place, location t = some place → h.IsAt w x t

/-- Controlled local transition: the reported location is unchanged on each
adjacent pair. The reversible window is a mathematical control, not a law
asserted about actual trees or existential persistence. -/
def Stationary (location : Int → Option L) : Prop :=
  Follows (fun _ earlier later => later = earlier) location

/-- The anchored stationary location trace preserves the location and its
presence presupposition throughout the same modeled history. -/
def AnchoredLocation : Prop :=
  ∀ (W B L : Type) (h : History W B Int) (w : W) (x : B)
    (location : Int → Option L) (s : Int) (place : L),
    Sound h w x location → Stationary location → location s = some place →
      ∀ t, location t = some place ∧ h.IsAt w x t

end TruthCore.Explanation.LocationPersistence
