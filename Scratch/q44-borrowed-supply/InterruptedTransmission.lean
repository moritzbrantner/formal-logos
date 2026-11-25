import TruthCore.Causality.EssentialPower
import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
import TruthCore.Causality.Q44EssentialSource

namespace InterruptedTransmission

open TruthCore.Causality (PowerTransmissionRule)
open TruthCore.Causality.Q44EssentialSource (ParticipatedHasEssentialSource)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause)
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource (tailAtState)

/-- Link x carries from its immediate upstream neighbour x+1. -/
def edge (live : Nat → Prop) (c x : Nat) : Prop := c = x + 1 ∧ live x

def clearFrom (live : Nat → Prop) (x : Nat) : Prop :=
  ∀ j, x ≤ j → live j

theorem equation {live active : Nat → Prop} :
    PowerTransmissionRule (edge live) active ↔
      ∀ x, active x ↔ live x ∧ active (x + 1) := by
  constructor
  · intro law x
    constructor
    · intro hx
      obtain ⟨c, ⟨rfl, intact⟩, hc⟩ := (law x).mp hx
      exact ⟨intact, hc⟩
    · rintro ⟨intact, hc⟩
      exact (law x).mpr ⟨x + 1, ⟨rfl, intact⟩, hc⟩
  · intro law x
    constructor
    · intro hx
      obtain ⟨intact, hc⟩ := (law x).mp hx
      exact ⟨x + 1, ⟨rfl, intact⟩, hc⟩
    · rintro ⟨_, ⟨rfl, intact⟩, hc⟩
      exact (law x).mpr ⟨intact, hc⟩

theorem clearSolution (live : Nat → Prop) :
    PowerTransmissionRule (edge live) (clearFrom live) := by
  apply equation.mpr
  intro x
  constructor
  · exact fun h => ⟨h x (Nat.le_refl _), fun j hj => h j (by omega)⟩
  · rintro ⟨hx, h⟩ j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact hx
    · exact h j hlt

/-- Nonemptiness selects a unique solution pointwise, for arbitrary sets of cuts.
    The punctured law itself always also admits the empty solution. -/
theorem classify {live active : Nat → Prop} (law : PowerTransmissionRule (edge live) active)
    (populated : ∃ z, active z) (x : Nat) : active x ↔ clearFrom live x := by
  have eqn := equation.mp law
  have upstream {n j : Nat} (h : n ≤ j) (hn : active n) : active j := by
    induction h with
    | refl => exact hn
    | step _ ih => exact ((eqn _).mp ih).2
  constructor
  · intro hx j hj
    exact ((eqn j).mp (upstream hj hx)).1
  · intro clear
    obtain ⟨z, hz⟩ := populated
    have agree {j : Nat} (hj : x ≤ j) : active x ↔ active j := by
      induction hj with
      | refl => exact Iff.rfl
      | step h ih =>
        exact ih.trans ⟨fun hy => ((eqn _).mp hy).2,
          fun hs => (eqn _).mpr ⟨clear _ h, hs⟩⟩
    exact (agree (Nat.le_max_left x z)).mpr (upstream (Nat.le_max_right x z) hz)

theorem populationCriterion (live : Nat → Prop) :
    (∃ active, PowerTransmissionRule (edge live) active ∧ ∃ z, active z) ↔
      ∃ n, clearFrom live n := by
  constructor
  · rintro ⟨active, law, z, hz⟩
    exact ⟨z, (classify law ⟨z, hz⟩ z).mp hz⟩
  · exact fun h => ⟨clearFrom live, clearSolution live, h⟩

theorem oneCut (k x : Nat) : clearFrom (fun j => j ≠ k) x ↔ k < x := by
  constructor
  · intro h
    by_contra! hx
    exact h k hx rfl
  · intro h j hj
    omega

/-- Close all incoming links from k upwards. A relay-only chain must be empty;
    an independently active node at k would sustain the entire lower segment.
    This second rule specifies only an input relative to the interrupted links. -/
theorem sourceContrast (k : Nat) :
    (∀ active, PowerTransmissionRule (edge (fun j => j < k)) active → ∀ z, ¬ active z) ∧
      (∀ x : Nat, x ≤ k ↔ x = k ∨ (x < k ∧ x + 1 ≤ k)) := by
  constructor
  · intro active law z hz
    have clear := (classify law ⟨z, hz⟩ z).mp hz
    have bad := clear (max z k) (Nat.le_max_left z k)
    exact (Nat.not_lt.mpr (Nat.le_max_right z k)) bad
  · intro x
    omega

/-- Use both actuality guards on the existing state-indexed De ente profile.
    A live state always has a distinct actual supplier. -/
theorem localGiver {live active : Nat → Prop} (law : PowerTransmissionRule (edge live) active)
    {x : Nat} (hx : active x) : live x ∧ ActualEsseCause (tailAtState active) (x + 1) x := by
  have next := (equation.mp law x).mp hx
  exact ⟨next.1, Nat.succ_ne_self _, next.2, hx, rfl⟩

/-- The relay equations do not constrain the q44 OwnBeing interpretation. -/
theorem noOwnAssignment {active : Nat → Prop} (populated : ∃ z, active z) :
    ¬ ParticipatedHasEssentialSource (tailAtState active) active (fun _ => False) := by
  rintro supply
  obtain ⟨z, hz⟩ := populated
  obtain ⟨_, _, _, own, _⟩ := supply z hz
  exact own

end InterruptedTransmission
