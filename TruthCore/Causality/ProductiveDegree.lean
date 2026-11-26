module

public import Mathlib.Tactic.Linarith
public import TruthCore.Greek.Aristotle.Metaphysics

/-! Degree comparisons under gearing, dilution and restricted response. -/

@[expose] public section

namespace TruthCore.Causality.ProductiveDegree

open TruthCore.Greek.Aristotle.Metaphysics

-- d and r are positive unsigned speeds. m and n are the tooth counts.
theorem gear (m n d r : ℚ) (hm : 0 < m) (hr : 0 < r)
    (mesh : m * d = n * r) : r < d ↔ m < n := by
  constructor
  · intro h
    by_contra! hn
    nlinarith [mul_pos hm (sub_pos.mpr h), mul_nonneg (sub_nonneg.mpr hn) hr.le]
  · intro h
    by_contra! hd
    nlinarith [mul_pos (sub_pos.mpr h) hr, mul_nonneg hm.le (sub_nonneg.mpr hd)]

-- Steady balance for positive donor flow p, clear diluent flow q, donor
-- concentration d and outlet concentration r in a well-mixed tank.
theorem dilution (p q d r : ℚ) (hp : 0 < p) (hq : 0 ≤ q) (hr : 0 < r)
    (balance : (p + q) * r = p * d) : r < d ↔ 0 < q := by
  constructor
  · intro h
    by_contra! hz
    have z : q = 0 := le_antisymm hz hq
    subst q
    nlinarith [mul_pos hp (sub_pos.mpr h)]
  · intro h
    by_contra! hd
    nlinarith [mul_pos h hr, mul_nonneg hp.le (sub_nonneg.mpr hd)]

-- Sole feed into a well-mixed tank; replacing its solute by clear carrier
-- at the same flow gives zero outlet concentration. Both actual degrees are 1.
def outlet (donor : Nat) : Nat := donor

def soleFeed (a b : Bool) (_ : Unit) : Prop :=
  a = false ∧ b = true ∧ outlet 0 < outlet 1

def sameConcentration (_ : Bool) : Nat := 1

theorem tie : ¬ CauseOfQualityInAnotherIsMoreSuchReading soleFeed
    (fun _ a b => sameConcentration b < sameConcentration a) := by
  intro h
  exact (Nat.lt_irrefl 1) (h false true () (by decide) ⟨rfl, rfl, by decide +revert⟩)

namespace ReceptionCalibration

abbrev Command := Bool × Bool

def response (locked : Bool) (u : Command) : Command :=
  (u.1, if locked then false else u.2)

def reachable (locked : Bool) (v : Command) := ∃ u, response locked u = v

def keepsHeading (locked : Bool) := ∀ u : Command, (response locked u).2 = false

theorem actualTie : response true (true, false) = response false (true, false) := rfl

theorem restrictedRange :
    (∀ v, reachable true v → reachable false v) ∧
    (reachable false (false, true) ∧ ¬ reachable true (false, true)) := by
  refine ⟨?_, ⟨⟨(false, true), rfl⟩, ?_⟩⟩
  · intro v _
    exact ⟨v, rfl⟩
  · rintro ⟨u, h⟩
    exact Bool.noConfusion (congrArg Prod.snd h)

theorem headingContrast : keepsHeading true ∧ ¬ keepsHeading false := by
  exact ⟨fun _ => rfl, fun h => Bool.noConfusion (h (false, true))⟩

theorem profileTie {Bearer Profile : Type} (positive : Bearer → Profile)
    (above : Profile → Profile → Prop) (strict : ∀ p, ¬ above p p)
    {c x : Bearer} (equalContent : positive c = positive x) :
    ¬ above (positive c) (positive x) := by
  rw [equalContent]
  exact strict _

end ReceptionCalibration

end TruthCore.Causality.ProductiveDegree
