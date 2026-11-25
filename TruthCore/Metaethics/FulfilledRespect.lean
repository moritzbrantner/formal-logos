module

public import TruthCore.Metaethics.GoodnessFormEnd

/-! Actuality, due status and the choice of a positive goodness threshold. -/

@[expose] public section

namespace TruthCore.Metaethics.FulfilledRespect

open TruthCore.Latin.Aquinas.SummaTheologiae

-- One existing bearer and one respect, evaluated in two conditions.
def attained (s : Bool) (_ _ : Unit) : Prop := s = true

def mark (s : Bool) : Nat := if s then 1 else 0

-- Ordered marks for deficiency (0), neutrality (1), and excellence (2).
def good (score : Bool → Nat) (s : Bool) (_ _ : Unit) : Prop := 1 < score s

theorem sameComparisons (s t : Bool) :
    (mark s < mark t) ↔ (mark s + 1 < mark t + 1) := by
  cases s <;> cases t <;> decide

theorem differentVerdicts :
    (∀ s, GoodnessIsActualityReading (good (fun t => mark t + 1) s) (attained s)) ∧
    ¬ GoodnessIsActualityReading (good mark true) (attained true) := by
  constructor
  · intro s x p
    cases s <;> unfold good attained mark <;> decide
  · intro h
    have bad := (h () ()).mpr rfl
    exact (Nat.lt_irrefl 1) bad

open TruthCore.Metaethics.GoodnessFormEnd

/-- The substantial actuality of this bearer reduces goodness to due status. -/
theorem goodIffDueAtSubstantial (f : Frame) (h : DueActualityThesis f)
    (n : f.Being) (ha : f.Has n f.substantial) :
    f.GoodIn n f.substantial ↔ Due f n f.substantial :=
  ⟨fun good => ((h n f.substantial).mp good).1,
   fun due => (h n f.substantial).mpr ⟨due, ha⟩⟩

/-- This consequence ranges over actual bearers at the one substantial respect. -/
theorem substantialGoodnessIffDue (f : Frame) (h : DueActualityThesis f) :
    (∀ x, f.Has x f.substantial → f.GoodIn x f.substantial) ↔
      (∀ x, f.Has x f.substantial → Due f x f.substantial) :=
  ⟨fun hg x ha => (goodIffDueAtSubstantial f h x ha).mp (hg x ha),
   fun hd x ha => (goodIffDueAtSubstantial f h x ha).mpr (hd x ha)⟩

end TruthCore.Metaethics.FulfilledRespect
