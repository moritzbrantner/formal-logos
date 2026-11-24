module

public import TruthCore.Explanation.PairedInterventions

@[expose] public section

namespace TruthCore.Results.Explanation.PairedInterventions
open TruthCore.Explanation.PairedInterventions
open TruthCore.Logic.AtomismIndependence (Triple Index coordinate Parity)

private theorem edgeParity (s : Triple) (left right : Bool) :
    Parity s ↔ Parity (paired s left right) := by
  rcases s with ⟨a, b, c⟩
  unfold Parity
  decide +revert

private theorem parityClass (s t : Triple) :
    Reachable s t ↔ (Parity s ↔ Parity t) := by
  constructor
  · intro h
    induction h with
    | stay => exact Iff.rfl
    | step _ left right ih => exact ih.trans (edgeParity _ left right)
  · rcases s with ⟨a, b, c⟩
    rcases t with ⟨x, y, z⟩
    intro same
    -- Setting each outer coordinate fixes its incident edge input. Parity
    -- ensures that these same two choices also set the middle coordinate.
    have hits : paired (a, b, c) (a.xor x) (c.xor z) = (x, y, z) := by
      unfold Parity at same
      decide +revert
    exact hits ▸ Reachable.step Reachable.stay (a.xor x) (c.xor z)

private theorem pairInputs (i j : Index) :
    ∀ a b c x y : Bool, i ≠ j → ∃ left right : Bool,
      coordinate (paired (a, b, c) left right) i = x ∧
      coordinate (paired (a, b, c) left right) j = y := by
  cases i <;> cases j <;> decide

theorem inputRange : InputRange := by
  refine ⟨parityClass, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩ i j distinct x y
    obtain ⟨left, right, hx, hy⟩ := pairInputs i j a b c x y distinct
    exact ⟨_, Reachable.step Reachable.stay left right, hx, hy⟩
  · rintro ⟨a, b, c⟩ reachable
    have flipped : ¬ (Parity (a, b, c) ↔ Parity (endpoint (a, b, c) true)) := by
      clear reachable
      unfold Parity
      decide +revert
    exact flipped ((parityClass _ _).mp reachable)
  · rintro ⟨a, b, c⟩ ⟨x, y, z⟩
    -- Toggle the endpoint just when the total parity must change.
    let single := ((a.xor b).xor c).xor ((x.xor y).xor z)
    refine ⟨single, (parityClass _ _).mpr ?_⟩
    dsimp [single, Parity, endpoint]
    decide +revert

theorem offsetAccuracy : OffsetAccuracy := by
  unfold OffsetAccuracy
  decide

end TruthCore.Results.Explanation.PairedInterventions
