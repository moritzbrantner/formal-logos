module

public import TruthCore.Causality.ComparativeFoundation
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Order.Basic

@[expose] public section
namespace TruthCore.Results.Causality.ComparativeFoundation
open TruthCore.Causality.ComparativeFoundation

private theorem belowIff (p : Pair) (k : Int) : p.below k ↔ k < p.right - p.left := by
  unfold Pair.below
  rw [Int.add_comm]
  exact Int.lt_sub_right_iff_add_lt.symm

theorem thresholds : ThresholdCharacterization := by
  intro w
  refine ⟨?_, ?_⟩
  · intro k
    simp only [belowIff, Int.not_lt, and_comm, iff_self, and_self]
  · have gap : w.actual.right - w.actual.left =
        (w.residual.right - w.residual.left) + (w.rightInput - w.leftInput) := by
      unfold Run.actual
      dsimp
      simp only [Int.sub_eq_add_neg, Int.neg_add]
      ac_rfl
    constructor
    · intro same
      have bound (k : Int) := (belowIff w.residual k).symm.trans ((same k).trans (belowIff w.actual k))
      have eq : w.residual.right - w.residual.left = w.actual.right - w.actual.left :=
        eq_of_forall_lt_iff bound
      have zero : w.rightInput - w.leftInput = 0 :=
        Int.add_left_cancel (show (w.residual.right - w.residual.left) + (w.rightInput - w.leftInput) =
          (w.residual.right - w.residual.left) + 0 by rw [← gap, ← eq, Int.add_zero])
      exact (Int.sub_eq_zero.mp zero).symm
    · intro equal k
      rw [belowIff, belowIff, gap, equal, Int.sub_self, Int.add_zero]

open Rods
open TruthCore.Case.Catholicism (TransferRole UniversalCauseTransfersPerfections)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)

private instance (p : Pair) (k : Int) : Decidable (p.below k) :=
  inferInstanceAs (Decidable (p.left + k < p.right))

private theorem universalSource (d : TransferRole) :
    CausesAllInGenus (inAct d) (diagnostic d) .esse .source := by
  intro x distinct _
  exact ⟨rfl, distinct⟩

theorem controls (sensitivity : ThresholdCharacterization) : Rods.Controls := by
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro d
    refine ⟨universalSource d, ?_⟩
    cases d <;> simp only [after, before, diagnostic, inAct, Pair.below] <;> decide
  · intro a _ x r _ atEsse actual
    obtain ⟨rfl, _⟩ := atEsse
    cases r with
    | esse => exact ⟨rfl, by assumption⟩
    | shorterThanExtending => exact ⟨actual, by decide⟩
    | longerThanFixed => exact ⟨actual, by decide⟩
  · intro h
    have edge := h .source (universalSource _) .recipient .shorterThanExtending
      (by decide) ⟨rfl, by decide⟩ ⟨rfl, by decide⟩
    exact edge.2 (by decide)
  · exact fun edge => edge.2 (by decide)
  · exact ⟨by decide, by decide, ((sensitivity common).2).mpr rfl⟩

end TruthCore.Results.Causality.ComparativeFoundation
