module

public import TruthCore.Causality.ReceiptAllocation

@[expose] public section
namespace TruthCore.Results.Causality.ReceiptAllocation
open TruthCore.Causality.ReceiptAllocation
open TruthCore.Causality.ExerciseContribution (Step)

private theorem stepIff {w : Window} {r : Allocation} (h : w.fits r) :
    Step (exercise w r) .receipt .work ↔ 0 < r.namedWork := by
  obtain ⟨h₁, _, h₂, _⟩ := h
  constructor
  · rintro ⟨_, _, _, _, _, hp⟩
    exact hp
  · intro hp
    have work := Nat.lt_of_lt_of_le hp (Nat.le.intro h₂)
    have received := Nat.lt_of_lt_of_le hp (Nat.le.intro h₁)
    exact ⟨received, work, (), ⟨work, work⟩, rfl, hp⟩

private theorem rangeAt {w : Window} (h : w.balanced) (n : Nat) :
    (∃ r, w.fits r ∧ r.namedWork = n) ↔
      w.work - (w.opening + w.other) ≤ n ∧ n ≤ min w.work w.receipt := by
  constructor
  · rintro ⟨r, ⟨h₁, h₂, h₃, _⟩, rfl⟩
    refine ⟨Nat.sub_le_iff_le_add.mpr ?_, Nat.le_min.mpr ⟨Nat.le.intro h₃, Nat.le.intro h₁⟩⟩
    rw [← h₃, ← h₂]
    exact Nat.add_le_add_left (Nat.le_add_right ..) _
  · rintro ⟨lower, upper⟩
    obtain ⟨hw, hi⟩ := Nat.le_min.mp upper
    obtain ⟨pooled, toWork⟩ := Nat.le.dest hw
    obtain ⟨held, fromInlet⟩ := Nat.le.dest hi
    have hcap := Nat.sub_le_iff_le_add.mp lower
    rw [← toWork] at hcap
    obtain ⟨stored, fromPool⟩ := Nat.le.dest (Nat.le_of_add_le_add_left hcap)
    refine ⟨⟨n, held, pooled, stored⟩, ⟨fromInlet, fromPool, toWork, ?_⟩, rfl⟩
    change held + stored = w.closing
    apply Nat.add_left_cancel (n := w.work)
    calc
      w.work + (held + stored) = (n + held) + (pooled + stored) := by rw [← toWork]; ac_rfl
      _ = w.opening + w.receipt + w.other := by rw [fromInlet, fromPool]; ac_rfl
      _ = w.work + w.closing := h

theorem sharpRange : RangeCertificate := by
  intro w hb
  refine ⟨rangeAt hb, ?_⟩
  constructor
  · intro all
    rcases Nat.lt_or_ge (w.opening + w.other) w.work with deficit | covered
    · exact deficit
    · have zeroShare : w.work - (w.opening + w.other) ≤ 0 := by
        rw [Nat.sub_eq_zero_of_le covered]
      obtain ⟨r, hr, hzero⟩ := (rangeAt hb 0).mpr ⟨zeroShare, Nat.zero_le _⟩
      exact (Nat.ne_of_gt ((stepIff hr).mp (all r hr)) hzero).elim
  · intro deficit r hr
    have lower := ((rangeAt hb r.namedWork).mp ⟨r, hr, rfl⟩).1
    exact (stepIff hr).mpr (Nat.lt_of_lt_of_le (Nat.sub_pos_of_lt deficit) lower)

theorem controls (bounds : RangeCertificate) : Controls := by
  constructor
  · let use : Allocation := ⟨1, 0, 0, 1⟩
    let store : Allocation := ⟨0, 1, 1, 0⟩
    refine ⟨rfl, use, store, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact (stepIff ⟨rfl, rfl, rfl, rfl⟩).mpr (by decide : 0 < use.namedWork)
    · intro edge
      have := (stepIff ⟨rfl, rfl, rfl, rfl⟩).mp edge
      exact (by decide : ¬ 0 < store.namedWork) this
  · let w : Window := ⟨1, 1, 0, 2, 0⟩
    refine ⟨rfl, ⟨⟨1, 0, 1, 0⟩, rfl, rfl, rfl, rfl⟩, ?_⟩
    intro r hr
    have edge := ((bounds w rfl).2.mpr (by decide)) r hr
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
    dsimp at h₁ h₂ h₃ h₄
    obtain ⟨noNamed, noPool⟩ := Nat.eq_zero_of_add_eq_zero h₄
    rw [noNamed, Nat.add_zero] at h₁
    rw [noPool, Nat.add_zero] at h₂
    refine ⟨edge, ⟨1, 0, 0, 1⟩, ⟨0, 1, 1, 0⟩, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp only [Allocation.accounts, h₁, h₂] <;> decide

end TruthCore.Results.Causality.ReceiptAllocation
