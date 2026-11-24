module

public import TruthCore.Explanation.PopulationEntry

@[expose] public section
namespace TruthCore.Results.Explanation.PopulationEntry
open TruthCore.Explanation.PopulationEntry
open TruthCore.Modern.Hume.Induction (Trace)
open TruthCore.Modal.TemporalHistory (BeginsAt)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Explanation.ExistencePSR (Sound)

private theorem population_step (w : Trace) (t : Nat) :
    population w (t+1) = population w t + (w (t+1)).toNat := by
  unfold population
  rw [Finset.range_add_one, Finset.filter_insert]
  cases he : w (t+1) <;> simp [he]

private theorem conserved_iff (w : Trace) :
    admits .conserved w ↔ ∀ t, w (t+1) = false := by
  constructor
  · intro h t
    have he := h t
    rw [population_step] at he
    cases hw : w (t+1) <;> simp_all
  · intro h t
    simp [population_step, h t]

private theorem solitary_capacity (i : Nat) : admits .capacityOne (solitary i) := by
  intro t
  apply le_trans (Finset.card_le_card (s := (Finset.range (t+1)).filter
    (fun j => solitary i j = true)) (t := {i}) ?_)
  · simp
  · intro j hj
    simpa [solitary] using (Finset.mem_filter.mp hj).2

private theorem capacity_founder (w : Trace) (hw : w 0 = true) :
    admits .capacityOne w ↔ admits .conserved w := by
  have hbase : population w 0 = 1 := by simp [population, Finset.filter_singleton, hw]
  have hpos (t : Nat) : 1 ≤ population w t := by
    induction t with
    | zero => omega
    | succ t ih => rw [population_step]; omega
  constructor
  · intro h t
    have hn := h (t+1)
    have ht := h t
    have hp := hpos t
    have hp' := hpos (t+1)
    omega
  · intro h t
    induction t with
    | zero => omega
    | succ t ih => rw [h t]; exact ih

private theorem admitted_actual (b : Boundary) : admits b actual := by
  cases b with
  | conserved => exact (conserved_iff _).mpr (by simp [actual, solitary])
  | capacityOne => exact solitary_capacity 0
  | unrestricted => trivial

private theorem admitted_empty (b : Boundary) : admits b (fun _ => false) := by
  cases b with
  | conserved => exact (conserved_iff _).mpr (fun _ => rfl)
  | capacityOne => intro t; simp [population]
  | unrestricted => trivial

private theorem no_incoming (b : Boundary) (t i : Nat) (w : Trace) :
    ¬ ∃ x, (history b t).ontic.Causes w x (.agent i) := by
  rintro ⟨_, _, _, h, _⟩
  cases h

private theorem no_reason (b : Boundary) (t i : Nat) (w : Trace) :
    ¬ ∃ r, (reasonModel b t).explains w r (.fact (.agent i)) := by
  rintro ⟨_, _, _, h, _⟩
  cases h

private theorem reason_sound (b : Boundary) (t : Nat) : Sound (reasonModel b t) := by
  rintro w x r ⟨i, _, h, hi⟩
  cases h
  exact hi

private theorem founder (b : Boundary) : FounderCase b := by
  have hc : ContingentAt (history b 1).ontic actual (.agent 0) :=
    ⟨⟨rfl, by decide⟩, fun _ => false, ⟨admitted_actual b, admitted_empty b⟩,
      fun h => Bool.noConfusion h.1⟩
  have hn := no_reason b 1 0 actual
  refine ⟨admitted_actual b, hc, fun t => no_incoming b t 0 actual, hn,
    ⟨0, rfl, rfl, rfl, rfl⟩, ⟨0, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact fun h => hn (h (.agent 0) hc)

private theorem begins (b : Boundary) (t i : Nat) {w : Trace} (hw : w i = true) :
    BeginsAt (history b t) w (.agent i) i := by
  refine ⟨⟨hw, Nat.le_refl i⟩, ?_⟩
  intro s hs h
  exact (Nat.not_le.mpr hs) h.2

private theorem no_entry (k : Nat) (b : Boundary)
    (hblock : ∀ w, admits b w → w 0 = true → w (k+1) = false) :
    ¬ AdditionalEntry b k := by
  rintro ⟨w, ha, _, _, hfounder, hnew, _⟩
  have hf := hblock w ha.2 hfounder.1
  exact Bool.noConfusion (hf.symm.trans hnew.1.1)

private theorem unrestricted_entry (k : Nat) : AdditionalEntry .unrestricted k := by
  let v : Trace := fun i => actual i || solitary (k+1) i
  have outside (i : Nat) (hi : i ≠ k+1) : v i = actual i := by
    simp [v, solitary, hi]
  have hentry : v (k+1) = true := by simp [v, solitary]
  have hbase : actual (k+1) = false := by simp [actual, solitary]
  have hp (x : Entity) (t : Nat) (ht : t ≤ k) : present v x t ↔ present actual x t := by
    cases x with
    | agent i =>
      by_cases hi : i ≤ t
      · simp [present, hi, outside i (by omega)]
      · simp [present, hi]
    | firing i =>
      by_cases hi : i + 1 = t
      · simp [present, hi, outside i (by omega)]
      · simp [present, hi]
  refine ⟨v, ⟨trivial, trivial⟩, outside, hp, ⟨by simp [v, actual, solitary], by omega⟩,
    begins _ _ _ hentry, ⟨⟨hentry, by omega⟩, actual, ⟨trivial, trivial⟩, ?_⟩,
    (fun t => no_incoming _ t _ _), no_reason _ _ _ _, ⟨k+1, rfl, rfl, hentry, rfl⟩,
    ⟨k+1, hentry, rfl⟩, ?_⟩
  · intro h
    exact Bool.noConfusion (hbase.symm.trans h.1)
  · rintro ⟨i, hi, htime⟩
    have : i = k+1 := by omega
    exact Bool.noConfusion (hbase.symm.trans (this ▸ hi))

/-- The same brute contingent founder under population conservation, a
one-agent bound, and an unrestricted boundary with a fixed detector. -/
theorem entryComparison : TruthCore.Explanation.PopulationEntry.EntryComparison := by
  refine ⟨reason_sound, founder, conserved_iff, ?_, capacity_founder, ?_, ?_⟩
  · intro w v hw hv hzero
    funext i
    cases i with
    | zero => exact hzero
    | succ t => exact ((conserved_iff w).mp hw t).trans ((conserved_iff v).mp hv t).symm
  · intro k
    exact ⟨solitary_capacity _, fun h => by simpa [solitary] using h.1,
      begins _ _ _ (by simp [solitary])⟩
  · intro k
    exact ⟨no_entry k _ (fun w h _ => (conserved_iff w).mp h k),
      no_entry k _ (fun w h hw => (conserved_iff w).mp ((capacity_founder w hw).mp h) k),
      unrestricted_entry k⟩

end TruthCore.Results.Explanation.PopulationEntry
