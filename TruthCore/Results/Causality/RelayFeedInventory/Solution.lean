module

public import TruthCore.Causality.RelayFeedInventory

@[expose] public section

namespace TruthCore.Results.Causality.RelayFeedInventory

open TruthCore.Causality.RelayCutSensitivity
open TruthCore.Causality.RelayFeedInventory
open TruthCore.Logic.RegressHeadcount (RegressHeadcountCriterion)

private theorem reachableResponse (feeds : ℕ → Prop) :
    CutResponses feeds (fun i n => ∃ d, n ≤ d ∧ (d ≤ i ∨ i < n) ∧ feeds d) := by
  intro i n
  constructor
  · rintro ⟨d, downstream, path, feed⟩
    rcases Nat.eq_or_lt_of_le downstream with rfl | upstream
    · exact Or.inl feed
    · have intact : n ≠ i := by
        rcases path with within | beyond
        · exact Nat.ne_of_lt (upstream.trans_le within)
        · exact Nat.ne_of_gt beyond
      exact Or.inr ⟨intact, d, Nat.succ_le_of_lt upstream,
        path.imp_right Nat.lt_succ_of_lt, feed⟩
  · rintro (here | ⟨intact, d, upstream, path, feed⟩)
    · exact ⟨n, le_rfl, (Nat.lt_or_ge i n).symm, here⟩
    · have noCut : i < n + 1 → i < n :=
        fun next => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ next) intact.symm
      exact ⟨d, (Nat.le_succ n).trans upstream, path.imp_right noCut, feed⟩

private theorem prefixActivity {feeds active : ℕ → Prop} {i : ℕ}
    (valid : RelayActivity (singleCut i) feeds active) :
    ∀ n ≤ i, active n ↔ ∃ d, n ≤ d ∧ d ≤ i ∧ feeds d := by
  intro n within
  refine Nat.decreasingInduction (motive := fun k _ =>
    active k ↔ ∃ d, k ≤ d ∧ d ≤ i ∧ feeds d) ?_ ?_ within
  · intro k below next
    have intact : singleCut i k := Nat.ne_of_lt (Nat.lt_of_succ_le below)
    refine (valid k).trans ⟨?_, ?_⟩
    · rintro (feed | ⟨_, supplierOn⟩)
      · exact ⟨k, le_rfl, (Nat.le_succ k).trans below, feed⟩
      · obtain ⟨d, downstream, bounded, feed⟩ := next.mp supplierOn
        exact ⟨d, (Nat.le_succ k).trans downstream, bounded, feed⟩
    · rintro ⟨d, downstream, bounded, feed⟩
      rcases Nat.eq_or_lt_of_le downstream with rfl | upstream
      · exact Or.inl feed
      · exact Or.inr ⟨intact, next.mpr ⟨d, Nat.succ_le_of_lt upstream, bounded, feed⟩⟩
  · refine (valid i).trans ⟨?_, ?_⟩
    · rintro (feed | ⟨intact, _⟩)
      · exact ⟨i, le_rfl, le_rfl, feed⟩
      · exact False.elim (intact rfl)
    · rintro ⟨d, lower, upper, feed⟩
      have equal := Nat.le_antisymm lower upper
      exact Or.inl (equal ▸ feed)

private theorem countStep (feeds : ℕ → Prop) (i : ℕ) :
    unitFeedCount feeds (i + 1) = unitFeedCount feeds i +
      @ite ℕ (feeds i) (Classical.propDecidable _) 1 0 := rfl

private theorem countBefore (feeds : ℕ → Prop) (length : ℕ)
    (absent : ∀ i < length, ¬ feeds i) : unitFeedCount feeds length = 0 := by
  induction length with
  | zero => rfl
  | succ length ih =>
    rw [countStep, ite_eq_right (absent length (Nat.lt_succ_self length)), Nat.add_zero]
    exact ih fun i below => absent i (Nat.lt_trans below (Nat.lt_succ_self length))

theorem feedInventoryComparison (singleCutResult : SingleCutComparison)
    (headcount : RegressHeadcountCriterion) : FeedInventoryComparison := by
  have bottom feeds response (valid : CutResponses feeds response) i :
      response i 0 ↔ ∃ d ≤ i, feeds d :=
    (prefixActivity (valid i) 0 (Nat.zero_le i)).trans
      ⟨fun ⟨d, _, bounded, feed⟩ => ⟨d, bounded, feed⟩,
        fun ⟨d, bounded, feed⟩ => ⟨d, Nat.zero_le d, bounded, feed⟩⟩
  refine ⟨?_, bottom, ?_, ?_, ?_⟩
  · intro feeds
    exact ⟨fun _ => ⟨fun _ => Or.inr ⟨trivial, trivial⟩, fun _ => trivial⟩,
      ⟨_, reachableResponse feeds⟩⟩
  · intro d
    refine ⟨?_, (headcount.1 _ _).mpr ⟨?_, ?_⟩⟩
    · intro single many singleValid manyValid i
      have only := singleCutResult.2.2.2.2.1 d single singleValid i
      have someFeed : (∃ source ≤ i, d ≤ source) ↔ d ≤ i :=
        ⟨fun ⟨source, bounded, feed⟩ => feed.trans bounded,
          fun bounded => ⟨d, bounded, le_rfl⟩⟩
      exact only.trans ((bottom (d ≤ ·) many manyValid i).trans someFeed).symm
    · let oneCharge : {n : ℕ // n = d} → Unit := fun _ => ()
      exact Finite.of_injective oneCharge (fun a b _ => Subtype.ext (a.2.trans b.2.symm))
    · let tailCharge (n : ℕ) : {position : ℕ // d ≤ position} :=
        ⟨d + n, Nat.le_add_right d n⟩
      exact Infinite.of_injective tailCharge (fun _ _ equal =>
        Nat.add_left_cancel (congrArg Subtype.val equal))
  · intro feeds i
    rw [countStep, Nat.add_left_cancel_iff]
    constructor
    · intro count
      by_contra absent
      rw [ite_eq_right absent] at count
      exact Nat.zero_ne_one count
    · exact fun feed => ite_eq_left feed
  · intro d
    have noSingle := countBefore (· = d) d (fun i below => Nat.ne_of_lt below)
    have noTail := countBefore (d ≤ ·) d (fun i below => Nat.not_le_of_gt below)
    refine ⟨?_, ?_⟩
    · rw [countStep, ite_eq_right (Nat.ne_of_gt (Nat.lt_succ_self d)), Nat.add_zero,
        countStep, ite_eq_left (Eq.refl d), noSingle]
    · rw [countStep, ite_eq_left (Nat.le_succ d), countStep, ite_eq_left (Nat.le_refl d), noTail]

end TruthCore.Results.Causality.RelayFeedInventory
