module
public import TruthCore.Causality.PostCutStore

@[expose] public section
namespace TruthCore.Results.Causality.PostCutStore

open TruthCore.Causality.ProductiveStore
open TruthCore.Causality.PostCutStore
open scoped BigOperators

private theorem prefixCandidateBound (budget : TemporalBudget)
    {N n : ℕ} {cap : ℝ} {lower upper stock output other candidate : ℕ → ℝ}
    (ledger : ObservationLedger N cap lower upper stock output other candidate)
    (hn : n ≤ N) : prefixSum lower n ≤ cap + prefixSum upper n + prefixSum candidate n := by
  obtain ⟨initial, stockNonnegative, intervals⟩ := ledger
  -- Extend the finite ledger by freezing the last stock and turning off all flows.
  let paddedStock (t : ℕ) := stock (min t N)
  let paddedInput (t : ℕ) := if t < N then other t + candidate t else 0
  let paddedOutput (t : ℕ) := if t < N then output t else 0
  have paddedNonnegative (t : ℕ) : 0 ≤ paddedStock t :=
    stockNonnegative _ (min_le_right _ _)
  have paddedBalance (t : ℕ) :
      paddedStock (t + 1) + paddedOutput t = paddedStock t + paddedInput t := by
    by_cases ht : t < N
    · obtain ⟨_, _, _, _, _, balance⟩ := intervals t ht
      simpa [paddedStock, paddedInput, paddedOutput, ht,
        min_eq_left (Nat.succ_le_of_lt ht), min_eq_left (Nat.le_of_lt ht)] using balance
    · have hNt := Nat.le_of_not_gt ht
      simp [paddedStock, paddedInput, paddedOutput, ht,
        min_eq_right hNt, min_eq_right (Nat.le_succ_of_le hNt)]
  have outputSum : prefixSum paddedOutput n = prefixSum output n := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [paddedOutput, Nat.lt_of_lt_of_le (Finset.mem_range.mp ht) hn]
  have inputSum : prefixSum paddedInput n = prefixSum other n + prefixSum candidate n := by
    rw [prefixSum, prefixSum, prefixSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    simp [paddedInput, Nat.lt_of_lt_of_le (Finset.mem_range.mp ht) hn]
  have total := budget paddedStock paddedInput paddedOutput paddedNonnegative paddedBalance n
  change prefixSum paddedOutput n ≤ paddedStock 0 + prefixSum paddedInput n at total
  rw [outputSum, inputSum] at total
  simp [paddedStock] at total
  have lowerSum : prefixSum lower n ≤ prefixSum output n := by
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨_, _, _, lowerBound, _, _⟩ :=
      intervals t (Nat.lt_of_lt_of_le (Finset.mem_range.mp ht) hn)
    exact lowerBound
  have upperSum : prefixSum other n ≤ prefixSum upper n := by
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨_, _, _, _, upperBound, _⟩ :=
      intervals t (Nat.lt_of_lt_of_le (Finset.mem_range.mp ht) hn)
    exact upperBound
  linarith

theorem zeroCandidateCriterion (budget : TemporalBudget) : ZeroCandidateCriterion := by
  intro N cap lower upper _capNonnegative lowerNonnegative upperNonnegative
  constructor
  · rintro ⟨stock, output, other, ledger⟩ n hn
    simpa [prefixSum] using prefixCandidateBound budget ledger hn
  · intro prefixes
    let stock (t : ℕ) := cap + prefixSum upper t - prefixSum lower t
    refine ⟨stock, lower, upper, ?_, ?_, ?_⟩
    · simp [stock, prefixSum]
    · intro t ht
      exact sub_nonneg.mpr (prefixes t ht)
    · intro t ht
      refine ⟨lowerNonnegative t ht, upperNonnegative t ht, le_rfl, le_rfl, le_rfl, ?_⟩
      simp only [stock, prefixSum, Finset.sum_range_succ]
      ring

theorem candidateReplenishmentBound (budget : TemporalBudget) : CandidateReplenishmentBound := by
  intro N cap lower upper stock output other candidate ledger n hn
  have bound := prefixCandidateBound budget ledger hn
  constructor
  · linarith
  · intro deficit
    by_contra! nonePositive
    have sumNonpositive : prefixSum candidate n ≤ 0 :=
      Finset.sum_nonpos fun t ht => nonePositive t (Finset.mem_range.mp ht)
    linarith

end TruthCore.Results.Causality.PostCutStore
