module

public import TruthCore.Causality.FiniteReserveOdds

@[expose] public section
namespace TruthCore.Results.Causality.FiniteReserveOdds

open Filter
open scoped Topology
open TruthCore.Causality.FiniteReserveOdds
open TruthCore.Causality.OccamRegress
open TruthCore.Causality.PostCutStore

private theorem fits_iff (criterion : ZeroCandidateCriterion) (capacity periods : ℕ) :
    UnitTraceFits capacity periods ↔ periods ≤ capacity := by
  constructor
  · rintro ⟨stock, fits⟩
    have prefixes := (criterion periods capacity (fun _ => 1) (fun _ => 0)
      (by positivity) (fun _ _ => zero_le_one) (fun _ _ => le_rfl)).mp
      ⟨stock, fun _ => 1, fun _ => 0, fits⟩
    have final : (periods : ℝ) ≤ capacity := by
      simpa [prefixSum] using prefixes periods le_rfl
    exact_mod_cast final
  · intro enough
    refine ⟨fun t => (capacity : ℝ) - t, by simp, ?_, ?_⟩
    · intro t within
      exact sub_nonneg.mpr (by exact_mod_cast within.trans enough)
    · intro t _
      refine ⟨zero_le_one, le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
      simp [Nat.cast_succ]
      ring

private theorem likelihood_eq_tail (criterion : ZeroCandidateCriterion)
    {prior : ℕ → ℝ} (nonnegative : ∀ capacity, 0 ≤ prior capacity)
    (proper : HasSum prior 1) (periods : ℕ) :
    reserveLikelihood prior periods = ∑' i : ℕ, prior (i + periods) := by
  classical
  let survives (capacity : ℕ) := if periods ≤ capacity then prior capacity else 0
  have summable : Summable survives :=
    .of_nonneg_of_le
      (fun capacity => by
        unfold survives
        split_ifs <;> first | exact nonnegative capacity | exact le_rfl)
      (fun capacity => by
        unfold survives
        split_ifs <;> first | exact nonnegative capacity | exact le_rfl)
      proper.summable
  have finiteZero : ∑ capacity ∈ Finset.range periods, survives capacity = 0 :=
    Finset.sum_eq_zero fun i below => by
      simp [survives, Nat.not_le_of_lt (Finset.mem_range.mp below)]
  have shift : (fun i : ℕ => survives (i + periods)) = fun i => prior (i + periods) := by
    funext i
    simp [survives]
  change (∑' capacity : ℕ, if UnitTraceFits capacity periods then prior capacity else 0) = _
  simp only [fits_iff criterion]
  simpa only [finiteZero, zero_add, shift] using
    (summable.sum_add_tsum_nat_add periods).symm

private theorem tail_eq_complement {prior : ℕ → ℝ} (proper : HasSum prior 1)
    (periods : ℕ) : (∑' i : ℕ, prior (i + periods)) = 1 - prefixSum prior periods := by
  have partition := proper.summable.sum_add_tsum_nat_add periods
  rw [proper.tsum_eq] at partition
  exact eq_sub_of_add_eq (by simpa [prefixSum, add_comm] using partition)

private theorem geometric_is_proper : HasSum geometricPrior 1 := by
  change HasSum (fun capacity : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ capacity) 1
  convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2 : ℝ) using 1
  norm_num

private theorem geometric_is_positive (capacity : ℕ) : 0 < geometricPrior capacity := by
  unfold geometricPrior
  positivity

private theorem geometric_tail (periods : ℕ) :
    (∑' i : ℕ, geometricPrior (i + periods)) = (1 / 2 : ℝ) ^ periods := by
  calc
    (∑' i : ℕ, geometricPrior (i + periods)) =
        ∑' i : ℕ, (1 / 2 : ℝ) ^ periods * geometricPrior i := by
      apply tsum_congr
      intro i
      simp only [geometricPrior, pow_add]
      ring
    _ = (1 / 2 : ℝ) ^ periods := by rw [tsum_mul_left, geometric_is_proper.tsum_eq, mul_one]

theorem finiteReserveComparison
    (criterion : ZeroCandidateCriterion) (comparison : UnboundedPreference) :
    FiniteReserveComparison := by
  refine ⟨fits_iff criterion, ?_, geometric_is_proper, geometric_is_positive, ?_⟩
  · intro prior nonnegative proper
    have likelihood (periods : ℕ) : reserveLikelihood prior periods = 1 - prefixSum prior periods :=
      (likelihood_eq_tail criterion nonnegative proper periods).trans
        (tail_eq_complement proper periods)
    refine ⟨likelihood, ?_⟩
    intro storedPrior suppliedPrior lower storedLikelihood suppliedLikelihood storedPos suppliedPos
      lowerPos storedBound suppliedBound factor factorPos
    have tailLimit : Tendsto (reserveLikelihood prior) atTop (𝓝 0) := by
      have same : reserveLikelihood prior = fun n => 1 - prefixSum prior n := funext likelihood
      rw [same]
      simpa only [prefixSum, sub_self] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub proper.tendsto_sum_nat
    have storedLimit :
        Tendsto (fun n => factor * (storedPrior * reserveLikelihood prior n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tailLimit.const_mul storedPrior).const_mul factor
    have eventuallyBelow := storedLimit.eventually_lt_const (mul_pos suppliedPos lowerPos)
    obtain ⟨start, below⟩ := Filter.eventually_atTop.mp eventuallyBelow
    refine ⟨start, fun n hn => ?_⟩
    have storedLe := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (storedBound n).2 storedPos.le) factorPos.le
    exact (storedLe.trans_lt (below n hn)).trans_le
      (mul_le_mul_of_nonneg_left (suppliedBound n).1 suppliedPos.le)
  · intro periods
    have likelihood : reserveLikelihood geometricPrior periods = (1 / 2 : ℝ) ^ periods :=
      (likelihood_eq_tail criterion (fun m => (geometric_is_positive m).le)
        geometric_is_proper periods).trans (geometric_tail periods)
    have likelihoodPos : 0 < reserveLikelihood geometricPrior periods := by
      rw [likelihood]
      positivity
    refine ⟨likelihood, likelihoodPos, ?_⟩
    intro storedPrior suppliedWeight storedPos suppliedPos
    have storedWeightPos := mul_pos storedPos likelihoodPos
    exact fun h => storedWeightPos.ne' ((comparison _ _ suppliedPos storedWeightPos.le).mp h)

end TruthCore.Results.Causality.FiniteReserveOdds
