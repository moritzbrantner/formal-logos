module

public import TruthCore.Causality.OccamRegress
import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace TruthCore.Results.Causality.OccamRegress

open TruthCore.Causality.OccamRegress

private theorem commonLikelihoodCalculation {finite infinite likelihood : ℝ}
    (hfinite : 0 < finite) (hinfinite : 0 < infinite) (hlikelihood : 0 < likelihood) :
    0 < posteriorWeight finite infinite likelihood ∧
    0 < posteriorWeight infinite finite likelihood ∧
    posteriorWeight finite infinite likelihood / posteriorWeight infinite finite likelihood =
      finite / infinite := by
  have hf := mul_pos hfinite hlikelihood
  have hi := mul_pos hinfinite hlikelihood
  have hsum := add_pos hf hi
  unfold posteriorWeight
  rw [add_comm (infinite * likelihood) (finite * likelihood)]
  refine ⟨div_pos hf hsum, div_pos hi hsum, ?_⟩
  field_simp [ne_of_gt hsum, ne_of_gt hinfinite, ne_of_gt hlikelihood]

theorem equalLikelihoodOdds : EqualLikelihoodOdds := by
  refine ⟨fun _ _ _ => commonLikelihoodCalculation, ?_⟩
  intro odds likelihood hodds hlikelihood
  have hdenom : 0 < odds + 1 := add_pos hodds zero_lt_one
  have hfinite := div_pos hodds hdenom
  have hinfinite := div_pos zero_lt_one hdenom
  refine ⟨odds / (odds + 1), 1 / (odds + 1), hfinite, hinfinite, ?_, ?_⟩
  · rw [← add_div, div_self (ne_of_gt hdenom)]
  · rw [(commonLikelihoodCalculation hfinite hinfinite hlikelihood).2.2]
    field_simp [ne_of_gt hdenom]

theorem unboundedPreference : UnboundedPreference := by
  intro finite infinite hfinite hinfinite
  constructor
  · intro hpreference
    by_contra hne
    have hi := lt_of_le_of_ne hinfinite (Ne.symm hne)
    have hratio : 0 < finite / infinite := div_pos hfinite hi
    have h := hpreference (finite / infinite + 1) (add_pos hratio zero_lt_one)
    exact (not_le_of_gt (lt_add_of_pos_right _ zero_lt_one)) ((le_div_iff₀ hi).2 h)
  · rintro rfl factor _
    simpa using le_of_lt hfinite

theorem uniformPrefixDiscount : UniformPrefixDiscount := by
  intro weight q prefixWeight hweight hq hq1 hinitial hstep hcontained
  have hbound (n : ℕ) : prefixWeight n ≤ q ^ n := by
    induction n with
    | zero => simpa using hinitial
    | succ n ih =>
      calc
        prefixWeight (n + 1) ≤ q * prefixWeight n := hstep n
        _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) := (pow_succ' q n).symm
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have hzero := ge_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n => (hcontained n).trans (hbound n)))
  exact le_antisymm hzero hweight

theorem sharedLawCharge : SharedLawCharge := by
  intro charge hpos hcharge
  refine ⟨fun n => if n = 0 then 1 else charge, by simp, by simp, fun n => by simp, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simpa using hcharge
    | succ n => simp
  · rintro ⟨q, hq, hstep⟩
    have hnext : charge ≤ q * charge := by simpa using hstep 1
    exact (not_le_of_gt (mul_lt_of_lt_one_left hpos hq)) (by simpa [mul_comm] using hnext)

end TruthCore.Results.Causality.OccamRegress
