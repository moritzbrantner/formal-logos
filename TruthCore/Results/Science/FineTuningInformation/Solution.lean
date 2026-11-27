module

public import TruthCore.Science.FineTuningInformation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace TruthCore.Results.Science.FineTuningInformation

open MeasureTheory ProbabilityTheory
open TruthCore.Science.FineTuningInformation
open TruthCore.Science.FineTuningSelection TruthCore.Science.FineTuningEvidence
open TruthCore.Logic.FiniteInformation
open TruthCore.Logic.EpistemicAccuracy.BayesianRefinement

private theorem prior_true (p : unitInterval) :
    (modelPrior p).real {true} = (p : ℝ) := by
  unfold modelPrior
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp) (by simp)

private theorem prior_false (p : unitInterval) :
    (modelPrior p).real {false} = 1 - (p : ℝ) := by
  unfold modelPrior
  exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton _) (by simp) (by simp)

private theorem binaryInformation_eq_zero_iff (p d n : unitInterval)
    (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1) :
    mutualInformation (modelPrior p ⊗ₘ binaryKernel d n) = 0 ↔ d = n := by
  constructor
  · intro hz
    have hrows := (kernel_information_eq_zero_iff _ _).mp hz
    have ht : modelPrior p {true} ≠ 0 := by
      intro h
      exact hp.ne' (by rw [← prior_true p, measureReal_def, h, ENNReal.toReal_zero])
    have hf : modelPrior p {false} ≠ 0 := by
      intro h
      exact (sub_pos.mpr hp').ne' (by rw [← prior_false p, measureReal_def, h, ENNReal.toReal_zero])
    have hrowsEq := (hrows true ht).trans (hrows false hf).symm
    have hrates := congrArg (fun μ : Measure Bool => μ.real {true}) hrowsEq
    change (modelPrior d).real {true} = (modelPrior n).real {true} at hrates
    exact Subtype.ext (by simpa only [prior_true] using hrates)
  · rintro rfl
    have hk : binaryKernel d d = Kernel.const Bool (modelPrior d) := by
      ext m : 1
      cases m <;> rfl
    rw [mutualInformation_eq_zero_iff, hk, Measure.compProd_const, Measure.map_fst_prod,
      Measure.map_snd_prod, measure_univ, measure_univ, one_smul, one_smul]

theorem observerInformation : ObserverInformationCriterion := by
  intro p d n hp hp'
  exact (binaryInformation_eq_zero_iff p (reportRate d) (reportRate n) hp hp').trans
    ⟨fun h => Rat.cast_injective (congrArg Subtype.val h),
      fun h => Subtype.ext (by simp [reportRate, h])⟩

theorem screeningControls : ScreeningControls := by
  have hd : likelihood screenedDesign = 1 := by
    norm_num [likelihood, screenedDesign]
  have hn : likelihood screenedNatural = 1 := by
    norm_num [likelihood, screenedNatural]
  have hrd : reportRate screenedDesign = 1 := Subtype.ext (by simp [reportRate, hd])
  have hrn : reportRate screenedNatural = 1 := Subtype.ext (by simp [reportRate, hn])
  let p : unitInterval := ⟨1/3, by norm_num, by norm_num⟩
  have hp : 0 < (p : ℝ) := by norm_num [p]
  have hp' : (p : ℝ) < 1 := by norm_num [p]
  change (modelPrior p).real {true} = 1/3 ∧ (modelPrior p).real {false} = 2/3 ∧ _
  refine ⟨prior_true p, ?_, ?_, ?_, (observerInformation p _ _ hp hp').mpr (hd.trans hn.symm), ?_⟩
  · rw [prior_false]
    norm_num [p]
  · change bernoulliMeasure true false (reportRate screenedDesign) = _
    rw [hrd, bernoulliMeasure_one]
  · change bernoulliMeasure true false (reportRate screenedNatural) = _
    rw [hrn, bernoulliMeasure_one]
  · refine lt_of_le_of_ne (mutualInformation_nonneg _) (Ne.symm ?_)
    intro hz
    have he := (observerInformation p design natural hp hp').mp hz
    norm_num [likelihood, design, natural] at he

theorem accuracyAgreement (hGain : BayesianGainCertificate)
    (hInformation : ObserverInformationCriterion) : AccuracyAgreement := by
  intro p d n w u v hp hp' hw hw' hu hu' hv hv' hm hj hj'
  have h := hGain p (reportRate d) (reportRate n) w u v hp hp'
    (reportRate d).property.1 (reportRate d).property.2
    (reportRate n).property.1 (reportRate n).property.2 hw hw' hu hu' hv hv' hm hj hj'
  exact h.2.2.trans ((show ((reportRate d : ℝ) = (reportRate n : ℝ)) ↔
      likelihood d = likelihood n from Rat.cast_inj).trans
    (hInformation p d n hp hp').symm)

/-- Before selection, observerhood itself separates the same screened rows
 at any interior pre-selection model prior. -/
theorem screenedObserverhoodSeparates (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1) :
    0 < mutualInformation (modelPrior p ⊗ₘ
      binaryKernel (observerRate screenedDesign) (observerRate screenedNatural)) := by
  refine lt_of_le_of_ne (mutualInformation_nonneg _) (Ne.symm ?_)
  intro hz
  have he := (binaryInformation_eq_zero_iff _ _ _ hp hp').mp hz
  have hval := congrArg Subtype.val he
  norm_num [observerRate, screenedDesign, screenedNatural] at hval

/-- The observation collapsing the two labels loses target information when
 both labels have positive mass. Reading the label itself loses none. -/
theorem deterministicReportControl (p : unitInterval) (hp : 0 < (p : ℝ))
    (hp' : (p : ℝ) < 1) :
    conditionalEntropy (modelPrior p) id (fun _ => true) ≠ 0 ∧
      conditionalEntropy (modelPrior p) id id = 0 := by
  constructor
  · intro h
    have ht : 0 < (modelPrior p).real {true} := (prior_true p).symm ▸ hp
    have hf : 0 < (modelPrior p).real {false} := (prior_false p).symm ▸ sub_pos.mpr hp'
    exact Bool.noConfusion ((conditionalEntropy_eq_zero_iff _ _ _).mp h true false ht hf rfl)
  · exact (conditionalEntropy_eq_zero_iff _ _ _).mpr fun _ _ _ _ h => h

/-- A constant report can determine the label on support even though it
 identifies two states in the carrier. -/
theorem nullStateControl :
    conditionalEntropy (modelPrior 1) id (fun _ => true) = 0 := by
  apply (conditionalEntropy_eq_zero_iff _ _ _).mpr
  intro s t hs ht _
  have hfalse : ¬ 0 < (modelPrior 1).real {false} := by rw [prior_false]; norm_num
  cases s <;> cases t <;> first | rfl | exact (hfalse hs).elim | exact (hfalse ht).elim

namespace Plenitude

open Set
open TruthCore.Science.FineTuningInformation.Plenitude

theorem repeatedTypes : RepeatedTypes := by
  constructor
  · apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro b _
      exact ⟨(b, 0), Set.mem_univ _, rfl⟩
  · intro b
    refine ⟨fun n => (b, n), ?_, ?_⟩
    · intro m n h
      exact congrArg Prod.snd h
    · intro n
      exact ⟨Set.mem_univ _, rfl⟩

theorem fine_probability (p : unitInterval) :
    (observationLaw p).real fineEvent = (p : ℝ) := by
  rw [observationLaw, fineEvent, measureReal_def, Measure.prod_prod, measure_univ, mul_one]
  exact prior_true p

theorem positive_singletons (p : unitInterval) (hp : 0 < (p : ℝ))
    (hp' : (p : ℝ) < 1) (u : Universe) :
    0 < (observationLaw p).real {u} := by
  rcases u with ⟨b, n⟩
  have hb : 0 < (modelPrior p).real {b} := by
    cases b
    · rw [prior_false]
      exact sub_pos.mpr hp'
    · rw [prior_true]
      exact hp
  have h0 : half ≠ 0 := by
    intro h
    have hv := congrArg (fun q : unitInterval => (q : ℝ)) h
    norm_num [half] at hv
  have h1 : half ≠ 1 := by
    intro h
    have hv := congrArg (fun q : unitInterval => (q : ℝ)) h
    norm_num [half] at hv
  have hn : 0 < (geometricMeasure half).real {n} :=
    geometricMeasure_real_singleton_pos h0 h1 n
  rw [← Set.singleton_prod_singleton, observationLaw, measureReal_def,
    Measure.prod_prod, ENNReal.toReal_mul]
  exact mul_pos hb hn

theorem observationalUnderdetermination : ObservationalUnderdetermination := by
  refine ⟨repeatedTypes, ?_, ?_⟩
  · intro p
    refine ⟨?_, positive_singletons p.val p.property.1 p.property.2, fine_probability p.val⟩
    unfold observationLaw
    infer_instance
  · intro possible reachable h
    let lo : InteriorRate :=
      ⟨⟨1/100, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    let hi : InteriorRate :=
      ⟨⟨99/100, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    have he := h lo hi rfl
    simp only [fine_probability] at he
    norm_num [lo, hi] at he

theorem cutoffUnderdetermination : CutoffUnderdetermination := by
  intro a b ha hb
  refine ⟨?_, ?_, ?_⟩
  · intro n m h tag k hk
    simp only [slice, Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
  · intro tag k
    have ht : 1 ≤ (if tag then a else b) := by
      cases tag <;> simp <;> omega
    have hx := Nat.mul_le_mul_right (k + 1) ht
    simp only [slice, Finset.mem_range]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (by simpa using hx)
  · intro n
    have hA : 0 < (a : ℚ) := by exact_mod_cast ha
    have hB : 0 < (b : ℚ) := by exact_mod_cast hb
    have hN : 0 < (n : ℚ) + 1 := by positivity
    have hSum : 0 < (a : ℚ) + b := add_pos hA hB
    simp [cutoffLikelihood, slice, Nat.cast_mul, Nat.cast_add] <;>
      rw [← add_mul] <;> field_simp [ne_of_gt hN, ne_of_gt hSum] <;> ring

theorem observerWeightUnderdetermination : ObserverWeightUnderdetermination := by
  constructor
  · intro s
    simp [weightedLikelihood, likelihood]
  · intro s hother p hp hp'
    refine ⟨p / s.weight 0, (1-p) / s.weight 1,
      div_pos hp s.evidence_pos, div_pos (sub_pos.mpr hp') hother, ?_⟩
    have hx : s.weight 0 * (p / s.weight 0) = p := by
      field_simp [ne_of_gt s.evidence_pos]
    have hy : s.weight 1 * ((1-p) / s.weight 1) = 1-p := by
      field_simp [ne_of_gt hother]
    rw [weightedLikelihood, hx, hy, show p + (1-p) = 1 by ring, div_one]

end Plenitude

end TruthCore.Results.Science.FineTuningInformation
