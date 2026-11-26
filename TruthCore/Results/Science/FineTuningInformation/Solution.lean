module

public import TruthCore.Science.FineTuningInformation

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

private theorem row_true (d n : Sampling) :
    (reportKernel d n true).real {true} = (reportRate d : ℝ) :=
  prior_true (reportRate d)

private theorem row_false (d n : Sampling) :
    (reportKernel d n false).real {true} = (reportRate n : ℝ) :=
  prior_true (reportRate n)

theorem observerInformation : ObserverInformationCriterion := by
  intro p d n hp hp'
  change mutualInformation (modelPrior p ⊗ₘ reportKernel d n) = 0 ↔ _
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
    rw [row_true, row_false] at hrates
    exact Rat.cast_injective (show (likelihood d : ℝ) = (likelihood n : ℝ) from hrates)
  · intro h
    have hrates : reportRate d = reportRate n := Subtype.ext (by simp [reportRate, h])
    have hk : reportKernel d n = Kernel.const Bool (modelPrior (reportRate d)) := by
      ext m : 1
      cases m
      · exact congrArg modelPrior hrates.symm
      · rfl
    rw [mutualInformation_eq_zero_iff, hk, Measure.compProd_const, Measure.map_fst_prod,
      Measure.map_snd_prod, measure_univ, measure_univ, one_smul, one_smul]

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

end TruthCore.Results.Science.FineTuningInformation
