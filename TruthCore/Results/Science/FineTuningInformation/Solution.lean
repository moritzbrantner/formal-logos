module

public import TruthCore.Science.FineTuningInformation
public import TruthCore.Explanation.HistorySelection
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

/-! Plenitude controls. The registered theorems sit at the top level of the
results namespace so that the generated Challenge freezes them. -/
section Plenitude

open Set
open TruthCore.Science.FineTuningInformation.Plenitude
open TruthCore.Logic.CarrierProbability

universe u

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

private theorem cutoff_frequency (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    frequency fineEvent (cutoffStage a b n) = (a : ℝ) / ((a : ℝ) + b) := by
  classical
  have hfilter : (cutoffStage a b n).filter (· ∈ fineEvent) =
      ({true} ×ˢ Finset.range (a * (n + 1)) : Finset Universe) := by
    ext ⟨t, k⟩
    cases t <;> simp [cutoffStage, fineEvent]
  have hdisj : Disjoint ({true} ×ˢ Finset.range (a * (n + 1)) : Finset Universe)
      ({false} ×ˢ Finset.range (b * (n + 1))) := by
    rw [Finset.disjoint_left]
    rintro ⟨t, k⟩ h₁ h₂
    simp only [Finset.mem_product, Finset.mem_singleton] at h₁ h₂
    rw [h₁.1] at h₂
    exact Bool.noConfusion h₂.1
  have hcard : (cutoffStage a b n).card = a * (n + 1) + b * (n + 1) := by
    rw [cutoffStage, Finset.card_union_of_disjoint hdisj]
    simp
  unfold frequency
  rw [Finset.filter_congr_decidable, hfilter, hcard]
  have hA : 0 < (a : ℝ) := by exact_mod_cast ha
  have hB : 0 < (b : ℝ) := by exact_mod_cast hb
  have hN : 0 < (n : ℝ) + 1 := by positivity
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [← add_mul]
  field_simp

theorem cutoffUnderdetermination : CutoffUnderdetermination := by
  intro a b ha hb
  refine ⟨⟨?_, ?_⟩, fun n => cutoff_frequency a b n ha hb, ?_⟩
  · intro n m h u hu
    rcases u with ⟨t, k⟩
    have hmono : ∀ c : ℕ, c * (n + 1) ≤ c * (m + 1) := fun c =>
      Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1)
    cases t <;> simp only [cutoffStage, Finset.mem_union, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_range] at hu ⊢ <;> simp at hu ⊢
    · exact lt_of_lt_of_le hu (hmono b)
    · exact lt_of_lt_of_le hu (hmono a)
  · rintro ⟨t, k⟩
    refine ⟨k, ?_⟩
    have hk : ∀ c : ℕ, 0 < c → k < c * (k + 1) := fun c hc =>
      lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_mul_of_pos_left _ hc)
    cases t <;> simp [cutoffStage, hk a ha, hk b hb]
  · have h : (fun n => frequency fineEvent (cutoffStage a b n)) =
        fun _ => (a : ℝ) / ((a : ℝ) + b) := funext fun n => cutoff_frequency a b n ha hb
    unfold HasDensity
    rw [h]
    exact tendsto_const_nhds

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
    have hsum : p + (1-p) = 1 := by ring
    rw [weightedLikelihood, hx, hy, hsum, div_one]

/-- Push the product control forward along a surjection `Bool × ℕ → W` that
sends the true fiber onto `s` and the false fiber onto its complement. One
construction therefore serves every countable carrier with a nonempty event
and nonempty complement; no second mixture construction is needed. -/
theorem arbitraryInteriorMass : ArbitraryInteriorMass.{u} := by
  intro W _ _ _ s _ _ p
  classical
  obtain ⟨e, he⟩ : ∃ e : ℕ → s, Function.Surjective e := exists_surjective_nat _
  obtain ⟨f, hf⟩ : ∃ f : ℕ → (sᶜ : Set W), Function.Surjective f :=
    exists_surjective_nat _
  let g : Universe → W := fun u => if u.1 then (e u.2 : W) else (f u.2 : W)
  have hg : Measurable g := measurable_of_countable g
  have hpre : g ⁻¹' s = fineEvent := by
    ext ⟨b, n⟩
    cases b
    · simp only [mem_preimage, g, fineEvent, mem_prod, mem_singleton_iff, mem_univ,
        and_true, Bool.false_eq_true, ite_false, iff_false]
      exact (f n).property
    · simp only [mem_preimage, g, fineEvent, mem_prod, mem_singleton_iff, mem_univ,
        and_true, ite_true, iff_true]
      exact (e n).property
  have hsurj : ∀ x : W, ∃ u, g u = x := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨n, hn⟩ := he ⟨x, hx⟩
      exact ⟨(true, n), by simp [g, hn]⟩
    · obtain ⟨n, hn⟩ := hf ⟨x, hx⟩
      exact ⟨(false, n), by simp [g, hn]⟩
  have hprob : IsProbabilityMeasure (observationLaw p.val) := by
    unfold observationLaw
    infer_instance
  refine ⟨(observationLaw p.val).map g, inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨u, hu⟩ := hsurj x
    rw [Measure.map_apply hg (measurableSet_singleton x)]
    have hpos := positive_singletons p.val p.property.1 p.property.2 u
    rw [measureReal_def] at hpos
    refine lt_of_lt_of_le (ENNReal.toReal_pos_iff.mp hpos).1 (measure_mono ?_)
    intro v hv
    rw [mem_singleton_iff] at hv
    simp [hv, hu]
  · rw [measureReal_def, Measure.map_apply hg (Set.to_countable s).measurableSet, hpre,
      ← measureReal_def]
    exact fine_probability p.val

/-- Compose with the repository's exact identifiability criterion. There is
no decoder, even one of arbitrary complexity, which reads the entire fixed
ontology profile and returns the correct observer likelihood for every
interior measure. This does not assert that every physical law has this defect. -/
theorem no_scope_decoder (possible reachable : Set Bool) :
    ¬ ∃ recover : (Set Bool × Set Bool × Set Universe × (Universe → Bool)) → ℝ,
      ∀ p : InteriorRate, recover (scopeData possible reachable p) =
        (observationLaw p.val).real fineEvent := by
  intro h
  exact (observationalUnderdetermination.2.2 possible reachable)
    ((TruthCore.Science.Identifiability.total_factor_iff _ _).mp h).1

/-- #736's evidence-only criterion, not a new definition of metaphysical
adequacy. Every truth-vector derived from the fixed scope data is invariant;
the proposition that the report has probability at least one half is not.
The basis can be infinite, and no restrictions on the readout are imposed. -/
theorem threshold_not_evidence_only (possible reachable : Set Bool) (R : Type)
    (read : (Set Bool × Set Bool × Set Universe × (Universe → Bool)) → R → Prop)
    (basis : R → Prop) :
    ¬ TruthCore.Explanation.HistorySelection.EvidenceOnly
      (fun (p : InteriorRate) r => read (scopeData possible reachable p) r) basis
      (fun p => (1/2 : ℝ) ≤ (observationLaw p.val).real fineEvent) := by
  intro h
  let lo : InteriorRate :=
    ⟨⟨1/100, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  let hi : InteriorRate :=
    ⟨⟨99/100, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  have he := h lo hi (by intro r _; rfl)
  simp only [fine_probability] at he
  norm_num [lo, hi] at he

end Plenitude

end TruthCore.Results.Science.FineTuningInformation
