module

public import TruthCore.Causality.SupplierAuditVisibility
public import TruthCore.Logic.InformationInvariance

@[expose] public section
namespace TruthCore.Results.Causality.SupplierAuditVisibility

open Filter Topology
open TruthCore.Causality.SupplierAudit
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Causality.SupplierAuditLikelihood
open TruthCore.Causality.SupplierAuditVisibility
open TruthCore.Causality.PostCutStore (prefixSum)
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)
open TruthCore.Logic.InformationInvariance (factor_iff)

theorem boundaryStopComparison (comparison : PrefixComparison) : BoundaryStopComparison := by
  intro depth
  have finitePrefix (k : ℕ) : (k ≤ depth + 1 ∧ PrefixMatches k (sourced depth)) ↔
      k ≤ depth := by
    rw [comparison.1]
    exact ⟨And.right, fun fits => ⟨fits.trans (Nat.le_succ depth), fits⟩⟩
  have endlessPrefix (k : ℕ) : (k ≤ depth ∧ PrefixMatches k endless) ↔ k ≤ depth :=
    ⟨And.left, fun fits => ⟨fits, (comparison.2.1 k).1⟩⟩
  have stop (k : ℕ) : (k ≤ depth ∧ ¬ k + 1 ≤ depth) ↔ k = depth := by omega
  have finiteRecord (k : ℕ) :
      untaggedRecord (depth + 1) (sourced depth) k = (k ≤ depth, k = depth) := by
    simp only [untaggedRecord, finitePrefix, stop]
  have endlessRecord (k : ℕ) :
      untaggedRecord depth endless k = (k ≤ depth, k = depth) := by
    simp only [untaggedRecord, endlessPrefix, stop]
  have same : untaggedRecord (depth + 1) (sourced depth) = untaggedRecord depth endless :=
    funext fun k => (finiteRecord k).trans (endlessRecord k).symm
  have finiteRoot := (comparison.2.1 depth).2.2
  have notEndlessRoot : ¬ RootAncestor depth 0 endless := by
    intro root
    obtain ⟨supplier, edge⟩ := endlessBorrower depth
    exact root.2 supplier edge
  have finiteBoundary : visibleList (depth + 1) (sourced depth) depth = some ∅ := by
    rw [visibleList, ite_eq_left (Nat.lt_succ_self depth)]
    congr 1
    ext supplier
    exact iff_false_intro (finiteRoot.2 supplier)
  have endlessBoundary : visibleList depth endless depth = none := by
    simp [visibleList]
  dsimp only
  refine ⟨same, finiteRecord, finiteRoot, notEndlessRoot, ?_, finiteBoundary, endlessBoundary, ?_⟩
  · intro classifier
    have invariant := (factor_iff _ _).mp classifier
    exact notEndlessRoot ((invariant true false same).mp finiteRoot)
  · intro finite
    cases finite
    · change visibleList depth endless depth = some ∅ ↔ RootAncestor depth 0 endless
      simp [endlessBoundary, notEndlessRoot]
    · change visibleList (depth + 1) (sourced depth) depth = some ∅ ↔
        RootAncestor depth 0 (sourced depth)
      simp [finiteBoundary, finiteRoot]

theorem calibratedPrefixRecovery (comparison : PrefixComparison) : CalibratedPrefixRecovery := by
  have recover : ∀ (prior : ℕ → ℝ) (w : ℝ) (v observed : ℕ → ℝ),
      (∀ depth, 0 ≤ prior depth) → HasSum prior 1 →
      (∀ k, 0 < v k ∧ v k ≤ 1) → (∀ k, observed k = v k * mixturePrefix prior w k) →
      Tendsto (fun k => observed k / v k) atTop (𝓝 w) := by
    intro prior w v observed nonnegative proper positive factors
    obtain ⟨_, _, _, _, _, properTail, _⟩ := comparison
    have tailFormula := (properTail prior nonnegative proper).1
    have tailLimit : Tendsto (depthLikelihood prior) atTop (𝓝 0) := by
      rw [show depthLikelihood prior = fun k => 1 - prefixSum prior k from funext tailFormula]
      simpa only [prefixSum, sub_self] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub proper.tendsto_sum_nat
    have corrected : (fun k => observed k / v k) = mixturePrefix prior w := by
      funext k
      rw [factors k, mul_comm, mul_div_cancel_right₀ _ (positive k).1.ne']
    rw [corrected]
    change Tendsto (fun k => w + (1 - w) * depthLikelihood prior k) atTop (𝓝 w)
    simpa only [mul_zero, add_zero] using
      (tailLimit.const_mul (1 - w)).const_add w
  refine ⟨?_, ?_, ?_⟩
  · intro prior w v observed length _ _ _ _ positive _ factors
    have corrected : observed / v = mixturePrefix prior w length := by
      rw [factors, mul_comm, mul_div_cancel_right₀ _ positive.ne']
    refine ⟨?_, ?_, ?_⟩
    · intro belowOne
      rw [corrected, eq_div_iff (sub_pos.mpr belowOne).ne', mixturePrefix]
      ring
    · intro full
      simp [factors, mixturePrefix, full]
    · intro tailPositive
      field_simp [positive.ne', tailPositive.ne']
  · intro p w v observed nonnegative proper _ _ positive factors
    exact recover p w v observed nonnegative proper positive factors
  · intro p q w u v observed pNonnegative pProper qNonnegative qProper _ _ _ _ positive hp hq
    exact tendsto_nhds_unique (recover p w v observed pNonnegative pProper positive hp)
      (recover q u v observed qNonnegative qProper positive hq)

theorem commonCapControl (comparison : PrefixComparison) : CommonCapControl := by
  intro cap
  classical
  let p (d : ℕ) : ℝ := if d = cap then 1 else 0
  have tailWeight (k : ℕ) : depthLikelihood p k = if k ≤ cap then 1 else 0 := by
    have asSingle (d : ℕ) : (if PrefixMatches k (sourced d) then p d else 0) =
        if d = cap then (if k ≤ cap then 1 else 0) else 0 := by
      rw [comparison.1]
      by_cases atCap : d = cap <;> simp [p, atCap]
    unfold depthLikelihood
    exact (tsum_congr asSingle).trans (hasSum_ite_eq cap _).tsum_eq
  have nonnegative (d : ℕ) : 0 ≤ p d := by
    unfold p
    split <;> norm_num
  refine ⟨nonnegative, hasSum_ite_eq cap 1, ?_, ?_, ?_⟩
  · intro k visible
    exact (tailWeight k).trans (ite_eq_left visible)
  · intro k hidden
    exact (tailWeight k).trans (ite_eq_right (Nat.not_le.mpr hidden))
  · funext k
    let v : ℝ := if k ≤ cap then 1 else 0
    change v * mixturePrefix p 0 k = v * mixturePrefix p 1 k
    by_cases visible : k ≤ cap
    · simp [mixturePrefix, tailWeight, visible]
    · simp [v, visible]

end TruthCore.Results.Causality.SupplierAuditVisibility
