module

public import TruthCore.Causality.SupplierAuditLikelihood
public import TruthCore.Logic.CorrectionCriterion

/-! Observation of complete supplier lists with a finite access boundary,
and calibration of population prefix frequencies on the same supplier models. -/

@[expose] public section
noncomputable section

namespace TruthCore.Causality.SupplierAuditVisibility

open Filter Topology
open TruthCore.Causality.SupplierAudit
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Causality.SupplierAuditLikelihood
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)

/-- Inside the visible range the complete incoming list is returned, including
an empty list when verified. Outside it no list is returned. -/
def visibleList (visible : ℕ) (supplies : ℕ → ℕ → Prop) (recipient : ℕ) : Option (Set ℕ) :=
  if recipient < visible then some {supplier | supplies supplier recipient} else none

/-- For each length, whether a matching prefix is reported and whether the
largest reported matching prefix ends there. The stop signal does not retain
the reason why a longer matching prefix was unavailable. -/
def untaggedRecord (visible : ℕ) (supplies : ℕ → ℕ → Prop) (length : ℕ) : Prop × Prop :=
  let reported k := k ≤ visible ∧ PrefixMatches k supplies
  (reported length, reported length ∧ ¬ reported (length + 1))

/-- A sourced world is visible through its root d; its endless counterpart is
visible through the preceding member. Both yield the same untagged record.
The boundary packet distinguishes them and gives an exact two-world criterion. -/
def BoundaryStopComparison : Prop :=
  ∀ depth : ℕ,
    let supplies (finite : Bool) := if finite then sourced depth else endless
    let visible (finite : Bool) := if finite then depth + 1 else depth
    let untagged (finite : Bool) := untaggedRecord (visible finite) (supplies finite)
    let boundary (finite : Bool) := visibleList (visible finite) (supplies finite) depth
    let root (finite : Bool) := RootAncestor depth 0 (supplies finite)
    untagged true = untagged false ∧
    (∀ k, untagged true k = (k ≤ depth, k = depth)) ∧
    root true ∧ ¬ root false ∧ ¬ AdmitsCriterion untagged root ∧
    boundary true = some ∅ ∧ boundary false = none ∧
    (∀ finite, boundary finite = some ∅ ↔ root finite)

/-- A mixture's latent matching-prefix probability when its endless share is
w and the remaining share has a fixed proper conditional depth prior. -/
def mixturePrefix (prior : ℕ → ℝ) (w : ℝ) (length : ℕ) : ℝ :=
  w + (1 - w) * depthLikelihood prior length

/-- At a calibrated cutoff the observation factor multiplies the latent match
probability. Knowing the finite tail below one yields finite recovery; a tail
of one makes that cutoff independent of the share. Across lengths, a positive
common profile and proper priors suffice for limit recovery and identification,
even when the compared proper priors differ. -/
def CalibratedPrefixRecovery : Prop :=
  (∀ (prior : ℕ → ℝ) (w v observed : ℝ) (length : ℕ),
    (∀ depth, 0 ≤ prior depth) → HasSum prior 1 → 0 ≤ w → w ≤ 1 →
    0 < v → v ≤ 1 → observed = v * mixturePrefix prior w length →
    (depthLikelihood prior length < 1 →
      w = (observed / v - depthLikelihood prior length) / (1 - depthLikelihood prior length)) ∧
    (depthLikelihood prior length = 1 → observed = v) ∧
    (0 < depthLikelihood prior length →
      v / (v * depthLikelihood prior length) = 1 / depthLikelihood prior length)) ∧
  (∀ (prior : ℕ → ℝ) (w : ℝ) (v observed : ℕ → ℝ),
    (∀ depth, 0 ≤ prior depth) → HasSum prior 1 → 0 ≤ w → w ≤ 1 →
    (∀ k, 0 < v k ∧ v k ≤ 1) → (∀ k, observed k = v k * mixturePrefix prior w k) →
    Tendsto (fun k => observed k / v k) atTop (𝓝 w)) ∧
  (∀ (p q : ℕ → ℝ) (w u : ℝ) (v observed : ℕ → ℝ),
    (∀ depth, 0 ≤ p depth) → HasSum p 1 → (∀ depth, 0 ≤ q depth) → HasSum q 1 →
    0 ≤ w → w ≤ 1 → 0 ≤ u → u ≤ 1 → (∀ k, 0 < v k ∧ v k ≤ 1) →
    (∀ k, observed k = v k * mixturePrefix p w k) →
    (∀ k, observed k = v k * mixturePrefix q u k) → w = u)

/-- A common observation cap makes share zero and share one observationally
equal when the finite prior is concentrated at the cap. -/
def CommonCapControl : Prop :=
  ∀ cap : ℕ,
    let v (k : ℕ) : ℝ := if k ≤ cap then 1 else 0
    let p (d : ℕ) : ℝ := if d = cap then 1 else 0
    (∀ d, 0 ≤ p d) ∧ HasSum p 1 ∧
    (∀ k, k ≤ cap → depthLikelihood p k = 1) ∧
    (∀ k, cap < k → depthLikelihood p k = 0) ∧
    (fun k => v k * mixturePrefix p 0 k) = (fun k => v k * mixturePrefix p 1 k)

end TruthCore.Causality.SupplierAuditVisibility
