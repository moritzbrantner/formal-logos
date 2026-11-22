import TruthCore.Causality.NecessarilyUnderived

/-! Strength orders of the lifting premise `NecessaryPredecessorLifting` over
`NoNovelNecessarySupport` and `NoContingentGroundOfNecessary`
(`TruthCore.Causality.NecessarilyUnderived`), found by a `truth discover` run
over the modal sense-fork nodes (findings t3 and t6, #1784), with certified
differences (#1598) and strictness controls on two finite models. No premise is
asserted to hold. -/

namespace TruthCore.Results.Causality.LiftingStrength

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived

/-- Lifting entails no novel necessary support: the actual edge is lifting's
third conjunct; the weak version's necessity hypothesis on the source is unused. -/
theorem noNovelOfLifting {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h : NecessaryPredecessorLifting m supportsEsse w₀) :
    NoNovelNecessarySupport m supportsEsse w₀ := by
  sorry

/-- Lifting entails no contingent ground of the necessary: the source's
necessity is lifting's first conjunct. -/
theorem noContingentOfLifting {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h : NecessaryPredecessorLifting m supportsEsse w₀) :
    NoContingentGroundOfNecessary m supportsEsse w₀ := by
  sorry

/-- Certified difference: lifting ⇔ no novel support ∧ supporters of necessary
individuals are necessary and actual. Backward, the delta supplies the source's
necessity, which no novel support needs to give the actual edge. -/
theorem liftingOverNoNovelExact : LiftingOverNoNovelExact := by
  sorry

/-- Certified difference: lifting ⇔ no contingent ground ∧ support edges into
necessary individuals recur actually. -/
theorem liftingOverNoContingentExact : LiftingOverNoContingentExact := by
  sorry

/-- Strictness control (a): in the contingent-source model no novel necessary
support holds vacuously and lifting fails. -/
theorem contingentSourceSeparates : ContingentSourceSeparates := by
  sorry

/-- Strictness control (b): in the two-necessary model no contingent ground
holds and lifting fails, since the edge is absent at the actual world. -/
theorem nonActualEdgeSeparates : NonActualEdgeSeparates := by
  sorry

end TruthCore.Results.Causality.LiftingStrength
