module

public import TruthCore.Causality.NecessarilyUnderived

/-! Strength orders of the lifting premise `NecessaryPredecessorLifting` over
`NoNovelNecessarySupport` and `NoContingentGroundOfNecessary`
(`TruthCore.Causality.NecessarilyUnderived`), found by a `truth discover` run
over the modal sense-fork nodes (findings t3 and t6, #1784), with certified
differences (#1598) and strictness controls on two finite models. No premise is
asserted to hold. -/

@[expose] public section

namespace TruthCore.Results.Causality.LiftingStrength

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived

/-- Lifting entails no novel necessary support: the actual edge is lifting's
third conjunct; the weak version's necessity hypothesis on the source is unused. -/
theorem noNovelOfLifting {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h : NecessaryPredecessorLifting m supportsEsse w₀) :
    NoNovelNecessarySupport m supportsEsse w₀ :=
  fun w source target _ hTarget hSource hEdge => (h w source target hTarget hSource hEdge).2.2

/-- Lifting entails no contingent ground of the necessary: the source's
necessity is lifting's first conjunct. -/
theorem noContingentOfLifting {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h : NecessaryPredecessorLifting m supportsEsse w₀) :
    NoContingentGroundOfNecessary m supportsEsse w₀ :=
  fun w source target hSource hTarget hEdge => (h w source target hTarget hSource hEdge).1

/-- Certified difference: lifting ⇔ no novel support ∧ supporters of necessary
individuals are necessary and actual. Backward, the delta supplies the source's
necessity, which no novel support needs to give the actual edge. -/
theorem liftingOverNoNovelExact : LiftingOverNoNovelExact := by
  intro World Being m supportsEsse w₀
  constructor
  · intro h
    exact ⟨noNovelOfLifting m supportsEsse w₀ h, fun w source target hTarget hSource hEdge =>
      ⟨(h w source target hTarget hSource hEdge).1, (h w source target hTarget hSource hEdge).2.1⟩⟩
  · rintro ⟨hNoNovel, hDelta⟩ w source target hTarget hSource hEdge
    obtain ⟨hNecessary, hActual⟩ := hDelta w source target hTarget hSource hEdge
    exact ⟨hNecessary, hActual, hNoNovel w source target hNecessary hTarget hSource hEdge⟩

/-- Certified difference: lifting ⇔ no contingent ground ∧ support edges into
necessary individuals recur actually. -/
theorem liftingOverNoContingentExact : LiftingOverNoContingentExact := by
  intro World Being m supportsEsse w₀
  constructor
  · intro h
    exact ⟨noContingentOfLifting m supportsEsse w₀ h, fun w source target hTarget hSource hEdge =>
      (h w source target hTarget hSource hEdge).2⟩
  · rintro ⟨hNoContingent, hDelta⟩ w source target hTarget hSource hEdge
    exact ⟨hNoContingent w source target hSource hTarget hEdge,
      hDelta w source target hTarget hSource hEdge⟩

/-- Strictness control (a): in the contingent-source model no novel necessary
support holds vacuously and lifting fails. -/
theorem contingentSourceSeparates : ContingentSourceSeparates := by
  refine ⟨trivial, ?_, ?_⟩
  · intro w source target hSource _ _ hEdge
    obtain ⟨_, rfl, _⟩ := hEdge
    rcases hSource false trivial with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · intro h
    have hNec := (h true false true (fun _ _ => Or.inl rfl) (Or.inr rfl) ⟨rfl, rfl, rfl⟩).1
    rcases hNec false trivial with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- Strictness control (b): in the two-necessary model no contingent ground
holds and lifting fails, since the edge is absent at the actual world. -/
theorem nonActualEdgeSeparates : NonActualEdgeSeparates := by
  refine ⟨trivial, fun _ _ _ _ _ _ _ _ => trivial, ?_⟩
  intro h
  have hEdge := (h true false true (fun _ _ => trivial) trivial ⟨rfl, rfl, rfl⟩).2.2
  exact absurd hEdge.1 (by decide)

end TruthCore.Results.Causality.LiftingStrength
