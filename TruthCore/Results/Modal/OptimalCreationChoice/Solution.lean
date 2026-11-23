module

public import TruthCore.Modal.OptimalCreationChoice

@[expose] public section

namespace TruthCore.Results.Modal.OptimalCreationChoice
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.OptimalCreationChoice
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Results.Modal.SelectedEffectBridge

theorem uniqueOptimalStable {W B A V : Type} [PartialOrder V]
    (p : OutputProfile W B A) (w : W) (a : A) (feasible : Set B) (quality : B → V)
    (h : OptimalOutputs p w a feasible quality)
    (unique : ∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y) :
    StableActOutput p w a := by
  intro x hx v hv hp
  obtain ⟨y, hy⟩ := (h v (Or.inr hv)).1 hp
  have heq := unique x y ((h w (Or.inl rfl)).2 x hx) ((h v (Or.inr hv)).2 y hy)
  exact heq ▸ hy

theorem noOptimalWhenImprovable {B V : Type} [PartialOrder V]
    (feasible : Set B) (quality : B → V) (h : StrictlyImprovable feasible quality) :
    ¬ ∃ x, Optimal feasible quality x := by
  rintro ⟨x, hx, hmax⟩
  obtain ⟨y, hy, hlt⟩ := h x hx
  exact (not_le_of_gt hlt) (hmax.2 ⟨y, hy, rfl⟩)

theorem tiedOptimal (b : Bool) : Optimal tiedCandidates tiedQuality (some b) := by
  refine ⟨⟨b, rfl⟩, ⟨⟨some b, ⟨b, rfl⟩, rfl⟩, ?_⟩⟩
  rintro _ ⟨y, _, rfl⟩
  exact Nat.le_refl 0

theorem checks : OptimalChoiceCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B A V inst p w a feasible quality h hu
    exact uniqueOptimalStable p w a feasible quality h hu
  · intro W B A V inst p w a x feasible quality h hu hs hr ha hx
    exact selectedEffectNecessary p w a x hs hr ha
      (uniqueOptimalStable p w a feasible quality h hu) hx
  · intro B V inst feasible quality h
    exact noOptimalWhenImprovable feasible quality h
  · intro B V inst feasible quality x y hx hy
    exact le_antisymm (hy.2.2 ⟨x, hx.1, rfl⟩) (hx.2.2 ⟨y, hy.1, rfl⟩)
  · intro x _
    exact ⟨x + 1, Set.mem_univ _, Nat.lt_succ_self x⟩
  · refine ⟨?_, tiedOptimal false, tiedOptimal true, ?_, varyingChecks.2.2.2.2.1,
      varyingChecks.2.2.2.2.2.2.1, varyingChecks.2.2.2.2.2.2.2.2.2⟩
    · intro v _
      constructor
      · intro _
        exact ⟨some v, rfl⟩
      · intro x hx
        rw [hx]
        exact tiedOptimal v
    · intro h
      cases h

/-! The following are additional #1737 structural controls. They do not modify
the existing frozen \`OptimalChoiceCertificate\` or any registered premise. -/

/-- Kernel-checkable three-world model. No divine/free-agency interpretation
follows from the satisfiability of the displayed finite assignments. -/
theorem threeWorldCreationChecks : ThreeWorldCreationControl := by
  decide

/-- Both produced creatures are tied optima under the fixed created-candidate
comparison. The no-creation world has no performance or output, rather than
a spurious \`none\` output being scored against created candidates. -/
theorem threeWorldOptimalOutputs :
    OptimalOutputs threeWorldCreation (some false) () tiedCandidates tiedQuality := by
  intro v _
  constructor
  · intro hp
    cases v with
    | none =>
      exact False.elim (hp rfl)
    | some b =>
      exact ⟨some b, ⟨by decide, rfl⟩⟩
  · intro x hx
    change v ≠ none ∧ x = v at hx
    rcases hx with ⟨hn, rfl⟩
    cases v with
    | none => exact False.elim (hn rfl)
    | some b => exact tiedOptimal b

/-- Deleting only cross-world positive output while retaining the same rigid
act and unique optimal *created* candidate leaves the effect contingent. -/
theorem omissionStructureChecks : OmissionStructureControl := by
  decide

theorem soleCreatedOptimal :
    Optimal soleCreatedCandidate tiedQuality firstEffect := by
  refine ⟨(by simp [soleCreatedCandidate]), ?_⟩
  refine ⟨⟨firstEffect, (by simp [soleCreatedCandidate]), rfl⟩, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  exact Nat.le_refl 0

theorem soleCreatedUnique :
    ∀ x y, Optimal soleCreatedCandidate tiedQuality x →
      Optimal soleCreatedCandidate tiedQuality y → x = y := by
  intro x y hx hy
  have hx' : x = firstEffect := by simpa [soleCreatedCandidate] using hx.1
  have hy' : y = firstEffect := by simpa [soleCreatedCandidate] using hy.1
  exact hx'.trans hy'.symm

/-- Total optimal output remains true when productive exercise is optional:
it requires output only where that act is performed. -/
theorem optionalOmissionOptimal :
    OptimalOutputs optionallyPerformedOmission true ()
      soleCreatedCandidate tiedQuality := by
  intro v _
  constructor
  · intro hv
    exact ⟨firstEffect, ⟨hv, rfl⟩⟩
  · intro x hx
    change v = true ∧ x = firstEffect at hx
    rw [hx.2]
    exact soleCreatedOptimal

/-- All produced objects are optimal in the universal-performance alternative,
but at the omission world no output exists. -/
theorem universalOmissionOutputOptimal :
    ∀ v x, alwaysPerformedOmission.output v () x →
      Optimal soleCreatedCandidate tiedQuality x := by
  intro v x hx
  change v = true ∧ x = firstEffect at hx
  rw [hx.2]
  exact soleCreatedOptimal

/-- Unique feasible optimum + worldwise optimality + SameActEverywhere do not
imply the positive-output-totality conjunct of \`OptimalOutputs\`.
This exactly isolates an extra premise of \`uniqueOptimalStable\`. -/
theorem universalOmissionNotTotal :
    ¬ OptimalOutputs alwaysPerformedOmission true ()
      soleCreatedCandidate tiedQuality := by
  intro h
  obtain ⟨x, hx⟩ := (h false (Or.inr True.intro)).1 True.intro
  change false = true ∧ x = firstEffect at hx
  exact Bool.noConfusion hx.1

/-- Joint controls: same source, unique candidate, optional exercise versus
same-act but omitted output. The source/effect meanings and ontology are fixed. -/
theorem omissionChoiceChecks :
    Optimal soleCreatedCandidate tiedQuality firstEffect ∧
    (∀ x y, Optimal soleCreatedCandidate tiedQuality x →
      Optimal soleCreatedCandidate tiedQuality y → x = y) ∧
    OptimalOutputs optionallyPerformedOmission true () soleCreatedCandidate tiedQuality ∧
    (∀ v x, alwaysPerformedOmission.output v () x →
      Optimal soleCreatedCandidate tiedQuality x) ∧
    ¬ OptimalOutputs alwaysPerformedOmission true () soleCreatedCandidate tiedQuality := by
  exact ⟨soleCreatedOptimal, soleCreatedUnique, optionalOmissionOptimal,
    universalOmissionOutputOptimal, universalOmissionNotTotal⟩

end TruthCore.Results.Modal.OptimalCreationChoice
