module

public import TruthCore.Modal.OptimalCreationChoice

@[expose] public section

namespace TruthCore.Results.Modal.OptimalCreationChoice
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.OptimalCreationChoice
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.German.Kant.CosmologicalInference
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
the existing frozen `OptimalChoiceCertificate` or any registered premise. -/

/-- Kernel-checkable three-world model. No divine/free-agency interpretation
follows from the satisfiability of the displayed finite assignments. -/
theorem threeWorldCreationChecks : ThreeWorldCreationControl := by
  have hSound : SoundDistinctCauses threeWorldCreation.ontic := by
    intro w x y h
    change x = source ∧ w ≠ none ∧ y = w at h
    rcases h with ⟨rfl, hn, rfl⟩
    refine ⟨Or.inl rfl, Or.inr ⟨hn, rfl⟩, ?_⟩
    intro heq
    exact hn heq.symm
  have hNecessary : NecessaryAt threeWorldCreation.ontic (some false) source := by
    intro _ _
    exact Or.inl rfl
  have hCap : ∀ v, hasIntellectualCapacity v source ∧
      hasVolitionalCapacity v source ∧ ∀ b, recognizesOption v b := by
    intro _
    exact ⟨rfl, rfl, fun _ => True.intro⟩
  have hRealized : RealizedOutputs threeWorldCreation := by
    intro v _ x _ hx
    change v ≠ none ∧ x = v at hx
    exact ⟨rfl, hx.1, hx.2⟩
  have hLocal : LocallyDeterministic threeWorldCreation := by
    intro _ _ _ _ hx hy
    exact hx.2.trans hy.2.symm
  have hTracks : TracksSelectedCreation threeWorldCreation selectedCandidate := by
    intro v b
    constructor
    · intro hx
      exact hx.2.symm
    · intro hv
      subst v
      exact ⟨by simp, rfl⟩
  have hFirstContingent :
      ContingentAt threeWorldCreation.ontic (some false) firstEffect := by
    refine ⟨(by simp [threeWorldCreation, firstEffect, source]), none, True.intro, ?_⟩
    simp [threeWorldCreation, firstEffect, source]
  have hSecondContingent :
      ContingentAt threeWorldCreation.ontic (some true) secondEffect := by
    refine ⟨(by simp [threeWorldCreation, secondEffect, source]), none, True.intro, ?_⟩
    simp [threeWorldCreation, secondEffect, source]
  have hNoExercise :
      ¬ ExercisesCausation threeWorldCreation.ontic none source := by
    rintro ⟨y, hy⟩
    exact hy.2.1 rfl
  have hNotSame : ¬ SameActEverywhere threeWorldCreation (some false) () := by
    intro h
    exact (h none True.intro) rfl
  have hNotStable : ¬ StableActOutput threeWorldCreation (some false) () := by
    intro h
    have hb := h firstEffect (by simp [threeWorldCreation, firstEffect])
      (some true) True.intro (by simp [threeWorldCreation])
    cases hb.2
  have hCoincident : threeWorldCreation.output (some false) () firstEffect ∧
      coincidentalTag (some false) false := by
    exact ⟨⟨by simp, rfl⟩, rfl⟩
  have hNotTag : ¬ TracksSelectedCreation threeWorldCreation coincidentalTag := by
    intro h
    have hb := (h (some true) true).mp
      (show threeWorldCreation.output (some true) () secondEffect from ⟨by simp, rfl⟩)
    exact Bool.noConfusion hb
  exact ⟨(fun _ _ => True.intro), hSound, hNecessary, hCap, hRealized, hLocal,
    hTracks, (by simp [threeWorldCreation, firstEffect]),
    (by simp [threeWorldCreation, secondEffect]), hFirstContingent,
    hSecondContingent, hNoExercise, hNotSame, hNotStable, hCoincident, hNotTag⟩

/-- Both produced creatures are tied optima under the fixed created-candidate
comparison. The no-creation world has no performance or output, rather than
a spurious `none` output being scored against created candidates. -/
theorem threeWorldOptimalOutputs :
    OptimalOutputs threeWorldCreation (some false) () tiedCandidates tiedQuality := by
  intro v _
  constructor
  · intro hp
    cases v with
    | none =>
      exact False.elim (hp rfl)
    | some b =>
      exact ⟨some b, ⟨by simp, rfl⟩⟩
  · intro x hx
    change v ≠ none ∧ x = v at hx
    rcases hx with ⟨hn, heq⟩
    cases v with
    | none => exact False.elim (hn rfl)
    | some b =>
      subst x
      exact tiedOptimal b

/-- Deleting only cross-world positive output while retaining the same rigid
act and unique optimal *created* candidate leaves the effect contingent. -/
theorem omissionStructureChecks : OmissionStructureControl := by
  have hSound : SoundDistinctCauses alwaysPerformedOmission.ontic := by
    intro w x y h
    change x = source ∧ w = true ∧ y = firstEffect at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨Or.inl rfl, Or.inr ⟨rfl, rfl⟩, by decide⟩
  have hNecessary : NecessaryAt alwaysPerformedOmission.ontic true source := by
    intro _ _
    exact Or.inl rfl
  have hRealized : RealizedOutputs alwaysPerformedOmission := by
    intro v _ x _ hx
    exact ⟨rfl, hx.1, hx.2⟩
  have hOptionalRealized : RealizedOutputs optionallyPerformedOmission := by
    intro v _ x _ hx
    exact ⟨rfl, hx.1, hx.2⟩
  have hLocal : LocallyDeterministic alwaysPerformedOmission := by
    intro _ _ _ _ hx hy
    exact hx.2.trans hy.2.symm
  have hSame : SameActEverywhere alwaysPerformedOmission true () := by
    intro _ _
    trivial
  have hNotSame : ¬ SameActEverywhere optionallyPerformedOmission true () := by
    intro h
    exact Bool.noConfusion (h false True.intro)
  have hStable : StableActOutput optionallyPerformedOmission true () := by
    intro x hx v _ hp
    change v = true at hp
    subst v
    exact hx
  have hNotStable : ¬ StableActOutput alwaysPerformedOmission true () := by
    intro h
    have hb := h firstEffect ⟨rfl, rfl⟩ false True.intro True.intro
    exact Bool.noConfusion hb.1
  have hContingent : ContingentAt alwaysPerformedOmission.ontic true firstEffect := by
    refine ⟨Or.inr ⟨rfl, rfl⟩, false, True.intro, ?_⟩
    rintro (h | ⟨h, _⟩)
    · cases h
    · cases h
  have hNoExercise : ¬ ExercisesCausation alwaysPerformedOmission.ontic false source := by
    rintro ⟨y, hy⟩
    exact Bool.noConfusion hy.2.1
  exact ⟨hSound, hNecessary, hRealized, hOptionalRealized, hLocal, hSame,
    hNotSame, hStable, hNotStable, hContingent, hNoExercise⟩

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
imply the positive-output-totality conjunct of `OptimalOutputs`.
This exactly isolates an extra premise of `uniqueOptimalStable`. -/
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
