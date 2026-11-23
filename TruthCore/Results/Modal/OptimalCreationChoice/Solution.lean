module

public import TruthCore.Modal.OptimalCreationChoice
public import TruthCore.Results.Modal.SimplicityCollapse.Solution

@[expose] public section

namespace TruthCore.Results.Modal.OptimalCreationChoice
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.OptimalCreationChoice
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Results.Modal.SelectedEffectBridge
open TruthCore.Modal.SimplicityCollapse
  (optionalAct inefficaciousAct noCreation BeingCarriesAct)

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
  exact ⟨(fun _ _ => True.intro), hSound, hNecessary, hRealized, hLocal,
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

/-- The #555 profiles' remaining facts. Failed stability of `inefficaciousAct`
is composed from #555 `Core`: clause 2 would turn stability (with sound causes,
realized outputs and the actual output) into strict efficacy, which the
inefficacious clause denies. -/
theorem omissionStructureChecks : OmissionStructureControl := by
  have hSound : SoundDistinctCauses noCreation := by
    intro w x y h
    change w = false ∧ x = source ∧ y = firstEffect at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨Or.inl rfl, Or.inr ⟨rfl, rfl⟩, by decide⟩
  have hRealized : RealizedOutputs inefficaciousAct := by
    intro v _ x _ hx
    exact ⟨hx.1, rfl, hx.2⟩
  have hOptionalRealized : RealizedOutputs optionalAct := by
    intro v _ x _ hx
    exact ⟨hx.1, rfl, hx.2⟩
  have hLocal : LocallyDeterministic inefficaciousAct := by
    intro _ _ _ _ hx hy
    exact hx.2.trans hy.2.symm
  have hStable : StableActOutput optionalAct false () := by
    intro x hx v _ hp
    change v = false at hp
    subst v
    exact hx
  have hNotStable : ¬ StableActOutput inefficaciousAct false () := by
    intro h
    have core := TruthCore.Results.Modal.SimplicityCollapse.core
    exact core.2.2.2.2.1.2.2.2.1
      (core.2.1 _ _ _ inefficaciousAct false () firstEffect hSound hRealized h ⟨rfl, rfl⟩)
  have hNoExercise : ¬ ExercisesCausation noCreation true source := by
    rintro ⟨y, hy⟩
    exact Bool.noConfusion hy.1
  exact ⟨hSound, hRealized, hOptionalRealized, hLocal, hStable, hNotStable, hNoExercise⟩

/-- #555's `BeingCarriesAct` (the token is performed wherever the bearer
exists) fails on `threeWorldCreation` and `optionalAct` and holds on
`inefficaciousAct`. With a necessary bearer it yields `SameActEverywhere`
(#555 `Core`), so only the always-performed profile survives that reading. -/
theorem beingCarriesActApplication :
    ¬ BeingCarriesAct threeWorldCreation () ∧ ¬ BeingCarriesAct optionalAct () ∧
    BeingCarriesAct inefficaciousAct () := by
  refine ⟨?_, TruthCore.Results.Modal.SimplicityCollapse.core.2.2.2.2.2.2.2.1,
    fun _ _ => True.intro⟩
  intro h
  exact h none (Or.inl rfl) rfl

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
    OptimalOutputs optionalAct false ()
      soleCreatedCandidate tiedQuality := by
  intro v _
  constructor
  · intro hv
    exact ⟨firstEffect, ⟨hv, rfl⟩⟩
  · intro x hx
    change v = false ∧ x = firstEffect at hx
    rw [hx.2]
    exact soleCreatedOptimal

/-- All produced objects are optimal in the universal-performance alternative,
but at the omission world no output exists. -/
theorem universalOmissionOutputOptimal :
    ∀ v x, inefficaciousAct.output v () x →
      Optimal soleCreatedCandidate tiedQuality x := by
  intro v x hx
  change v = false ∧ x = firstEffect at hx
  rw [hx.2]
  exact soleCreatedOptimal

/-- Unique feasible optimum + worldwise optimality + SameActEverywhere do not
imply the positive-output-totality conjunct of `OptimalOutputs`.
This exactly isolates an extra premise of `uniqueOptimalStable`. -/
theorem universalOmissionNotTotal :
    ¬ OptimalOutputs inefficaciousAct false ()
      soleCreatedCandidate tiedQuality := by
  intro h
  obtain ⟨x, hx⟩ := (h true (Or.inr True.intro)).1 True.intro
  change true = false ∧ x = firstEffect at hx
  exact Bool.noConfusion hx.1

/-- Joint optimality controls on #555's profiles: unique created candidate,
optional exercise versus same act with omitted output. -/
theorem omissionChoiceChecks :
    Optimal soleCreatedCandidate tiedQuality firstEffect ∧
    (∀ x y, Optimal soleCreatedCandidate tiedQuality x →
      Optimal soleCreatedCandidate tiedQuality y → x = y) ∧
    OptimalOutputs optionalAct false () soleCreatedCandidate tiedQuality ∧
    (∀ v x, inefficaciousAct.output v () x →
      Optimal soleCreatedCandidate tiedQuality x) ∧
    ¬ OptimalOutputs inefficaciousAct false () soleCreatedCandidate tiedQuality := by
  exact ⟨soleCreatedOptimal, soleCreatedUnique, optionalOmissionOptimal,
    universalOmissionOutputOptimal, universalOmissionNotTotal⟩

end TruthCore.Results.Modal.OptimalCreationChoice
