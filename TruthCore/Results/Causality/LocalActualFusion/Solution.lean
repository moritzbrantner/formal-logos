module

public import TruthCore.Causality.LocalActualFusion

@[expose] public section

namespace TruthCore.Results.Causality.LocalActualFusion

open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.LocalActualFusion
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)
open TruthCore.Mereology.FusionNoNecessaryParts (NoNecessaryPartsAt)

/-- The reductio inspects parts of the selected sum and of its actual causes. -/
theorem necessaryConcrete {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hFusion : ActualFusionAt m.ontic w sum)
    (hParts : SelectedFusionPartsExistAt m.ontic w sum)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m.ontic w)
    (hActual : CausesHaveActualEndpointsAt m.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt m.ontic w)
    (hConcrete : SelectedActualFusionPartsConcreteAt m w sum) :
    NecessaryConcreteAt m w := by
  apply Classical.byContradiction
  intro hNone
  have noNecessaryPart : ∀ p, SelectedFusionPart m.ontic w sum p →
      ¬ TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w p := by
    intro p hp hn
    have hExists := hParts hFusion.1 p hp
    exact hNone ⟨p, hConcrete p hExists hp, hExists, hn⟩
  obtain ⟨c, hc⟩ := hCausal sum hFusion.1 (fun p hp => noNecessaryPart p (Or.inl hp))
  have hcActual := (hActual c sum hc).1
  have hcNoParts : NoNecessaryPartsAt m.ontic w c :=
    fun p hp => noNecessaryPart p (Or.inr ⟨c, hcActual, hc, hp⟩)
  exact hNonoverlap c sum hc ⟨c, le_refl c, hFusion.2.1 c ⟨hcActual, hcNoParts⟩⟩

/-- The original global part-existence policy supplies the localized policy
without a change of carrier, sum, world or cause relation. -/
theorem partsExistOfGlobal {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hParts : ActualPartsExistAt m.ontic w) :
    SelectedFusionPartsExistAt m.ontic w sum := by
  intro hSum p hp
  rcases hp with hPart | ⟨c, hActual, _, hPart⟩
  · exact hParts sum p hSum hPart
  · exact hParts c p hActual hPart

theorem concreteOfGlobal {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    SelectedActualFusionPartsConcreteAt m w sum :=
  fun p hp _ => hConcrete p hp

/-- A concretely instantiated local region leaves an unrelated actual
contingent abstract individual outside the global calibration. -/
theorem calibrationStrictness : Control.CalibrationStrictness := by
  refine ⟨?_, ?_⟩
  · intro p _ hp
    rcases hp with hPart | ⟨c, _, hc, _⟩
    · cases p with
      | false => rfl
      | true => exact ((by decide : ¬ (true : Bool) ≤ false) hPart).elim
    · exact hc.elim
  · intro h
    have hTrue := h true (Or.inl rfl)
    simp [Control.strictProfile] at hTrue

theorem profileCalibrationOfExisting {W B : Type} (m : Profile W B) (w : W)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    ProfileExistentConcreteAt m w :=
  hConcrete

theorem localCalibrationOfProfile {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hConcrete : ProfileExistentConcreteAt m w) :
    SelectedActualFusionPartsConcreteAt m w sum :=
  concreteOfGlobal m w sum hConcrete

theorem calibrationExactDifference : CalibrationExactDifference := by
  intro W B _ m w sum
  change ProfileExistentConcreteAt m w ↔
    SelectedActualFusionPartsConcreteAt m w sum ∧ OutsideFusionActualConcreteAt m w sum
  constructor
  · intro h
    exact ⟨localCalibrationOfProfile m w sum h, fun p hp _ => h p hp⟩
  · rintro ⟨hLocal, hOutside⟩ p hp
    by_cases hPart : SelectedFusionPart m.ontic w sum p
    · exact hLocal p hp hPart
    · exact hOutside p hp hPart

end TruthCore.Results.Causality.LocalActualFusion
