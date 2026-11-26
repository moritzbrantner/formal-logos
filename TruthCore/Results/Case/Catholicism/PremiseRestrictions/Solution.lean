module

public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
public import TruthCore.Causality.ActualEuclidean
public import TruthCore.Causality.CausalConcreteRivalBoundary
public import TruthCore.Causality.NecessarySenseFork
public import TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
public import TruthCore.Results.Aquinas.DeEnte.EsseSource.Solution
public import TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle.Solution
public import TruthCore.Results.Causality.PossibleCausalSourceNecessity.Solution
public import TruthCore.Results.Causality.SurveyProductiveSource.Solution
public import TruthCore.Results.Modal.ModalGrounding.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.PremiseRestrictions

open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.NecessarySenseFork (OnticFrameS5)
open TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.SurveyProductiveSource
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ActualIdentityExerciseLifting
open TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal.ModalGrounding

/-- Keep the calibrated ontic frame, concrete predicate and esse interpretation.
The destination profile's independently supplied grounding relation is unused. -/
theorem concreteOfCalibration (f : TruthCore.Causality.CausalConcreteRivalBoundary.Frame)
    (grounds : f.World → f.Being → f.Being → Prop)
    (hCalibration : TruthCore.Causality.CausalConcreteRivalBoundary.Calibration f) :
    EsseInReIsConcrete ⟨f.ontic, f.concrete, grounds⟩ f.InAct f.esse :=
  fun x hx => (hCalibration x).mpr hx

/-- Read reflexivity on the same Ontic as the S5 bundle. -/
theorem actualReflexiveOfS5 {W B : Type} (m : Profile W B) (w : W)
    (hS5 : OnticFrameS5 m) : ActualReflexive m.ontic w :=
  hS5.1 w

/-- The bearer map and the identity test are identical on both sides. -/
theorem inhabitedOfFiniteNonempty {B P R E : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (bearer : E → B) (hFibres : ActualIdentityExerciseFibresFiniteNonempty p bearer) :
    ActualIdentityExerciseFibresInhabited p bearer :=
  fun r hr hi => (hFibres r hr hi).2

/-- Well-foundedness excludes an identity return. The existing no-return
argument can start with any actual bearer, including an identity bearer. -/
theorem commonSourceOfOne {B P R : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hSource : EveryDistinctEsseHasEsseIsEssenceSource p)
    (hOne : AtMostOneEsseIsEssence p) (hPopulation : ActualEssePopulation p)
    (hRegress : NoInfiniteActualEsseCauseRegress p)
    (hEM : ExcludedMiddle) : CommonEsseIsEssenceSource p :=
  TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle.commonSourceOfNoIdentityReturn
    p hSource hOne hPopulation
    (fun r _ _ => TruthCore.Results.Aquinas.DeEnte.EsseSource.not_transGen_self hRegress r) hEM

/-- Sourcehood and productive activity are tested at the accessible witness
world. Only existence and necessity are transported to the selected world. -/
theorem productiveSourceAt {W B : Type} (p : Profile W B) (w : W)
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple p.ontic)
    (hEuclidean : EuclideanAt p.ontic.frame w) (hReflexive : ActualReflexive p.ontic w)
    (hPossible : PossiblyFailedHeadlessCoverage p.ontic w)
    (hProductive : ProductiveSources p.ontic w)
    (hConcrete : AccessibleCausersConcrete p.ontic p.concrete w) :
    NecessaryConcreteAt p w := by
  obtain ⟨v, hwv, hFailure⟩ := hPossible
  obtain ⟨s, hs⟩ :=
    TruthCore.Results.Causality.HeadlessCausalAncestry.source_of_not_headless_coverage
      (TruthCore.Causality.WorldSourceRegress.actualGraph p.ontic v) hEM hFailure
  have hSource :=
    (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff p.ontic v s).mp hs
  have hNecessary :=
    TruthCore.Results.Causality.PossibleCausalSourceNecessity.source_necessary_at
      p.ontic v s.val hEM hCausal s.property hSource
  have hOrigin := TruthCore.Causality.ActualEuclidean.necessaryAtOrigin
    p.ontic w v s.val hEuclidean hReflexive hwv hNecessary
  obtain ⟨y, hEdge⟩ := hProductive v hwv s.val s.property hSource
  exact ⟨s.val, hConcrete v hwv s.val y hEdge, hOrigin.1, hOrigin.2⟩

/-- Keep the global absence content of the power and restrict only the
accessibility premise. The actual holder would be contingent at its
initiating history if it were missing at any successor of the selected world. -/
theorem globalAbsencePowerAt {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hEM : ExcludedMiddle) (hEuclidean : EuclideanAt F.history.ontic.frame w)
    (hGround : GlobalAbsenceGrounded F PowerFor concrete w)
    (hInit : GlobalAbsenceInitiatorPresent F PowerFor concrete w)
    (hConcrete : GlobalAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hPossible : PossiblyNoContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w) :
    NecessaryConcreteGlobalAbsencePowerAt F PowerFor concrete w := by
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨y, hyw, hPower⟩ := hGround hPossible (fun h => h x hxc hx)
  obtain ⟨v, hwv, hAbsent, hyv⟩ := hInit y hPower
  have hyc := hConcrete y hPower
  refine ⟨y, hyc, hyw, ?_, hPower⟩
  intro u hwu
  rcases hEM (F.history.ontic.ExistsAt u y) with hPresent | hMissing
  · exact hPresent
  · exact (hAbsent y hyc ⟨hyv, u, hEuclidean v u hwv hwu, hMissing⟩).elim

end TruthCore.Results.Case.Catholicism.PremiseRestrictions
