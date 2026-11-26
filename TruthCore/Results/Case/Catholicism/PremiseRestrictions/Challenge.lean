import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
import TruthCore.Causality.ActualEuclidean
import TruthCore.Causality.CausalConcreteRivalBoundary
import TruthCore.Causality.NecessarySenseFork
import TruthCore.Latin.Aquinas.DeEnte.BoundedIdentityExercise
import TruthCore.Results.Aquinas.DeEnte.EsseSource.Solution
import TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle.Solution
import TruthCore.Results.Causality.PossibleCausalSourceNecessity.Solution
import TruthCore.Results.Causality.SurveyProductiveSource.Solution
import TruthCore.Results.Modal.ModalGrounding.Solution

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
    EsseInReIsConcrete ⟨f.ontic, f.concrete, grounds⟩ f.InAct f.esse := by
  sorry

/-- Read reflexivity on the same Ontic as the S5 bundle. -/
theorem actualReflexiveOfS5 {W B : Type} (m : Profile W B) (w : W)
    (hS5 : OnticFrameS5 m) : ActualReflexive m.ontic w := by
  sorry

/-- The bearer map and the identity test are identical on both sides. -/
theorem inhabitedOfFiniteNonempty {B P R E : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (bearer : E → B) (hFibres : ActualIdentityExerciseFibresFiniteNonempty p bearer) :
    ActualIdentityExerciseFibresInhabited p bearer := by
  sorry

/-- Well-foundedness excludes an identity return. The existing no-return
argument can start with any actual bearer, including an identity bearer. -/
theorem commonSourceOfOne {B P R : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hSource : EveryDistinctEsseHasEsseIsEssenceSource p)
    (hOne : AtMostOneEsseIsEssence p) (hPopulation : ActualEssePopulation p)
    (hRegress : NoInfiniteActualEsseCauseRegress p)
    (hEM : ExcludedMiddle) : CommonEsseIsEssenceSource p := by
  sorry

/-- Sourcehood and productive activity are tested at the accessible witness
world. Only existence and necessity are transported to the selected world. -/
theorem productiveSourceAt {W B : Type} (p : Profile W B) (w : W)
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple p.ontic)
    (hEuclidean : EuclideanAt p.ontic.frame w) (hReflexive : ActualReflexive p.ontic w)
    (hPossible : PossiblyFailedHeadlessCoverage p.ontic w)
    (hProductive : ProductiveSources p.ontic w)
    (hConcrete : AccessibleCausersConcrete p.ontic p.concrete w) :
    NecessaryConcreteAt p w := by
  sorry

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
  sorry

end TruthCore.Results.Case.Catholicism.PremiseRestrictions
