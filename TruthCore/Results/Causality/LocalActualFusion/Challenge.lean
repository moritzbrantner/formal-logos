import TruthCore.Causality.LocalActualFusion

namespace TruthCore.Results.Causality.LocalActualFusion

open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.LocalActualFusion
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)

theorem necessaryConcrete {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hFusion : ActualFusionAt m.ontic w sum)
    (hParts : SelectedFusionPartsExistAt m.ontic w sum)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m.ontic w)
    (hActual : CausesHaveActualEndpointsAt m.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt m.ontic w)
    (hConcrete : NecessarySelectedFusionPartsConcreteAt m w sum) :
    NecessaryConcreteAt m w := by
  sorry

theorem partsExistOfGlobal {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hParts : ActualPartsExistAt m.ontic w) :
    SelectedFusionPartsExistAt m.ontic w sum := by
  sorry

theorem concreteOfGlobal {W B : Type} [PartialOrder B]
    (m : Profile W B) (w : W) (sum : B)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w) :
    NecessarySelectedFusionPartsConcreteAt m w sum := by
  sorry

theorem calibrationStrictness : Control.CalibrationStrictness := by
  sorry

end TruthCore.Results.Causality.LocalActualFusion
