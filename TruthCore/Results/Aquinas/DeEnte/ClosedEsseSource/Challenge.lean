import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
import TruthCore.Results.Causality.ConcreteRootAccess.Solution

/-! Conditional CCR transfer, on one fixed esse/essence dictionary. No
well-foundedness, asymmetry, efficient cause or world-grounding bridge is used. -/

namespace TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ConcreteRootAccess (RootAccess)
open TruthCore.Logic (ExcludedMiddle)

/-- Two actual beings imply the one-bearer population used below. -/
theorem populationOfTwo (p : Profile B P R) (h : TwoActualBeings p) :
    ActualEssePopulation p := by
  sorry

/-- CCR replaces unrestricted well-foundedness in the distinct-esse step. -/
theorem distinctSourceOfClosed (p : Profile B P R)
    (hC : ClosedActualEsseCollectionsRooted p)
    (hOther : DistinctEsseHasOtherActualCause p) (em : ExcludedMiddle) :
    EveryDistinctEsseHasEsseIsEssenceSource p := by
  sorry

/-- CCR, distinct-esse coverage, identity-bearer uniqueness, one actual
bearer and explicit excluded middle give the existing common-source endpoint. -/
theorem commonSourceOfClosed (p : Profile B P R)
    (hC : ClosedActualEsseCollectionsRooted p)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p) (hPop : ActualEssePopulation p)
    (em : ExcludedMiddle) : CommonEsseIsEssenceSource p := by
  sorry

/-- Unrestricted well-foundedness implies the weaker closed-collection premise. -/
theorem closedOfWF (p : Profile B P R) (h : NoInfiniteActualEsseCauseRegress p) :
    ClosedActualEsseCollectionsRooted p := by
  sorry

namespace Control

open TruthCore.Causality.ClosedGroundingRoots.Control

end Control

theorem controls : ClosedEsseControls := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource
