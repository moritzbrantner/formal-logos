import TruthCore.Latin.Aquinas.DeEnte.IdentitySupplierSingleton
import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution

namespace TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.DeEnte.ReceivedOrUnderived
open TruthCore.Latin.Aquinas.DeEnte.IdentitySupplierSingleton
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile DistinctEsseAt)
open TruthCore.Logic (ExcludedMiddle)

/-- The ordinary uniqueness premise bounds each recipient's identity ancestors
even when the recipient has infinitely many other ancestors. -/
theorem finiteIdentityAncestorsOfUniqueness (p : Profile B P R)
    (one : AtMostOneEsseIsEssence p) : ActualIdentityAncestorSetsFinite p := by
  sorry

/-- Select an identity bearer from one actual bearer, then identify every
incoming supplier as a point on a forbidden return path. -/
theorem commonSourceOfNoIdentityReturn (p : Profile B P R)
    (ancestry : EveryDistinctEsseHasEsseIsEssenceSource p)
    (one : AtMostOneEsseIsEssence p) (population : ActualEssePopulation p)
    (noReturn : ActualIdentityAncestryAcyclic p) (em : ExcludedMiddle) :
    CommonEsseIsEssenceSource p := by
  sorry

/-- Under uniqueness, every return would end in a supplier edge into the very
bearer whose incoming supply the common-source conclusion excludes. -/
theorem noIdentityReturnOfCommonSource (p : Profile B P R)
    (one : AtMostOneEsseIsEssence p) (source : CommonEsseIsEssenceSource p) :
    ActualIdentityAncestryAcyclic p := by
  sorry

/-- The existing rooted infinite profile satisfies all the application
premises while failing unrestricted well-foundedness. -/
theorem commonSourceWithEndlessBranch (em : ExcludedMiddle) :
    ∃ p : Profile (Option Nat) Bool Unit, EveryDistinctEsseHasEsseIsEssenceSource p ∧
      AtMostOneEsseIsEssence p ∧ ActualEssePopulation p ∧ ActualIdentityAncestryAcyclic p ∧
      CommonEsseIsEssenceSource p ∧ ¬ NoInfiniteActualEsseCauseRegress p := by
  sorry

/-- One value of represented essence and one successor law are compatible
with infinitely many actual identity ancestors of the same distinct
recipient, with incoming supply at each identity and no root. -/
theorem identitySupplierSingletonCountermodel : SingletonEssenceValueWithInfiniteIdentitySuppliers := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.IdentitySourceCycle
