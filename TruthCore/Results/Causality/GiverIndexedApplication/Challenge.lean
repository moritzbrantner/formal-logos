import TruthCore.Causality.GiverIndexedApplication
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.GiverIndexedApplication
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Causality.Q44SourceSupply (ActualEsseCauseComposes)
open TruthCore.Causality.GiverIndexedApplication
open TruthCore.Logic (ExcludedMiddle)

theorem composeOfPerSe {B P R : Type} (f : Profile B P R) (AsCaused : B → B → Prop)
    (hEM : ExcludedMiddle) (hBridge : CausedEsseCauseCausesAsCaused f AsCaused)
    (hPerSe : PerSeComposition f AsCaused) : ActualEsseCauseComposes f := by
  sorry

theorem perSeOfApplication {B P R : Type} (f : Profile B P R) (AsCaused : B → B → Prop)
    (Through : B → B → B → Prop) (hCredit : AppliedGiverComposes f Through)
    (hAlign : EachGiverApplies f AsCaused Through) : PerSeComposition f AsCaused := by
  sorry

theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.GiverIndexedApplication
