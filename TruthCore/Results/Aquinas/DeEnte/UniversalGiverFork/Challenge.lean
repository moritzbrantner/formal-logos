import TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork

namespace TruthCore.Results.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)

theorem sameGiverCriterion {B P R : Type} (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hGiver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading p.CausesIn MoreIn) :
    SameGiverForkCriterion p MoreIn := by
  sorry

theorem secondaryGiverControl : SecondaryGiverControl := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.UniversalGiverFork
