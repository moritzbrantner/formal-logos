module

public import TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)

theorem sameGiverCriterionAtEsse {B P R : Type} (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hGiver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (hAscent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse) :
    SameGiverForkCriterion p MoreIn := by
  sorry

theorem sameGiverCriterion {B P R : Type} (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hGiver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading p.CausesIn MoreIn) :
    SameGiverForkCriterion p MoreIn := by
  sorry

theorem secondaryGiverControl : SecondaryGiverControl := by
  sorry

end TruthCore.Results.Aquinas.DeEnte.UniversalGiverFork
