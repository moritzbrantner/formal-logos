import TruthCore.Causality.Q44EssentialSource

namespace TruthCore.Results.Causality.Q44EssentialSource
open TruthCore.Causality.Q44EssentialSource
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Latin.Aquinas.DeEnte (AtMostOneEsseIsEssence)
open TruthCore.Causality.Round2PerfectionPrimacy (OthersThanPrimaryParticipateEsse)
open TruthCore.Causality.CreatureSenses (IsCreatureOfUniversalCause)
open TruthCore.Latin.Aquinas.SummaTheologiae (OthersAreCreaturesReading CausesAllInGenus)

/-- Source selection through the existing De ente at-most-one statement,
with its identity dictionary and one selected actual identity witness explicit. -/
theorem sourcesSelected {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B)
    (hIdentity : RelevantEssentialSourceHasIdentity f Participated OwnBeing)
    (hOne : AtMostOneEsseIsEssence f)
    (hSelected : SelectedActualIdentity f p) :
    RelevantEssentialSourcesSelected f Participated OwnBeing p := by
  sorry

/-- Each other thing has a selected own-being source of esse. That same p
therefore causes every other actual being and makes each other thing CREATURE_1.
No GOD_4 dictionary, maximality or claim of efficiency is used. -/
theorem othersAreCreatures {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (p : B)
    (hOthers : OthersThanPrimaryParticipateEsse Participated p)
    (hSource : ParticipatedHasEssentialSource f Participated OwnBeing)
    (hSelection : RelevantEssentialSourcesSelected f Participated OwnBeing p) :
    OthersAreCreaturesReading
      (IsCreatureOfUniversalCause f.InAct f.CausesIn f.esse) p := by
  sorry

open Control.Three in

open Control.Three in

open Control.Three in

open Control.Three in

open Control in
/-- Closed finite interpretations, not metaphysical possibility claims. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.Q44EssentialSource
