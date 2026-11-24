import TruthCore.Causality.SoleEsseGiver

namespace TruthCore.Results.Causality.SoleEsseGiver

open TruthCore.Causality.SoleEsseGiver
open TruthCore.Causality.Q44EssentialSource
open TruthCore.Causality.CartesianAdequacy (AtLeastAsMuchDegreeInTotalCause)
open TruthCore.Causality.EsseCauseEfficiency (EfficiencyProfile)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.Round2PerfectionPrimacy (OthersThanPrimaryParticipateEsse)
open TruthCore.Causality.TermSenseForks (SomeBeingGreatestInBeing)
open TruthCore.Logic (ExcludedMiddle)

theorem soleGiverOfSelection {B P R : Type} (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (s : B)
    (hExists : ActualParticipantExists f Participated)
    (hLocal : ParticipatedHasEssentialSource f Participated OwnBeing)
    (hOne : RelevantEssentialSourcesSelected f Participated OwnBeing s) :
    SoleEssentialGiver f Participated OwnBeing s := by
  sorry

theorem boundOfAdequacy {B P R D : Type} [Preorder D] (q : EfficiencyProfile B P R)
    (Participated OwnBeing : B → Prop) (s : B)
    (Total : B → B → R → Prop) (degree : R → B → D)
    (hSource : SoleEssentialGiver q.toProfile Participated OwnBeing s)
    (hWhole : EssentialGivingIsEfficientAndTotal q Participated OwnBeing Total)
    (hAdequate : AtLeastAsMuchDegreeInTotalCause (efficientGrades q) Total degree) :
    BoundsParticipatedEsse q.toProfile Participated degree s := by
  sorry

theorem greatestOfCoverage {B P R D : Type} [Preorder D] (f : Profile B P R)
    (Participated : B → Prop) (s : B) (degree : R → B → D)
    (hBound : BoundsParticipatedEsse f Participated degree s)
    (hCover : OthersThanPrimaryParticipateEsse Participated s)
    (hEM : ExcludedMiddle) :
    SomeBeingGreatestInBeing f.InAct f.esse (degree f.esse) := by
  sorry

theorem equalDegree : EqualDegreeControl := by
  sorry

end TruthCore.Results.Causality.SoleEsseGiver
