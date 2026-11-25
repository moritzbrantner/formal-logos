import TruthCore.Causality.ReflectiveComprehension

namespace TruthCore.Results.Causality.ReflectiveComprehension

open TruthCore.Causality.ComprehensionByMeasure
open TruthCore.Causality.ReflectiveComprehension
open TruthCore.Causality.SoleEsseGiver
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

theorem ordersAct {B D : Type} [Preorder D] (M : Measures B D)
    (hKnowable : KnowableInsofarAsInAct M) (hWithin : KnowingWithinKnowersAct M) :
    ComprehensionOrdersAct M := by
  sorry

theorem participantBound {B P R D : Type} [Preorder D] (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (s : B) (degree : R → B → D) (M : Measures B D)
    (hSource : SoleEssentialGiver f Participated OwnBeing s)
    (hCompr : ComprehendsParticipants f Participated M s)
    (hOrder : ComprehensionOrdersAct M)
    (hScale : MeasuredActAgreesWithEsse f degree M) :
    BoundsParticipatedEsse f Participated degree s := by
  sorry

theorem reflectiveComparison {B P R D : Type} [Preorder D] (f : Profile B P R)
    (degree : R → B → D) (M : Measures B D)
    (hKnowable : KnowableInsofarAsInAct M) (hWithin : KnowingWithinKnowersAct M)
    (hScale : MeasuredActAgreesWithEsse f degree M) :
    ReflectiveComparison f degree M := by
  sorry

theorem controls : TruthCore.Causality.ReflectiveComprehension.Control.Controls := by
  sorry

end TruthCore.Results.Causality.ReflectiveComprehension
