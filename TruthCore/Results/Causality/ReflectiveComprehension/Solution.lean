module

public import TruthCore.Causality.ReflectiveComprehension

@[expose] public section
namespace TruthCore.Results.Causality.ReflectiveComprehension

open TruthCore.Causality.ComprehensionByMeasure
open TruthCore.Causality.ReflectiveComprehension
open TruthCore.Causality.SoleEsseGiver
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

theorem ordersAct {B D : Type} [Preorder D] (M : Measures B D)
    (hKnowable : KnowableInsofarAsInAct M) (hWithin : KnowingWithinKnowersAct M) :
    ComprehensionOrdersAct M := by
  intro s x ⟨d, hd, hfull⟩
  exact (hKnowable x).trans (hfull.trans (hWithin s x d hd))

theorem reciprocalBounds {B D : Type} [Preorder D] (M : Measures B D)
    (hOrder : ComprehensionOrdersAct M) (s x : B)
    (hForward : ComprehendsByMeasure M s x) (hReverse : ComprehendsByMeasure M x s) :
    M.actDegree x ≤ M.actDegree s ∧ M.actDegree s ≤ M.actDegree x :=
  ⟨hOrder s x hForward, hOrder x s hReverse⟩

theorem participantBound {B P R D : Type} [Preorder D] (f : Profile B P R)
    (Participated OwnBeing : B → Prop) (s : B) (degree : R → B → D) (M : Measures B D)
    (hSource : SoleEssentialGiver f Participated OwnBeing s)
    (hCompr : ComprehendsParticipants f Participated M s)
    (hOrder : ComprehensionOrdersAct M)
    (hScale : MeasuredActAgreesWithEsse f degree M) :
    BoundsParticipatedEsse f Participated degree s := by
  obtain ⟨w, hw, hp⟩ := hSource.1
  have hs := (hSource.2 w hw hp).1.2.1
  refine ⟨hs, ?_⟩
  intro x ha hx
  exact (hScale x ha).1.trans ((hOrder s x (hCompr x ha hx)).trans (hScale s hs).2)

/-- Independent knowledge of an object-side ceiling suffices even for a
noncognitive recipient. Establishing the strict cut is the applicability burden. -/
theorem strictAboveKnowability {B P R D : Type} [Preorder D] (f : Profile B P R)
    (degree : R → B → D) (M : Measures B D)
    (hKnowable : KnowableInsofarAsInAct M) (hWithin : KnowingWithinKnowersAct M)
    (hScale : MeasuredActAgreesWithEsse f degree M)
    (x s y : B) (b : D) (hx : f.InAct x f.esse) (hs : f.InAct s f.esse)
    (hknows : M.KnowsAt s y b) (hlt : M.knowability x < b) :
    degree f.esse x < degree f.esse s :=
  lt_of_le_of_lt ((hScale x hx).1.trans (hKnowable x))
    (lt_of_lt_of_le hlt ((hWithin s y b hknows).trans (hScale s hs).2))

theorem reflectiveComparison {B P R D : Type} [Preorder D] (f : Profile B P R)
    (degree : R → B → D) (M : Measures B D)
    (hKnowable : KnowableInsofarAsInAct M) (hWithin : KnowingWithinKnowersAct M)
    (hScale : MeasuredActAgreesWithEsse f degree M) :
    ReflectiveComparison f degree M := by
  intro x a hx hself hfull
  have ha := hWithin x x a hself
  have hxle := (hKnowable x).trans hfull
  refine ⟨⟨hxle, ha⟩, ⟨hfull, ha.trans (hKnowable x)⟩, ?_⟩
  intro s y b hs hknows hlt
  exact strictAboveKnowability f degree M hKnowable hWithin hScale x s y b hx hs hknows
    (lt_of_le_of_lt hfull hlt)

theorem controls : TruthCore.Causality.ReflectiveComprehension.Control.Controls := by
  unfold TruthCore.Causality.ReflectiveComprehension.Control.Controls
  dsimp only [TruthCore.Causality.ReflectiveComprehension.Control.tied,
    TruthCore.Causality.ReflectiveComprehension.Control.lowerSource,
    TruthCore.Causality.ReflectiveComprehension.Control.asymmetric,
    TruthCore.Causality.ReflectiveComprehension.Control.full,
    TruthCore.Causality.ReflectiveComprehension.Control.profile,
    SoleEssentialGiver, ActualParticipantExists, MeasuredActAgreesWithEsse, ComprehendsParticipants,
    KnowableInsofarAsInAct, KnowingWithinKnowersAct, PowerOfKnowingBoundedBy,
    ComprehendsByMeasure, TruthCore.Causality.IntentionalExemplarExtension.UnderstandsActualEffects,
    TruthCore.Causality.IntentionalExemplarExtension.Control.frame,
    TruthCore.Causality.IntentionalExemplarExtension.Control.about,
    TruthCore.Causality.IntentionalExemplarExtension.Control.correct,
    TruthCore.Causality.IntentionalExemplarExtension.Control.sourceTakesUp,
    TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.Control.causesIn]
  repeat' apply And.intro
  all_goals decide

end TruthCore.Results.Causality.ReflectiveComprehension
