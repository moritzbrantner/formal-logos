import TruthCore.Case.Catholicism.AttributesFromEsse
import TruthCore.Models.FiniteSupport
import TruthCore.Results.Case.Catholicism.GodIsOneFromEsse.Solution
import TruthCore.Results.Causality.ClassicalGodAssembly.Solution
import TruthCore.Results.Causality.TermSenseForks4.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution
import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic

namespace TruthCore.Results.Case.Catholicism.AttributesFromEsse
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.AttributesFromEsse
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.GodMaximalCausal (GodCausesBeingOfAllOthers)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Logic (ExcludedMiddle)

theorem perfectFromGodCause {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hCause : GodCausesBeingOfAllOthers IsGod F.CausesIn F.esse)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse)
    (hEM : ExcludedMiddle) : PerfectInFrame F IsGod := by
  sorry

theorem goodFromGodCause {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (GoodIn : B → R → Prop)
    (hCause : GodCausesBeingOfAllOthers IsGod F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hGood : GoodnessIsActualityReading GoodIn F.InAct)
    (hTransfer : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse) :
    GodIsSupremelyGood IsGod F.InAct GoodIn F.CausesIn F.esse := by
  sorry

theorem oneFromSource {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : ExcludedMiddle) : GodIsOne IsGod := by
  sorry

theorem perfectFromSource {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : ExcludedMiddle)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) : PerfectInFrame F IsGod := by
  sorry

theorem goodFromSource {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (GoodIn : B → R → Prop)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : ExcludedMiddle)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hGood : GoodnessIsActualityReading GoodIn F.InAct)
    (hTransfer : UniversalCauseTransfersPerfections F.InAct F.CausesIn F.esse) :
    GodIsSupremelyGood IsGod F.InAct GoodIn F.CausesIn F.esse := by
  sorry

theorem fromNine (σ : Signature) {W T R : Type} (F : GradesFrame W σ.Being T R)
    (GoodIn : σ.Being → R → Prop)
    (Composite Infinite Immutable Eternal HasIntellect HasWill : σ.Being → Prop)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect F.InAct)
      (IsSupremelyGood F.InAct GoodIn F.CausesIn F.esse) (IsTheOneGod σ.IsGod)
      Infinite Immutable Eternal HasIntellect HasWill)
    (hSimple : GodIsSimple σ.IsGod Composite) (hPerfect : PerfectInFrame F σ.IsGod)
    (hGood : GodIsSupremelyGood σ.IsGod F.InAct GoodIn F.CausesIn F.esse)
    (hOne : GodIsOne σ.IsGod) (hInfinite : GodIsInfinite σ.IsGod Infinite)
    (hImmutable : GodIsImmutable σ.IsGod Immutable) (hEternal : GodIsEternal σ.IsGod Eternal)
    (hIntellect : GodHasIntellect σ.IsGod HasIntellect) (hWill : GodHasWill σ.IsGod HasWill) :
    GodHasClassicalAttributes σ := by
  sorry

theorem fromSource (σ : Signature) {W T Respect : Type} {Principle : Type}
    (F : GradesFrame W σ.Being T Respect)
    (InPotency GoodIn : σ.Being → Respect → Prop)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect F.InAct)
      (IsSupremelyGood F.InAct GoodIn F.CausesIn F.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod F.InAct F.MoreIn F.esse)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn F.InAct)
    (hPerfections : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing F.InAct F.MoreIn F.esse F.PriorSimply)
    (hPrior : ClassicalAttributesLocalLogic.IndependentPriority F.InAct InPotency F.PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading F.InAct InPotency)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf F.PriorSimply)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill) :
    GodHasClassicalAttributes σ := by
  sorry

theorem fromGodCause (σ : Signature) {W T Respect : Type} {Principle : Type}
    (F : GradesFrame W σ.Being T Respect)
    (InPotency GoodIn : σ.Being → Respect → Prop)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect F.InAct)
      (IsSupremelyGood F.InAct GoodIn F.CausesIn F.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod F.InAct F.MoreIn F.esse)
    (hCause : GodCausesBeingOfAllOthers σ.IsGod F.CausesIn F.esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn F.InAct)
    (hPerfections : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing F.InAct F.MoreIn F.esse F.PriorSimply)
    (hPrior : ClassicalAttributesLocalLogic.IndependentPriority F.InAct InPotency F.PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading F.InAct InPotency)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf F.PriorSimply)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill) :
    GodHasClassicalAttributes σ := by
  sorry

theorem sameSignatureConsumers (σ : Signature) {W T Respect : Type} {Principle : Type}
    (F : GradesFrame W σ.Being T Respect)
    (InPotency GoodIn : σ.Being → Respect → Prop)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect F.InAct)
      (IsSupremelyGood F.InAct GoodIn F.CausesIn F.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod F.InAct F.MoreIn F.esse)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn F.InAct)
    (hPerfections : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing F.InAct F.MoreIn F.esse F.PriorSimply)
    (hPrior : ClassicalAttributesLocalLogic.IndependentPriority F.InAct InPotency F.PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading F.InAct InPotency)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf F.PriorSimply)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill)
    (hFull : GodNamesTheFullyDescribedPrinciple F.InAct F.MoreIn F.CausesIn F.esse ComponentOf σ.IsGod)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    UniqueClassicalGodExists σ ∧ CatholicismTrue σ := by
  sorry

set_option synthInstance.maxSize 2048 in
theorem controls : Control.Checks := by
  sorry

end TruthCore.Results.Case.Catholicism.AttributesFromEsse
