module

public import TruthCore.Case.Catholicism.AttributesFromEsse
public import TruthCore.Models.FiniteSupport
public import TruthCore.Results.Case.Catholicism.GodIsOneFromEsse.Solution
public import TruthCore.Results.Causality.ClassicalGodAssembly.Solution
public import TruthCore.Results.Causality.TermSenseForks4.Solution
public import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution
public import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic

@[expose] public section

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
  intro g hg x r hx
  rcases hEM (x = g) with he | hn
  · exact he ▸ hx
  · exact hPre g x r (hCause g x hg hn) hx

theorem goodFromGodCause {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (GoodIn : B → R → Prop)
    (hCause : GodCausesBeingOfAllOthers IsGod F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hGood : GoodnessIsActualityReading GoodIn F.InAct)
    (hTransfer : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse) :
    GodIsSupremelyGood IsGod F.InAct GoodIn F.CausesIn F.esse := by
  intro g hg
  exact ⟨(hGood g F.esse).mpr (hMax g hg).1,
    fun x r hn hx => hTransfer g x r (hCause g x hg hn) hx⟩

private theorem namedSource {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : ExcludedMiddle) :
    ∃ m, (∀ g, IsGod g → g = m) ∧ CausesAllInGenus F.InAct F.CausesIn F.esse m := by
  obtain ⟨m, _, hAll⟩ := hSource
  refine ⟨m, ?_, hAll⟩
  intro g hg
  rcases hEM (g = m) with he | hn
  · exact he
  · have hm := hMax g hg
    exact (hm.2 m (hAscent m g F.esse (Ne.symm hn) (hAll g hn hm.1))).elim

theorem oneFromSource {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : ExcludedMiddle) : GodIsOne IsGod := by
  obtain ⟨_, hPin, _⟩ := namedSource F IsGod hSource hMax hAscent hEM
  intro g hg k hk
  exact (hPin k hk).trans (hPin g hg).symm

theorem perfectFromSource {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hSource : MaximeEnsCausesBeingOfAllReading F.InAct F.MoreIn F.CausesIn F.esse)
    (hMax : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : ExcludedMiddle)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) : PerfectInFrame F IsGod := by
  obtain ⟨m, hPin, hAll⟩ := namedSource F IsGod hSource hMax hAscent hEM
  intro g hg x r hx
  obtain rfl := hPin g hg
  rcases hEM (x = g) with he | hn
  · exact he ▸ hx
  · exact hPre g x r (hAll x hn (hBeing x r hx)) hx

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
  obtain ⟨m, hPin, hAll⟩ := namedSource F IsGod hSource hMax hAscent hEM
  intro g hg
  obtain rfl := hPin g hg
  exact ⟨(hGood g F.esse).mpr (hMax g hg).1,
    fun x r hn hx => hTransfer g hAll x r hn (hAll x hn (hBeing x r hx)) hx⟩

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
  intro g hg
  exact classicalAttributesFromNine σ _ _ _ _ _ _ _ _ _ hSuffice g
    ⟨hSimple g hg, hPerfect g hg, hGood g hg, hOne g hg, hInfinite g hg,
      hImmutable g hg, hEternal g hg, hIntellect g hg, hWill g hg⟩

private theorem finishSix (σ : Signature) {W T Respect : Type} {Principle : Type}
    (F : GradesFrame W σ.Being T Respect)
    (InPotency GoodIn : σ.Being → Respect → Prop)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect F.InAct)
      (IsSupremelyGood F.InAct GoodIn F.CausesIn F.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod F.InAct F.MoreIn F.esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse)
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
    (hOne : GodIsOne σ.IsGod) (hPerfect : PerfectInFrame F σ.IsGod)
    (hGood : GodIsSupremelyGood σ.IsGod F.InAct GoodIn F.CausesIn F.esse) :
    GodHasClassicalAttributes σ := by
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple σ.IsGod
    Composite F.InAct F.MoreIn F.CausesIn F.esse hMaximal hUniting hCauseMore
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    σ.IsGod InPotency F.InAct F.MoreIn F.esse F.PriorSimply hMaximal hFirstBeing hPrior hNotBoth
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal σ.IsGod
    Eternal InPotency F.InAct F.MoreIn F.esse F.PriorSimply hMaximal hFirstBeing hPrior hNotBoth hEternity
  have hInfinite := TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.godIsInfinite
    σ.IsGod Composite ComposedOfMatterAndForm Infinite essenceOf esseOf F.InAct F.MoreIn F.CausesIn F.esse
    hMaximal hUniting hCauseMore hKinds hEM hInfinity
  have hIntellect := TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect
    σ.IsGod Composite ComposedOfMatterAndForm HasIntellect ComponentOf F.PriorSimply essenceOf esseOf
    F.InAct F.MoreIn F.CausesIn F.esse hMaximal hUniting hCauseMore hKinds hNoComponent hFirstBeing
    hImmaterial
  have hWill := TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.godHasWill σ.IsGod Composite
    ComposedOfMatterAndForm HasIntellect HasWill ComponentOf F.PriorSimply essenceOf esseOf F.InAct F.MoreIn
    F.CausesIn F.esse hMaximal hUniting hCauseMore hKinds hNoComponent hFirstBeing hImmaterial
    hWillFollows
  exact fromNine σ F GoodIn Composite Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill
    hSuffice hSimple hPerfect hGood hOne hInfinite hImmutable hEternal hIntellect hWill

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
  have hOne := oneFromSource F σ.IsGod hSource hMaximal hCauseMore hEM
  have hPerfect := perfectFromSource F σ.IsGod hSource hMaximal hCauseMore hEM hBeing hPreexist
  have hGood := goodFromSource F σ.IsGod GoodIn hSource hMaximal hCauseMore hEM hBeing hGoodness
    (fun c _ x r _ => hPerfections c x r)
  exact finishSix σ F InPotency GoodIn ComponentOf Composite ComposedOfMatterAndForm Infinite
    Eternal HasIntellect HasWill essenceOf esseOf hSuffice hMaximal hCauseMore hEM hUniting
    hFirstBeing hPrior hNotBoth hKinds hInfinity hEternity hNoComponent hImmaterial hWillFollows
    hOne hPerfect hGood

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
  have hOne := TruthCore.Results.Case.Catholicism.GodIsOneFromEsse.oneFromGodMaximal
    σ.IsGod F.InAct F.MoreIn F.CausesIn F.esse hMaximal
    (fun m hm c hn hc => hm.2 c (hCauseMore c m F.esse hn hc)) hCause hEM
  have hPerfect := perfectFromGodCause F σ.IsGod hCause hPreexist hEM
  have hGood := goodFromGodCause F σ.IsGod GoodIn hCause hMaximal hGoodness hPerfections
  exact finishSix σ F InPotency GoodIn ComponentOf Composite ComposedOfMatterAndForm Infinite
    Eternal HasIntellect HasWill essenceOf esseOf hSuffice hMaximal hCauseMore hEM hUniting
    hFirstBeing hPrior hNotBoth hKinds hInfinity hEternity hNoComponent hImmaterial hWillFollows
    hOne hPerfect hGood

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
  have attributes := fromSource σ F InPotency GoodIn ComponentOf Composite ComposedOfMatterAndForm
    Infinite Eternal HasIntellect HasWill essenceOf esseOf hSuffice hMaximal hSource hCauseMore hEM
    hUniting hBeing hPreexist hGoodness hPerfections hFirstBeing hPrior hNotBoth hKinds hInfinity
    hEternity hNoComponent hImmaterial hWillFollows
  have existsGod := TruthCore.Results.Causality.TermSenseForks4.godExistsFromMaximeEnsCausingAll
    F.InAct F.MoreIn F.CausesIn F.esse ComponentOf F.PriorSimply σ.IsGod hSource hBeing
    hCauseMore hEM hPerfections hNoComponent hFirstBeing hFull
  exact ⟨TruthCore.Results.Causality.ClassicalGodAssembly.assemble σ existsGod
      (oneFromSource F σ.IsGod hSource hMaximal hCauseMore hEM) attributes,
    TruthCore.Results.Causality.TermSenseForks4.catholicismFromMaximeEnsCausingAll σ
      F.InAct F.MoreIn F.CausesIn F.esse ComponentOf F.PriorSimply hSource hBeing hCauseMore
      hEM hPerfections hNoComponent hFirstBeing hFull attributes hRevelation hJesus hFounded
      hCatholic hDivineFounding hOnlyTruth hProposes⟩

set_option synthInstance.maxSize 2048 in
theorem controls : Control.Checks := by
  dsimp only [Control.Checks, Control.Joint, Control.Scope, Control.Omissions,
    ClassicalAttributesJointWitness.InAct, ClassicalAttributesJointWitness.CausesIn,
    ClassicalAttributesJointWitness.MoreIn, ClassicalAttributesJointWitness.ComponentOf,
    Control.named, Control.edge, Control.gift, Control.higher, Control.empty, Control.allAct,
    Control.extra, Control.splitAct, MaximeEnsCausesBeingOfAllReading, GodCausesBeingOfAllOthers,
    GodNamesTheFullyDescribedPrinciple, IsMaximumIn, CausesAllInGenus,
    CausesEveryPerfectionOfOthers, RemoteFromAll, GodIsPerfect, IsPerfect,
    GodIsSupremelyGood, IsSupremelyGood, MaximumInGenusCausesAllInGenusReading,
    GodIsMaximalInBeing, CauseOfQualityInAnotherIsMoreSuchReading,
    PerfectionsOfEffectPreexistInCauseReading, GoodnessIsActualityReading,
    UniversalCauseTransfersPerfections, ActualityOnlyInsofarAsBeingReading,
    CauseOfBeingCausesEveryPerfection]
  and_intros <;> decide

end TruthCore.Results.Case.Catholicism.AttributesFromEsse
