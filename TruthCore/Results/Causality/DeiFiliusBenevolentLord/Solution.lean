module

public import TruthCore.Causality.DeiFiliusBenevolentLord
public import TruthCore.Results.Causality.DeiFiliusUnifiedRoute.Solution

/-! LORD_3 (#1733): the restricted recipient-willing premise from the #1732
willing result and from the causal-willing bridge, the strength order of the
LORD_3 sense bridge against the LORD_2 bridge, the unified Dei Filius root
re-derived with its lord conjunct through LORD_3, and controls. Analyst
formulations, attribution deferred. No premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.DeiFiliusBenevolentLord

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine NineLiveSomeTime)
open TruthCore.Causality.DeiFiliusLivingSelfOperation (PureActLifeAtSomeTimeIsLiving)
open TruthCore.Causality.DeiFiliusLordBlessed
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
open TruthCore.Causality.DeiFiliusBenevolentLord
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Case.Catholicism.DivineLoveBridge
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- The #1732 result's conclusion gives the restricted premise: if every GOD_4
wills some good of its own to every being in act as to being, then in particular
to every distinct intellectual one whose being it causes. Weakening only. -/
theorem intellectualWillingOfWillsGoodForAll {Being Respect : Type}
    (IsGod HasWill HasIntellect : Being → Prop) (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect)
    (hAll : DivineWillsGoodForAllExisting IsGod InAct GoodIn WillsGoodFor esse) :
    IntellectualRecipientExistenceWilling IsGod HasWill HasIntellect InAct GoodIn CausesIn
      WillsGoodFor esse :=
  fun g x hg _ _ hx _ _ => hAll g hg x hx

/-- The causal-willing bridge with the q.5 a.1 coextension gives the restricted
premise without the divine self-case: the good willed is x's being, which is a
good of x because x is in act in it. -/
theorem intellectualWillingOfCausalWilling {Being Respect : Type}
    (IsGod HasWill HasIntellect : Being → Prop) (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn WillsGoodFor esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct) :
    IntellectualRecipientExistenceWilling IsGod HasWill HasIntellect InAct GoodIn CausesIn
      WillsGoodFor esse :=
  fun g x hg hw hne hx _ hc => ⟨esse, (hGoodness x esse).2 hx, hCausesWill g x hg hw hne hx hc⟩

/-- Strength order: the LORD_2 bridge entails the LORD_3 bridge, since whatever is
LORD_3 is LORD_2. Weakening of the antecedent only. -/
theorem benevolentLordSenseBridgeOfGovernorIsLord {Being Respect : Type}
    (InAct GoodIn : Being → Respect → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (Governs : Being → Being → Prop) (HasIntellect : Being → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (D : Primitives Being)
    (hOld : CauseAndGovernorOfAllIsLord InAct CausesIn esse Governs D) :
    BenevolentCauseAndGovernorOfAllIsLord InAct GoodIn CausesIn esse Governs HasIntellect
      WillsGoodFor D :=
  fun g h => hOld g h.1

/-- The spine's root has every typed Dei Filius attribute, with all five
primitives through their typed senses and the lord conjunct through LORD_3. The
registered `deiFiliusRootUnified` is applied, without the LORD_2 sense bridge, to
the primitives that agree with `D` except that their lord field is LORD_2; that
bridge then holds trivially and nothing about `D.IsLord` is used. Its root `n` is
GOD_4, has will and is LORD_2, so it causes the being of every other being in act
as to being; the restricted willing premise gives, for each such intellectual
other, a good of its own that `n` wills to it. Hence `n` is LORD_3, and the LORD_3
sense bridge gives `D.IsLord n`. Every other conjunct is carried over. -/
theorem deiFiliusRootUnifiedBenevolentLord {W Principle Respect Time : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being) (LivesAt : σ.Being → Time → Prop)
    (Governs : σ.Being → σ.Being → Prop) (understanding : Respect) (C : Comprehension σ.Being)
    (WillsGoodFor : σ.Being → σ.Being → Respect → Prop)
    (hUnderived : NecessaryConcreteUnderivedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesToMaximumAtBeing p.InAct MoreIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading p.InAct p.CausesIn p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hActPrior : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority
      p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hGodMaximal : GodIsMaximalInBeing σ.IsGod p.InAct MoreIn p.esse)
    (hNineLive : NineLiveSomeTime p.InAct GoodIn InPotency p.CausesIn p.esse σ.IsGod Composite
      Infinite Eternal HasIntellect HasWill LivesAt)
    (hLivingSense : PureActLifeAtSomeTimeIsLiving InPotency LivesAt D)
    (hNineLord : NineAreLordByCauseAndGovernment p.InAct GoodIn InPotency p.CausesIn p.esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill Governs)
    (hRecipient : IntellectualRecipientExistenceWilling σ.IsGod HasWill HasIntellect p.InAct
      GoodIn p.CausesIn WillsGoodFor p.esse)
    (hBenevolentSense : BenevolentCauseAndGovernorOfAllIsLord p.InAct GoodIn p.CausesIn p.esse
      Governs HasIntellect WillsGoodFor D)
    (hNineBlessed : NineAreBlessedByUnderstanding p.InAct GoodIn InPotency p.CausesIn p.esse
      understanding σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hBlessedSense : UnderstandingPerfectIsMostBlessed p.InAct GoodIn p.esse understanding
      HasIntellect D)
    (hNineImmense : NineAreImmenseAsInfiniteCauseOfAll p.InAct GoodIn InPotency p.CausesIn p.esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hImmenseSense : InfiniteCauseOfAllIsImmense p.InAct p.CausesIn p.esse Infinite D)
    (hNineIncomprehensible : NineAreIncomprehensibleToCausedIntellects p.InAct GoodIn InPotency
      p.CausesIn p.esse σ.IsGod Composite Infinite Eternal HasIntellect HasWill C)
    (hIncomprehensibleSense : InfiniteUncomprehendedIsIncomprehensible p.CausesIn p.esse Infinite
      HasIntellect C D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  let D' : Primitives σ.Being :=
    { D with IsLord := IsLordByCauseAndGovernment p.InAct p.CausesIn p.esse Governs }
  obtain ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod, h⟩ :=
    TruthCore.Results.Causality.DeiFiliusUnifiedRoute.deiFiliusRootUnified σ m w p GoodIn
      InPotency MoreIn PriorSimply ComponentOf Composite MatterForm Infinite Eternal HasIntellect
      HasWill Pw D' LivesAt Governs understanding C hUnderived hEM hGenus hExisting hEsse
      hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent
      hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hNineLive
      hLivingSense hNineLord (fun _ hx => hx) hNineBlessed hBlessedSense hNineImmense
      hImmenseSense hNineIncomprehensible hIncomprehensibleSense hPower
  have hLord2 : IsLordByCauseAndGovernment p.InAct p.CausesIn p.esse Governs n := h.lord
  have hLord3 : IsBenevolentLordByCauseAndGovernment p.InAct GoodIn p.CausesIn p.esse Governs
      HasIntellect WillsGoodFor n :=
    ⟨hLord2, fun x hne hx hi => hRecipient n x hGod h.will hne hx hi (hLord2.1 x hne hx)⟩
  exact ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod,
    { one := h.one
      living := h.living
      creator := h.creator
      lord := hBenevolentSense n hLord3
      almighty := h.almighty
      eternal := h.eternal
      immense := h.immense
      incomprehensible := h.incomprehensible
      intellect := h.intellect
      will := h.will
      perfect := h.perfect
      infinite := h.infinite
      simple := h.simple
      immutable := h.immutable
      spiritual := h.spiritual
      distinct := h.distinct
      blessed := h.blessed
      exalted := h.exalted
      good := h.good }⟩

/-- A Boolean other than `true` is `false`. -/
private theorem neTrue {x : Bool} (h : x ≠ true) : x = false := by
  cases x
  · rfl
  · exact absurd rfl h

open TruthCore.Causality.DeiFiliusBenevolentLord.Control in
open TruthCore.Case.Catholicism.DivineLoveSenses in
/-- The interpretations of `Control.Controls`, checked by unfolding. -/
theorem controls : TruthCore.Causality.DeiFiliusBenevolentLord.Control.Controls := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro g x rfl - hne - - hc
    exact ⟨(), trivial, rfl, rfl, hc.2⟩
  · rintro g ⟨⟨hc, -⟩, -⟩
    refine ⟨rfl, ?_⟩
    cases g
    · exact absurd (hc true (by decide) trivial).1 (by decide)
    · rfl
  · refine ⟨⟨fun x hne _ => ⟨rfl, ?_⟩, fun x hne _ => ⟨rfl, ?_⟩⟩, fun x hne _ _ =>
      ⟨(), trivial, rfl, rfl, ?_⟩⟩ <;> exact neTrue hne
  · exact ⟨rfl, rfl⟩
  · rintro g ⟨-, hw⟩
    exact absurd (hw (!g) (by cases g <;> decide) trivial trivial) (by
      rintro ⟨_, _, h, _⟩; exact absurd h (by decide))
  · intro hOld
    have hL : IsLordByCauseAndGovernment everywhere causes () governs true :=
      ⟨fun x hne _ => ⟨rfl, neTrue hne⟩,
        fun x hne _ => ⟨rfl, neTrue hne⟩⟩
    exact absurd (hOld true hL).1 (by decide)
  · refine ⟨⟨fun x hne _ => ⟨rfl, ?_⟩, fun x hne _ => ⟨rfl, ?_⟩⟩, fun x hne _ _ =>
      ⟨(), trivial, rfl, rfl, ?_⟩⟩ <;> exact neTrue hne
  · rintro ⟨h, -⟩; exact absurd h (by decide)
  · exact ⟨fun x hne _ => ⟨rfl, neTrue hne⟩,
      fun x hne _ => ⟨rfl, neTrue hne⟩⟩
  · rintro ⟨-, hw⟩
    obtain ⟨_, _, h, _⟩ := hw false (by decide) trivial trivial
    exact absurd h (by decide)
  · rintro g x hg - hne - hi -
    exact absurd ((show x = true from hi).trans (show g = true from hg).symm) hne
  · intro x r; exact Iff.rfl
  · rintro g x rfl - hne hr - -
    refine ⟨⟨true, Or.inl rfl, rfl, ?_, rfl⟩, ?_⟩
    · cases x
      · rfl
      · exact absurd rfl hne
    · rintro ⟨h, _⟩; exact absurd h (by decide)
  · intro hAll
    obtain ⟨_, _, h, _⟩ := hAll true rfl false trivial
    exact absurd h (by decide)
  · intro hCW
    obtain ⟨h, _⟩ := hCW true false rfl trivial (by decide) trivial ⟨rfl, rfl⟩
    exact absurd h (by decide)

open TruthCore.Causality.DeiFiliusBenevolentLord.Control in
/-- The LORD_3 root model, reusing the checked unified root model
(`DeiFiliusUnifiedRoute.controls`, which permits the three Mathlib axioms): its
bundle contains the LORD_2 bridge, which entails the LORD_3 bridge
(`benevolentLordSenseBridgeOfGovernorIsLord`); the willing assignment is permissive
and the act dictionary is all-true, so the restricted willing premise holds. -/
theorem rootModel : TruthCore.Causality.DeiFiliusBenevolentLord.Control.RootModel := by
  intro hEM
  obtain ⟨hBundle, hRoot⟩ := TruthCore.Results.Causality.DeiFiliusUnifiedRoute.controls.2.1 hEM
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLoS, -⟩ :=
    id hBundle
  exact ⟨hBundle, fun _ _ _ _ _ _ _ _ => ⟨true, trivial, trivial⟩,
    benevolentLordSenseBridgeOfGovernorIsLord _ _ _ _ _ _ _ _ hLoS,
    ⟨by decide, Or.inr rfl⟩, hRoot⟩

end TruthCore.Results.Causality.DeiFiliusBenevolentLord
