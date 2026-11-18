module

public import TruthCore.Case.Catholicism.DivineLoveSenses
public import TruthCore.Results.Case.Catholicism.DivineLoveRoute.Solution

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.DivineLoveSenseRoute
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.DivineLoveBridge
open TruthCore.Case.Catholicism.DivineLoveSenses
open TruthCore.Latin.Aquinas.SummaTheologiae (GoodnessIsActualityReading)

universe u v

/-- Strength order: the strong (exclusive) ordered variant implies the weak
ad 3 ordered reading by dropping its denial conjunct. -/
theorem orderedStrongToWeak {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill Rational : Being → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (W : RecipientGoodWilling Being Respect) (O : OrderedWilling Being Respect)
    (esse : Respect)
    (hStrong : OrderedExistenceWilling IsGod HasWill Rational InAct CausesIn W O esse) :
    OrderedExistenceWillingWeak IsGod HasWill Rational InAct CausesIn O esse :=
  fun g x hg hw hne hr hx hc => (hStrong g x hg hw hne hr hx hc).1

/-- At one `RecipientGoodWilling` W, the strong ordered variant and the
recipient-directed causal-willing bridge instantiated at `W.WillsGoodFor`
together exclude any distinct, non-rational, actual being whose esse a GOD_4
with will causes. -/
theorem orderedStrongExcludesNonRationalEffects {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill Rational : Being → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (W : RecipientGoodWilling Being Respect) (O : OrderedWilling Being Respect)
    (esse : Respect)
    (hStrong : OrderedExistenceWilling IsGod HasWill Rational InAct CausesIn W O esse)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn W.WillsGoodFor esse) :
    NoNonRationalCausedEffect IsGod HasWill Rational InAct CausesIn esse :=
  fun g x hg hw hne hr hx hc =>
    (hStrong g x hg hw hne hr hx hc).2 (hCausesWill g x hg hw hne hx hc)

open TruthCore.Case.Catholicism.DivineLoveSenses.Sample in
/-- The weak ordered reading is compatible with the recipient-directed bridge
at one `RecipientGoodWilling` (see `WeakOrderedCompatibilityWitness`). -/
theorem weakOrderedCompatible : WeakOrderedCompatibilityWitness := by
  refine ⟨?_, ?_, rfl, Bool.noConfusion, Bool.noConfusion, trivial, ⟨rfl, rfl⟩, ?_⟩
  · intro g x hg _ _ _ _ hc
    exact ⟨true, Or.inl rfl, hg, hc.2, rfl⟩
  · intro g _ hg _ _ _ _
    exact hg
  · intro h
    exact (h true false rfl rfl Bool.noConfusion Bool.noConfusion trivial ⟨rfl, rfl⟩).2 rfl

/-- `willsGoodForAllExisting` at the CREATURE_WILLING_1 sense carrier
`W.WillsGoodFor`. -/
theorem willsGoodForAllExistingAtCarrier {Being : Sort u} {Respect : Sort v}
    [DecidableEq Being]
    (IsGod HasWill : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (W : RecipientGoodWilling Being Respect) (esse : Respect)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse)
    (hWill : GodHasWill IsGod HasWill)
    (hActualGood : GoodnessIsActualityReading GoodIn InAct)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn W.WillsGoodFor esse)
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn W.WillsGoodFor esse) :
    DivineWillsGoodForAllExisting IsGod InAct GoodIn W.WillsGoodFor esse :=
  TruthCore.Results.Case.Catholicism.DivineLoveRoute.willsGoodForAllExisting
    IsGod HasWill InAct GoodIn CausesIn W.WillsGoodFor esse hGood hWill hActualGood
    hCausesWill hOwn

/-- `lovesAllExisting` at the sense carriers `W.WillsGoodFor`
(CREATURE_WILLING_1) and `T.Loves` (LOVE_1). -/
theorem lovesAllExistingAtCarriers {Being : Sort u} {Respect : Sort v}
    [DecidableEq Being]
    (IsGod HasWill : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (W : RecipientGoodWilling Being Respect) (T : ThinLove Being) (esse : Respect)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse)
    (hWill : GodHasWill IsGod HasWill)
    (hActualGood : GoodnessIsActualityReading GoodIn InAct)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn W.WillsGoodFor esse)
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn W.WillsGoodFor esse)
    (hLoveMeaning : WillingGoodEntailsLove GoodIn W.WillsGoodFor T.Loves) :
    GodLovesAllExisting IsGod InAct T.Loves esse :=
  TruthCore.Results.Case.Catholicism.DivineLoveRoute.lovesAllExisting
    IsGod HasWill InAct GoodIn CausesIn W.WillsGoodFor T.Loves esse hGood hWill
    hActualGood hCausesWill hOwn hLoveMeaning

end TruthCore.Results.Case.Catholicism.DivineLoveSenseRoute
