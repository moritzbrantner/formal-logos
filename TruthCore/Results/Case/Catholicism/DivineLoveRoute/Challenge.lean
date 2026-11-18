import TruthCore.Case.Catholicism.DivineLoveBridge

namespace TruthCore.Results.Case.Catholicism.DivineLoveRoute
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.DivineLoveBridge
open TruthCore.Latin.Aquinas.SummaTheologiae (GoodnessIsActualityReading)

universe u v

/-- Registered zero-axiom form of `DivineLoveBridge.divineWillsGoodForAllExisting`.
The self/other split on `x = g` uses an explicit `DecidableEq Being` instance
parameter instead of classical choice; it is a type-level input (a decision
procedure for identity of beings), not a philosophical premise, and it carries
no content about goodness, will or causation. The two volitional bridges
`CausalExistenceWilling` and `DivineOwnGoodWilling` remain OPEN premises.
Supreme goodness supplies the generic causal field for distinct actual effects;
the coextension of good and actuality supplies the recipient's good in `esse`. -/
theorem willsGoodForAllExisting {Being : Sort u} {Respect : Sort v}
    [DecidableEq Being]
    (IsGod HasWill : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse)
    (hWill : GodHasWill IsGod HasWill)
    (hActualGood : GoodnessIsActualityReading GoodIn InAct)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn WillsGoodFor esse)
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn WillsGoodFor esse) :
    DivineWillsGoodForAllExisting IsGod InAct GoodIn WillsGoodFor esse := by
  sorry

/-- Registered zero-axiom form of `DivineLoveBridge.godLovesAllExisting`: the
q.20 a.2 love-meaning bridge applied to the recipient-good willing obtained by
`willsGoodForAllExisting`. All three intentional bridges stay OPEN premises. -/
theorem lovesAllExisting {Being : Sort u} {Respect : Sort v}
    [DecidableEq Being]
    (IsGod HasWill : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop)
    (Loves : Being → Being → Prop) (esse : Respect)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse)
    (hWill : GodHasWill IsGod HasWill)
    (hActualGood : GoodnessIsActualityReading GoodIn InAct)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn WillsGoodFor esse)
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn WillsGoodFor esse)
    (hLoveMeaning : WillingGoodEntailsLove GoodIn WillsGoodFor Loves) :
    GodLovesAllExisting IsGod InAct Loves esse := by
  sorry

end TruthCore.Results.Case.Catholicism.DivineLoveRoute
