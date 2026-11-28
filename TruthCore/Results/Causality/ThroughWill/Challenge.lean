import TruthCore.Causality.ThroughWill

namespace TruthCore.Results.Causality.ThroughWill

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ThroughWill
open TruthCore.Causality.WillVersusChance (AgencyFrame OnePowerIntellectualGivingWilled)
open TruthCore.Causality.DeiFiliusLordBlessed (UniversalIntellectualCauseDirectsAll)
open TruthCore.Case.Catholicism (GodHasIntellect GodIsSupremelyGood)
open TruthCore.Case.Catholicism.DivineLoveBridge (CausalExistenceWilling)

/-- At any distinct actual effect, exercise of a non-rational power would
require an intellect prior to the first cause. The classified exercise
must therefore be rational. -/
theorem rationalGivingOfPriority
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop) (w : W)
    (hGive : ActualEsseCausesGiveAt F InAct w)
    (hClass : GivingHasClassifiedPowerAt F A w)
    (hPrior : NonrationalGivingHasPriorIntellectAt F A HasIntellect w)
    (hFirst : IntellectualUniversalCausesAreFirst F InAct HasIntellect HasWill) :
    IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w := by
  sorry

/-- The one-power alternative specializes the existing all-worlds result
to the world of the cause's giving of each actual effect. -/
theorem rationalGivingOfOnePower
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop) (w : W)
    (hGive : ActualEsseCausesGiveAt F InAct w)
    (hOne : IntellectualUniversalCausesHaveOnePower F A InAct HasIntellect HasWill)
    (hRat : OnePowerIntellectualGivingWilled F A HasIntellect) :
    IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w := by
  sorry

theorem directsAllOfRationalGiving
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop)
    (Directs : B → B → E → Prop) (w : W)
    (hRat : IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w)
    (hDirects : RationalUniversalGivingDirects F A InAct HasIntellect HasWill Directs w) :
    UniversalIntellectualCauseDirectsAll InAct F.CausesIn F.esse HasIntellect HasWill Directs := by
  sorry

theorem willsEsseForOfRationalGiving
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct GoodIn : B → R → Prop) (IsGod HasIntellect HasWill : B → Prop)
    (WillsGoodFor : B → B → R → Prop) (w : W)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn F.CausesIn F.esse)
    (hInt : GodHasIntellect IsGod HasIntellect)
    (hRat : IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w)
    (hRecipient : DivineRationalGivingWillsEsseFor F A InAct IsGod WillsGoodFor w) :
    CausalExistenceWilling IsGod HasWill InAct F.CausesIn WillsGoodFor F.esse := by
  sorry

theorem controls : TruthCore.Causality.ThroughWill.Control.Controls := by
  sorry

end TruthCore.Results.Causality.ThroughWill
