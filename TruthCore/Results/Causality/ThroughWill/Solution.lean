module

public import TruthCore.Causality.ThroughWill

@[expose] public section

namespace TruthCore.Results.Causality.ThroughWill

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ThroughWill
open TruthCore.Causality.WillVersusChance (AgencyFrame OnePowerIntellectualGivingWilled)
open TruthCore.Causality.DeiFiliusLordBlessed (UniversalIntellectualCauseDirectsAll)
open TruthCore.Case.Catholicism (GodHasIntellect GodIsSupremelyGood)
open TruthCore.Case.Catholicism.DivineLoveBridge (CausalExistenceWilling)

variable {W B T R S P E : Type}

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
  intro g hInt hWill hAll x hOther hAct
  have hGiving := hGive g x hOther hAct (hAll x hOther hAct)
  obtain ⟨p, hOwn, hExercises, hMode⟩ := hClass g x hGiving
  rcases hMode with hRat | hNonrat
  · exact ⟨p, hOwn, hRat, hGiving, hExercises⟩
  · obtain ⟨z, hz, hzg, _⟩ := hPrior g x p hOwn ⟨hGiving, hExercises⟩ hNonrat
    exact (hz (hFirst g hInt hWill hAll z hzg)).elim

/-- The one-power alternative specializes the existing all-worlds result
to the world of the cause's giving of each actual effect. -/
theorem rationalGivingOfOnePower
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop) (w : W)
    (hGive : ActualEsseCausesGiveAt F InAct w)
    (hOne : IntellectualUniversalCausesHaveOnePower F A InAct HasIntellect HasWill)
    (hRat : OnePowerIntellectualGivingWilled F A HasIntellect) :
    IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w := by
  intro g hInt hWill hAll x hOther hAct
  have hGiving := hGive g x hOther hAct (hAll x hOther hAct)
  obtain ⟨p, hOwn, hRational, hExercises⟩ :=
    hRat g hInt (hOne g hInt hWill hAll) w x hGiving
  exact ⟨p, hOwn, hRational, hGiving, hExercises⟩

theorem directsAllOfRationalGiving
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop)
    (Directs : B → B → E → Prop) (w : W)
    (hRat : IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w)
    (hDirects : RationalUniversalGivingDirects F A InAct HasIntellect HasWill Directs w) :
    UniversalIntellectualCauseDirectsAll InAct F.CausesIn F.esse HasIntellect HasWill Directs := by
  intro g hInt hWill hAll x hOther hAct
  exact hDirects g hInt hWill hAll x hOther hAct (hRat g hInt hWill hAll x hOther hAct)

theorem willsEsseForOfRationalGiving
    (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct GoodIn : B → R → Prop) (IsGod HasIntellect HasWill : B → Prop)
    (WillsGoodFor : B → B → R → Prop) (w : W)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn F.CausesIn F.esse)
    (hInt : GodHasIntellect IsGod HasIntellect)
    (hRat : IntellectualUniversalCausesGiveRationallyAt F A InAct HasIntellect HasWill w)
    (hRecipient : DivineRationalGivingWillsEsseFor F A InAct IsGod WillsGoodFor w) :
    CausalExistenceWilling IsGod HasWill InAct F.CausesIn WillsGoodFor F.esse := by
  intro g x hGod hWill hOther hAct _
  have hAll : TruthCore.Causality.DeiFiliusAttributeField.IsCreatorOfAll
      InAct F.CausesIn F.esse g := fun y hne hy => (hGood g hGod).2 y F.esse hne hy
  exact hRecipient g x hGod hOther hAct (hRat g (hInt g hGod) hWill hAll x hOther hAct)


theorem controls : TruthCore.Causality.ThroughWill.Control.Controls := by
  open TruthCore.Causality.ThroughWill.Control in
  simp [Controls, gives, classified, priority, first, rational, model, agency, acts, intellect, will,
    IntellectualUniversalCausesGiveRationallyAt, ActualEsseCausesGiveAt,
    GivingHasClassifiedPowerAt, NonrationalGivingHasPriorIntellectAt,
    IntellectualUniversalCausesAreFirst, RationallyGivesAt,
    TruthCore.Modal.PrussPowerPremises.GivesTo,
    TruthCore.Causality.WillVersusChance.GivesBy,
    TruthCore.Causality.WillVersusChance.WillIsRationalPower,
    TruthCore.Causality.NarDerivation.FixedTowardAt,
    TruthCore.Causality.NarDerivation.RationalFixedGivingIsRequired,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing,
    TruthCore.Causality.DeiFiliusAttributeField.IsCreatorOfAll,
    UniversalIntellectualCauseDirectsAll, CausalExistenceWilling,
    Bool.forall_bool, Bool.exists_bool]

end TruthCore.Results.Causality.ThroughWill
