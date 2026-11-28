module

public import TruthCore.Causality.DeiFiliusLordBlessed
public import TruthCore.Causality.NarDerivation
public import TruthCore.Case.Catholicism.DivineLoveBridge

/-! # The mode of a universal cause's giving

Analyst reconstruction of the priority argument in ST I q.19 a.4 co.
Causation in esse is tenseless. The adapter to giving in a selected world,
classification of the giving's exercised power, and priority requirements are
separate commitments. Rational exercise is effect-indexed but does not type
the practical content that specifies the effect. It leaves modal fixity open.
-/

@[expose] public section

namespace TruthCore.Causality.ThroughWill

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.WillVersusChance (AgencyFrame GivesBy OnePower)
open TruthCore.Causality.DeiFiliusAttributeField (IsCreatorOfAll)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing)
open TruthCore.Modal.PrussPowerPremises (GivesTo)

variable {W B T R S P : Type}

/-- At this effect and world the source gives by an owned rational power.
The rational-power classification is the existing agency-frame primitive.
Neither actual intellectual content nor alternative possibilities are typed. -/
def RationallyGivesAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (w : W) (g x : B) : Prop :=
  ∃ p, A.PowerOf g p ∧ A.Rational p ∧ GivesBy F A w g x p

/-- OPEN adapter to an actual exercise, only at the selected world and only
for distinct effects in act as to esse. No causal relation is identified
definitionally with another. -/
def ActualEsseCausesGiveAt (F : CausalityFrame W B T R) (InAct : B → R → Prop)
    (w : W) : Prop :=
  ∀ g x, x ≠ g → InAct x F.esse → F.CausesIn g x F.esse → GivesTo F w g x

/-- OPEN coverage: each giving at w exercises an owned power for which
rationality or its negation holds. This neither asserts uniqueness of power
nor rules out a giving with several exercised powers. -/
def GivingHasClassifiedPowerAt (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (w : W) : Prop :=
  ∀ g x, GivesTo F w g x →
    ∃ p, A.PowerOf g p ∧ A.Exercises w g x p ∧ (A.Rational p ∨ ¬ A.Rational p)

/-- OPEN consequence of intellectual predetermination of natural working:
each non-rational exercise in a giving requires a distinct prior intellect.
The stronger account of that intellect setting this end and means motivates
the premise. The type retains only the priority and intellectual capacity
needed by the inference. -/
def NonrationalGivingHasPriorIntellectAt (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (HasIntellect : B → Prop) (w : W) : Prop :=
  ∀ g x p, A.PowerOf g p → GivesBy F A w g x p → ¬ A.Rational p →
    ∃ z, z ≠ g ∧ F.PriorSimply z g ∧ HasIntellect z

/-- OPEN scope bridge: each qualifying universal cause is first in the
order of simple priority. Universal causal coverage by itself is silent on
whether a distinct being is prior to the cause. -/
def IntellectualUniversalCausesAreFirst (F : CausalityFrame W B T R)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop) : Prop :=
  ∀ g, HasIntellect g → HasWill g → IsCreatorOfAll InAct F.CausesIn F.esse g →
    IsFirstBeing F.PriorSimply g

/-- OPEN alternative to the priority route's premises: each qualifying
universal cause has at most one active power in the agency overlay. -/
def IntellectualUniversalCausesHaveOnePower (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (InAct : B → R → Prop)
    (HasIntellect HasWill : B → Prop) : Prop :=
  ∀ g, HasIntellect g → HasWill g → IsCreatorOfAll InAct F.CausesIn F.esse g →
    OnePower A g

/-- Effect-by-effect rational exercise at w by every qualifying universal
cause, at each distinct effect in act as to esse. -/
def IntellectualUniversalCausesGiveRationallyAt (F : CausalityFrame W B T R)
    (A : AgencyFrame W B S P) (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop)
    (w : W) : Prop :=
  ∀ g, HasIntellect g → HasWill g → IsCreatorOfAll InAct F.CausesIn F.esse g →
    ∀ x, x ≠ g → InAct x F.esse → RationallyGivesAt F A w g x

/-- OPEN application to providence: for a distinct actual effect of a
qualifying universal cause, owned rational exercise in giving entails an
end to which this giver directs this effect. -/
def RationalUniversalGivingDirects (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (HasIntellect HasWill : B → Prop)
    {E : Type} (Directs : B → B → E → Prop) (w : W) : Prop :=
  ∀ g, HasIntellect g → HasWill g → IsCreatorOfAll InAct F.CausesIn F.esse g →
    ∀ x, x ≠ g → InAct x F.esse → RationallyGivesAt F A w g x → ∃ e, Directs g x e

/-- OPEN recipient application: in the GOD_4 case, giving a distinct
actual effect by an owned rational power entails willing its esse to it.
This asks for the recipient-directed reading of willing. -/
def DivineRationalGivingWillsEsseFor (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (InAct : B → R → Prop) (IsGod : B → Prop) (WillsGoodFor : B → B → R → Prop)
    (w : W) : Prop :=
  ∀ g x, IsGod g → x ≠ g → InAct x F.esse → RationallyGivesAt F A w g x →
    WillsGoodFor g x F.esse


namespace Control

open TruthCore.Causality.DeiFiliusLordBlessed (UniversalIntellectualCauseDirectsAll)
open TruthCore.Case.Catholicism.DivineLoveBridge (CausalExistenceWilling)
open TruthCore.Causality.NarDerivation (FixedTowardAt RationalFixedGivingIsRequired)
open TruthCore.Causality.WillVersusChance (WillIsRationalPower)

/-- Two beings, both actual at both accessible worlds; false causes true's
esse. Whenever the exercise edge is present, it is present at both worlds.
The priority switch makes only the recipient prior to the cause. -/
def model (give prior : Bool) : CausalityFrame Bool Bool Unit Unit where
  history := ⟨⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => True⟩,
    fun _ _ _ => True, ()⟩
  GivesAt := fun _ g x _ => give = true ∧ g = false ∧ x = true
  CausesIn := fun g x _ => g = false ∧ x = true
  PriorSimply := fun z g => prior = true ∧ z = true ∧ g = false
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  esse := ()

/-- The cause owns two powers, of which only true is rational. Activating
neither power models an omitted exercise assignment, not natural giving. -/
def agency (power : Option Bool) : AgencyFrame Bool Bool Unit Bool where
  StateAt := fun _ _ _ => False
  ConditionOf := fun _ _ _ => False
  PowerOf := fun g _ => g = false
  Rational := fun p => p = true
  Exercises := fun _ g x p => g = false ∧ x = true ∧ power = some p

def acts (_ : Bool) (_ : Unit) : Prop := True
def intellect (_ : Bool) : Prop := True
def will (g : Bool) : Prop := g = false

def gives (give prior : Bool) : Prop := ActualEsseCausesGiveAt (model give prior) acts false
def classified (give prior : Bool) (power : Option Bool) : Prop :=
  GivingHasClassifiedPowerAt (model give prior) (agency power) false
def priority (give prior : Bool) (power : Option Bool) : Prop :=
  NonrationalGivingHasPriorIntellectAt (model give prior) (agency power) intellect false
def first (give prior : Bool) : Prop :=
  IntellectualUniversalCausesAreFirst (model give prior) acts intellect will
def rational (give prior : Bool) (power : Option Bool) : Prop :=
  IntellectualUniversalCausesGiveRationallyAt (model give prior) (agency power)
    acts intellect will false

/-- Each of the four omissions retains the other three inputs and falsifies
the conclusion with the same actual CAUSE_2 edge, intellect and will.
Omission of priority uses a fixed giving by the owned non-rational power even
though a rational power is owned. The positive control is also fixed; it
satisfies rational exercise and the four inputs while the direction and
recipient-willing outputs are empty. In it WN fails with no required means. -/
def Controls : Prop :=
  let F := model true false
  intellect false ∧ will false ∧ acts true F.esse ∧
  IsCreatorOfAll acts F.CausesIn F.esse false ∧
  WillIsRationalPower (agency (some false)) will ∧
  FixedTowardAt F false false true ∧
  GivesBy F (agency (some false)) false false true false ∧
  ¬ (agency (some false)).Rational false ∧
  (¬ gives false false ∧ classified false false none ∧ priority false false none ∧
    first false false ∧ ¬ rational false false none) ∧
  (gives true false ∧ ¬ classified true false none ∧ priority true false none ∧
    first true false ∧ ¬ rational true false none) ∧
  (gives true false ∧ classified true false (some false) ∧
    ¬ priority true false (some false) ∧ first true false ∧ ¬ rational true false (some false)) ∧
  (gives true true ∧ classified true true (some false) ∧
    priority true true (some false) ∧ ¬ first true true ∧ ¬ rational true true (some false)) ∧
  (gives true false ∧ classified true false (some true) ∧ priority true false (some true) ∧
    first true false ∧ rational true false (some true) ∧
    ¬ RationalFixedGivingIsRequired F (agency (some true)) (fun _ _ => False) false ∧
    ¬ UniversalIntellectualCauseDirectsAll acts F.CausesIn F.esse intellect will
      (fun _ _ (_ : Unit) => False) ∧
    ¬ CausalExistenceWilling will will acts F.CausesIn (fun _ _ _ => False) F.esse)

end Control
end TruthCore.Causality.ThroughWill
