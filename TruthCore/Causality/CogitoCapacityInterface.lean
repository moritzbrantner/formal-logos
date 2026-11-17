module

public import TruthCore.Causality.CapacityInterface
public import TruthCore.Logic.CogitoConcrete

/-! A selected intellectual-effect capacity for the existing Cogito consumer.
`intellectualEffect` specifies ability to perform an intellectual operation
(understanding or judging), not production of a separate inner object. Suitable
conditions and applicability remain open interpretation obligations. Possession
is the existing primitive, never defined as successful exercise. No law about
all events or all existents is imposed. Analyst reconstruction; attribution deferred.
-/

@[expose] public section

namespace TruthCore.Causality.CogitoCapacityInterface

open TruthCore.Causality.CapacityInterface
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Logic.CogitoConcrete

/-- Local mapping is enough for this selected-world consumer; values at other
worlds and other respects are unrestricted. It is an assumption, not automatic. -/
def SelectedMapping {W B R : Type} (power : W → B → Prop)
    (p : Capacity W B R) (intellectualEffect : R) (w : W) : Prop :=
  ∀ b, power w b ↔ p.possesses w b intellectualEffect

/-- Both original capacity clauses transport under a local mapping. This does
not prove either clause or infer capacity from occurrence. -/
def FormulaTransport : Prop :=
  ∀ (W B Episode R : Type)
    (a : TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect.OperationAttribution B Episode)
    (concrete : B → Prop) (power : W → B → Prop) (p : Capacity W B R)
    (intellectualEffect : R) (w : W),
    SelectedMapping power p intellectualEffect w →
    (IntellectualExerciserHasPowerAt a power w ↔
      IntellectualExerciserHasPowerAt a (bearerProfile p intellectualEffect) w) ∧
    (PowerRequiresConcreteAt concrete power w ↔
      PowerRequiresConcreteAt concrete (bearerProfile p intellectualEffect) w)

namespace Control
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoEsse

abbrev m := Round2ExistenceAct.Control.ont True False
abbrev a := Round2ExistenceAct.Control.att True
abbrev occurs : Unit → Prop := fun _ => True
abbrev bears : Unit → Unit → Prop := fun _ _ => True
abbrev noneConcrete : Unit → Prop := fun _ => False

/-- One bearer has a non-intellectual capacity (false respect), but lacks the
selected intellectual capacity (true respect). No event identification is used. -/
def otherPower : Capacity Unit Unit Bool := ⟨fun _ _ r => r = false⟩

/-- All four noncapacity Cogito premises hold with an actual exercise. -/
def Background : Prop :=
  ThoughtOccurs occurs ∧ EveryThoughtHasSubject occurs bears ∧
  BorneThoughtExercisesIntellect occurs bears a ∧ EveryBearerExistsAt m occurs bears ()

/-- With the five remaining premises true, omitting exercise-to-capacity permits
an intellectual exercise without selected capacity and without a concrete bearer. -/
def MissingActivation : Prop :=
  Background ∧
  PowerRequiresConcreteAt noneConcrete (bearerProfile otherPower true) () ∧
  ¬ IntellectualExerciserHasPowerAt a (bearerProfile otherPower true) () ∧
  ¬ InhabitedConcreteAt m noneConcrete ()

/-- Exercise-to-power for the old profile and concreteness for a different
selected profile cannot be composed. The missing mapping is concretely false. -/
def MissingMapping : Prop :=
  Background ∧
  IntellectualExerciserHasPowerAt a (fun (_ _ : Unit) => True) () ∧
  PowerRequiresConcreteAt noneConcrete (bearerProfile otherPower true) () ∧
  ¬ SelectedMapping (fun (_ _ : Unit) => True) otherPower true () ∧
  ¬ InhabitedConcreteAt m noneConcrete ()

end Control

/-- Exact formula correspondence and scoped finite omission controls, not
counterexamples to real exercise or evidence against a metaphysical premise. -/
def Certificate : Prop :=
  FormulaTransport ∧ Control.MissingActivation ∧ Control.MissingMapping

end TruthCore.Causality.CogitoCapacityInterface
