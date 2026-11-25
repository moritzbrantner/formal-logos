module

public import TruthCore.Causality.ExerciseContribution
public import TruthCore.Explanation.BruteContingencyParity

/-!
# Actual exercise, product-dependent adoption and productive supply

Analyst application of the existing joint-supply test, not a definition of
adequate explanation or of intentionality. The question is whether an adopted
productive role may get ALL its productive support from the very product whose
production it is offered to explain. `OutputFounded` makes that proposed
dependence precise over the existing exercised records. Its obstruction reuses
the existing `Trap` theorem; the new matched controls keep one necessary bearer,
the same exercise and recipient, nonempty contribution records and source
contributions in the allegedly circular account.

`adoption` is a role-event of the source, not another being or a stipulated
intrinsic modification. The event indices do not decide whether this role can
vary while the source is strictly simple. The independently supplied predicate
of `Supply` is likewise not the metaphysical intrinsic-property predicate.
Actual causal credit and existential tokens are interpreted by the existing
contributor paths, and remain weaker than inductive supply. Their real causal,
rational and explanatory adequacy is OPEN. See the linked PSR note.
-/

@[expose] public section

namespace TruthCore.Explanation.ActualExerciseExplanation

open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Causality.ExerciseContribution
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FirstMoverNecessity (ContingentHasDistinctEsseCause)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.BruteContingencyParity (NoBruteContingentExistenceAt)
open TruthCore.German.Kant.CosmologicalInference

variable {B E G W : Type}

/-- A selected adoption and product have no independent supply, every actual
supplier of adoption needs the product as a contributor, and every actual
supplier of the product needs adoption. Other contributors, including a
necessary source, are allowed. This is productive dependence, not merely the
truth of an output-relative description. No temporal priority is assumed. -/
structure OutputFounded (m : Exercise B E G W) (I : E → Prop)
    (adoption product : E) : Prop where
  adoptionNotIndependent : ¬ I adoption
  productNotIndependent : ¬ I product
  adoptionNeedsProduct : ∀ g, m.exercisedGroups.admitted g →
    m.groups.effect g = adoption → product ∈ m.groups.contributors g
  productNeedsAdoption : ∀ g, m.exercisedGroups.admitted g →
    m.groups.effect g = product → adoption ∈ m.groups.contributors g

/-- A narrow application of the existing borrowing-trap obstruction. An actual
source contribution outside the pair does not discharge a retained conjunctive
prerequisite inside it. This says nothing about an alternative account whose
adoption is independently supplied. -/
def ProductiveCut : Prop :=
  ∀ (B E G W : Type) (m : Exercise B E G W) (I : E → Prop) (a x : E),
    OutputFounded m I a x →
      ¬ Supply m.exercisedGroups I a ∧ ¬ Supply m.exercisedGroups I x

namespace Matched

inductive Bearer | source | recipient deriving DecidableEq
inductive Event | operation | adoption | product deriving DecidableEq
inductive Record | adoption | product | direct deriving DecidableEq
inductive Route | circular | admitted | exercised deriving DecidableEq
inductive Respect | operation | esse deriving DecidableEq

/-- Operation and adoption are distinct role indices of the SAME source.
This map asserts neither two substances nor two intrinsic actualizing forms. -/
def bearer : Event → Bearer
  | .operation | .adoption => .source
  | .product => .recipient

def respect : Event → Respect
  | .operation | .adoption => .operation
  | .product => .esse

/-- The source operation occurs in both populated worlds. Adoption and the
particular recipient's realization occur only in the actual world `true`.
Occurrence of a role is not defined as existence of its bearer. -/
def occurs (w : Bool) : Event → Prop
  | .operation => True
  | .adoption | .product => w = true

/-- The circular adoption record requires source operation AND product. The
direct record, when available, is a genuine alternative requiring only source
operation; it does not weaken the circular record's contributor set. -/
def groups (route : Route) : Groups Event Record where
  contributors := fun g => {e | match g with
    | .adoption => e = .operation ∨ e = .product
    | .product => e = .adoption
    | .direct => e = .operation}
  enablers := fun _ => ∅
  effect := fun g => match g with
    | .adoption | .direct => .adoption
    | .product => .product
  admitted := fun g => g ≠ .direct ∨ route ≠ .circular

/-- Records are exercised only in the on world. Merely admitting the direct
alternative does not exercise it. This is explicit data of the interpretation,
not a conclusion drawn from the presence of the source. -/
def exercise (route : Route) (w : Bool) : Exercise Bearer Event Record Bool where
  groups := groups route
  bearer := bearer
  occurs := occurs
  allowed := fun _ => True
  actual := w
  exercised := fun g => w = true ∧ (g ≠ .direct ∨ route = .exercised)

/-- Independently supplied actual contribution of the source operation. -/
def sourceBasis (e : Event) : Prop := e = .operation

/-- Alternative stopping policy: the source's actual adoption is independently
supplied too. This introduces NO additional event or bearer, and is NOT proved
adequate. `Supply.intrinsic` means independent contribution in this standard,
not an intrinsic metaphysical modification of the source. -/
def exerciseBasis (e : Event) : Prop := e = .operation ∨ e = .adoption

/-- The source necessarily exists; the same recipient exists at `true` only.
Causal edges are distinct-bearer actual contributor-path credit in the esse
respect, not an independently reassigned table of causes. -/
def ontic (route : Route) : Ontic Bool Bearer where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w b => b = .source ∨ w = true
  Causes := fun w a b => a ≠ b ∧ Credit (exercise route w) respect a b .esse

/-- A selected causal interpretation of the SAME exercise. CausesIn is the
existing path-credit reading at the actual context. GivesAt uses distinct-bearer
credit at the supplied world. The remaining shared fields are unused and empty;
no inference from them, temporal conservation or real esse efficacy is claimed. -/
def frame (route : Route) : CausalityFrame Bool Bearer Unit Respect where
  history := {
    ontic := ontic route
    IsAt := fun w b _ => (ontic route).ExistsAt w b
    now := () }
  GivesAt := fun w a b _ => (ontic route).Causes w a b
  CausesIn := Credit (exercise route true) respect
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := .esse

/-- Narrow path-credit token adapter. A circumstantial token about c is
admitted exactly when c has a distinct-bearer actual path to x's esse event.
It asserts no rational recognition, intrinsic explanation or adequacy. -/
def reasons (route : Route) : Model Bool Bearer where
  ontic := ontic route
  explains := fun w r f => match r, f with
    | .intrinsic _, .fact _ => False
    | .circumstance c, .fact x => (ontic route).Causes w c x

/-- Shared fixed-witness background for ALL three routes. Nonempty actual
records, source-to-adoption and adoption-to-product credit remain even in the
circular account. Token existential coverage and B2 therefore do not certify
the stronger source-rooted supply standard. Neither is asserted of reality. -/
def Background (route : Route) : Prop :=
  (exercise route true).coherent ∧
  (∀ g, (exercise route true).exercisedGroups.admitted g →
    ((exercise route true).groups.contributors g).Nonempty) ∧
  NecessaryAt (ontic route) true .source ∧
  ContingentAt (ontic route) true .recipient ∧
  (exercise route true).bearer .operation = .source ∧
  (exercise route true).bearer .adoption = .source ∧
  (exercise route true).bearer .product = .recipient ∧
  Step (exercise route true) .operation .adoption ∧
  Step (exercise route true) .adoption .product ∧
  Step (exercise route true) .product .adoption ∧
  Credit (exercise route true) respect .source .recipient .esse ∧
  (frame route).GivesAt true .source .recipient () ∧
  NoBruteContingentExistenceAt (reasons route) true ∧
  ContingentHasDistinctEsseCause (frame route) true ∧
  ¬ (exercise route true).suffices {.operation} .adoption ∧
  ¬ (exercise route true).suffices {.operation} .product

/-- Matched constructive controls, with no empty contribution relation.
All three profiles preserve the same worlds, occurrence table and bearers.
The first two are output-founded and unsupplied despite the necessary source's
actual contribution. Exercising the source-only alternative supplies both
roles while preserving the circular alternative. Accepting the adoption as an
independent exercise also supplies the product on the original carrier, without
another decision event. None of these structures determines agency, adequacy,
the metaphysical admissibility of the worlds, or strong simplicity. -/
def Comparison : Prop :=
  (∀ route, Background route) ∧
  OutputFounded (exercise .circular true) sourceBasis .adoption .product ∧
  OutputFounded (exercise .admitted true) sourceBasis .adoption .product ∧
  (groups .admitted).admitted .direct ∧
  ¬ (exercise .admitted true).exercised .direct ∧
  ¬ Supply (exercise .circular true).exercisedGroups sourceBasis .adoption ∧
  ¬ Supply (exercise .circular true).exercisedGroups sourceBasis .product ∧
  ¬ Supply (exercise .admitted true).exercisedGroups sourceBasis .product ∧
  Supply (exercise .exercised true).exercisedGroups sourceBasis .adoption ∧
  Supply (exercise .exercised true).exercisedGroups sourceBasis .product ∧
  ¬ OutputFounded (exercise .exercised true) sourceBasis .adoption .product ∧
  Supply (exercise .circular true).exercisedGroups exerciseBasis .product ∧
  ¬ OutputFounded (exercise .circular true) exerciseBasis .adoption .product ∧
  ¬ (exercise .exercised true).jointlySufficient .direct

/-- A different restored route: the same source operation directly supplies
the product. Adoption still requires source operation AND product in its only
actual supplying record. Product-dependent adoption is therefore not by itself
a borrowing trap: the product need not depend on adoption in EVERY alternative.
Calling this role a rational guide would require more than these records. -/
def outputExercise (w : Bool) : Exercise Bearer Event Record Bool :=
  { exercise .exercised w with
    groups := { groups .exercised with
      effect := fun g => match g with
        | .adoption => .adoption
        | .product | .direct => .product } }

/-- Same bearers, occurrences and actual episode, with a source-only productive
route to the product. The product and adoption both have source-rooted Supply
although every actual supplier of adoption still needs the product. Thus an
output-grounded description alone does not entail the two-sided obstruction.
No explanatory-priority or agency verdict follows from the restored supply. -/
def OutputBypass : Prop :=
  (outputExercise true).bearer = (exercise .exercised true).bearer ∧
  (outputExercise true).occurs = (exercise .exercised true).occurs ∧
  (outputExercise true).coherent ∧
  (∀ g, (outputExercise true).exercisedGroups.admitted g →
    (outputExercise true).groups.effect g = .adoption →
      Event.product ∈ (outputExercise true).groups.contributors g) ∧
  Step (outputExercise true) .operation .product ∧
  Supply (outputExercise true).exercisedGroups sourceBasis .product ∧
  Supply (outputExercise true).exercisedGroups sourceBasis .adoption ∧
  ¬ OutputFounded (outputExercise true) sourceBasis .adoption .product

end Matched
end TruthCore.Explanation.ActualExerciseExplanation
