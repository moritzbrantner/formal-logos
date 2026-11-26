module

public import TruthCore.Logic.AssertionRetorsion
public import TruthCore.Causality.Round2ExistenceAct
public import TruthCore.Causality.Round3CogitoBase

/-!
# Performance and bearing at the same world

The actuality reading uses the selected world's occurrence slice in the
realization premise. If the occurrence predicate is independently supplied,
`Round2ExistenceAct.OccurringThoughtOccursAt` is a sufficient calibration.
These are analyst readings with attribution deferred.
-/

@[expose] public section

namespace TruthCore.Logic.FirstPersonWitness

variable {B Content Act Episode : Type}

/-- Proposed agency dictionary for the assertion route. Interpret the
asserter in the same candidate domain used for bearers. An episode must be
both a realization of the assertion by that asserter and a local occurrence.
The bearer relation is separate from this dictionary. -/
def AssertionAgency (Asserts : B → Content → Prop) (claim : Content)
    (Here : Episode → Prop) (Realizes : B → Content → Episode → Prop)
    (b : B) (e : Episode) : Prop :=
  Asserts b claim ∧ Here e ∧ Realizes b claim e

/-- Proposed agency dictionary for the doubt route. The performer assignment
picks the candidate who does that act. A function value alone does not say
that the act is performed, that its episode is borne, or that the candidate
exists where the episode occurs. -/
def DoubtAgency (Performed DoubtsThought : Act → Prop) (performer : Act → B)
    (Here : Episode → Prop) (Realizes : Act → Episode → Prop)
    (b : B) (e : Episode) : Prop :=
  ∃ a, Performed a ∧ DoubtsThought a ∧ Here e ∧ Realizes a e ∧ performer a = b

namespace Control

/-- One act and episode. The episode occurs at one world; the performer
belongs to one world’s existence extension. The choices are independent. -/
def occursAt (site world : Bool) (_ : Unit) : Prop :=
  world = site

def ontic (home : Bool) : TruthCore.German.Kant.CosmologicalInference.Ontic Bool Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun world _ => world = home
  Causes := fun _ _ _ => False

def marked (_ : Unit) : Prop := True
def realizes (_ _ : Unit) : Prop := True
def performer (_ : Unit) : Unit := ()
def bearing (holds : Prop) (_ _ : Unit) : Prop := holds
def inAct (holds : Prop) (_ _ : Unit) : Prop := holds

end Control

end TruthCore.Logic.FirstPersonWitness
