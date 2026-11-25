module

public import TruthCore.Causality.ExerciseContribution

/-! Identical endpoint responses can arise from different productive paths. The operative-power case uses a step at each link. -/

@[expose] public section

namespace TruthCore.Causality.ExerciseEndpointControls

namespace ExerciseEndpoint

-- g is a selected working input. p is the producer's local readiness.
def mediatedStroke (g p : Bool) := g && p

def jointStroke (_g p : Bool) := p

def mediatedEffect (stroke : Bool) := stroke

def jointEffect (g stroke : Bool) := g && stroke

theorem endpointAgreement (g p : Bool) :
    mediatedEffect (mediatedStroke g p) = jointEffect g (jointStroke g p) := rfl

theorem actualAgreement : mediatedStroke true true = jointStroke true true := rfl

theorem discriminate : mediatedStroke false true ≠ jointStroke false true ∧
    mediatedEffect true ≠ jointEffect false true := by decide

end ExerciseEndpoint

namespace NativeResponse

-- cap is the response gain currently sustained by the named giver.
def cap (giver : Bool) (gain : Nat) : Nat := if giver then gain else 0

def run (power : Nat) (trigger feed : Bool) : Nat :=
  if trigger && feed then power else 0

theorem coupled (giver trigger : Bool) (gain : Nat) :
    run (cap giver gain) trigger true = run (cap giver gain) trigger giver := by
  cases giver <;> cases trigger <;> rfl

theorem isolate (gain : Nat) :
    run (cap true (gain + 1)) true true ≠ run (cap true (gain + 1)) true false := by
  intro h
  exact Nat.noConfusion h

open TruthCore.Causality.ExerciseContribution
open TruthCore.Causality.JointGroups (Exercise)

theorem viaOperativePower {B E G S : Type} (m : Exercise B E G S)
    (gift operative stroke result : E) (a b x : B)
    (ha : m.bearer gift = a) (hb : m.bearer stroke = b)
    (hx : m.bearer result = x) (give : Step m gift operative)
    (usePower : Step m operative stroke) (finish : Step m stroke result) :
    ThroughAt m stroke result a b x :=
  ⟨hb, hx, ⟨gift, ha, .tail (.single give) usePower⟩, finish⟩

end NativeResponse

end TruthCore.Causality.ExerciseEndpointControls
