module

public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Causality.WorldSourceRegress

@[expose] public section

namespace TruthCore.Causality.PerSeRegressCardinality
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.Regress

/-- The successor rule: n efficiently causes n+1, in the sole respect. -/
def successorEdge (cause effect : Nat) : Prop := effect = cause + 1

/-- In these controls precisely the efficient edges whose source is itself
efficiently caused are declared per se edges. -/
def asCaused {Being : Type} (edge : Being → Being → Prop) (cause effect : Being) : Prop :=
  edge cause effect ∧ ∃ earlier, edge earlier cause

/-- The Second Way's inputs other than its regress premise, interpreted on each
relation with the same single respect. -/
def SecondWayBackground {Being : Type} (edge prior : Being → Being → Prop) : Prop :=
  let efficient := fun cause effect (_ : Unit) => edge cause effect
  OrderOfEfficientCausesFoundReading efficient ∧
    EfficientCauseIsPriorToEffectReading efficient prior ∧
    NothingPriorToItselfReading prior ∧
    SecondEfficientCausesCauseOnlyAsCausedReading efficient (asCaused edge)

/-- Exact controls of bearer count and direction for the Second Way's regress
reading. The opposite orientations use the entire same Nat carrier. The finite
control uses distinct bearers and excludes self-edges. -/
def SuccessorOrientationAndFiniteCycle : Prop :=
  let forward := successorEdge
  let backward := Function.swap successorEdge
  let twoCycle := fun cause effect : Bool => cause ≠ effect
  (SecondWayBackground forward (· < ·) ∧
    Graph.NoCycles ⟨forward⟩ ∧
    NoInfinitePerSeEfficientCauseSeriesReading (asCaused forward) ∧
    IsFirstEfficientCause (fun cause effect (_ : Unit) => forward cause effect) 0) ∧
  (SecondWayBackground backward (· > ·) ∧
    Graph.NoCycles ⟨backward⟩ ∧
    (∀ x, AnchoredRegress ⟨asCaused backward⟩ x) ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading (asCaused backward) ∧
    ¬ ∃ first, IsFirstEfficientCause (fun cause effect (_ : Unit) => backward cause effect) first) ∧
  (Finite Bool ∧
    (∀ x, ¬ asCaused twoCycle x x) ∧
    PerSeCausalLoopReading (asCaused twoCycle) ∧
    InfinitePerSeCauseSeriesReading (asCaused twoCycle) ∧
    (∀ f : Nat → Bool, ¬ Function.Injective f) ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading (asCaused twoCycle))

end TruthCore.Causality.PerSeRegressCardinality
