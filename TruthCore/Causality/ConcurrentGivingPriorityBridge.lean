module

public import TruthCore.Causality.MetricBeginningArrival
public import TruthCore.Causality.SelfCausationPriority

/-!
A causal-sense bridge for the modal Arrival B no-self-giving premise.
Reuses the certified Second-Way derivation of no efficient self-causation from
cause-priority and no self-priority. Giving of being (time-indexed GivesAt)
and efficient causation (the supplied EfficientlyCausesIn) are DISTINCT senses.
No identification of the shared frame's CausesIn (cause of perfection) is made.
The selected simple-priority relation is one and the same F.PriorSimply.
All application premises remain OPEN; no claim of metaphysical establishment.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.MetricBeginningArrival (NoSelfGivingOnAccessible)

/-- If an agent actually gives its OWN being, that self-directed exercise also
falls under the supplied efficient cause of the agent's esse. This is the
minimum explicit cross-sense premise required for the already checked no-self
cause theorem. No assertion concerns distinct agents or world-independent
causal activities; the tenseless efficient cause predicate is used only on
the hypothetical self-edge. -/
def SelfGivingIsEfficientSelfCause {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ v c t, F.GivesAt v c c t → EfficientlyCausesIn c c F.esse

namespace Control
open TruthCore.Causality.MetricBeginningArrival.Control (selfGivingFrame)

def noEfficientCause (_ _ : Int) (_ : Unit) : Prop := False

/-- In the self-giving model, efficient causation and simple priority are
empty, so both priority premises hold; the missing cross-sense bridge is
exactly what permits self-GivesAt. Logical omission control only. -/
def Certificate : Prop :=
  TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
    noEfficientCause selfGivingFrame.PriorSimply ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading
    selfGivingFrame.PriorSimply ∧
  ¬ SelfGivingIsEfficientSelfCause selfGivingFrame noEfficientCause ∧
  ¬ NoSelfGivingOnAccessible selfGivingFrame true

end Control
end TruthCore.Causality.ConcurrentGivingPriorityBridge
