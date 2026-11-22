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
The bridge drops the history and moment indices of GivesAt, so the efficient
relation is read world- and time-neutrally here, and the reused Second Way
premises are used under that modal reading (see the bridge's docstring).
All application premises remain OPEN; no claim of metaphysical establishment.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.MetricBeginningArrival (NoSelfGivingOnAccessible)

/-- If an agent gives its OWN being in some history at some moment, that
self-directed exercise falls under the supplied efficient cause of the agent's
esse. This is the explicit cross-sense premise required for the already checked
no-self-cause theorem. It concerns only the self-edge, not distinct agents.

**Index collapse.** The antecedent `F.GivesAt v c c t` is indexed to a history
`v` (any history of the frame, not only those accessible from the selected
world) and a moment `t`; the consequent `EfficientlyCausesIn c c F.esse` has
neither index. On the here-and-now gloss of EFFICIENT_CAUSING_2 (definition
69c0b23e) the bridge would turn self-giving in a merely possible history into
an actual, present efficient self-causation, which is not intended. In the
arguments that use this bridge, `EfficientlyCausesIn` is therefore read world-
and time-neutrally: `c` is, in some history at some moment, an efficient cause
of `x`'s being `r`. On that reading the reused Second Way premises are used
modally as well: nothing is, in any history, its own efficient cause
(`NothingIsEfficientCauseOfItselfReading`), and whatever is in some history an
efficient cause of `x` is simply prior to `x`
(`EfficientCauseIsPriorToEffectReading`, with the unindexed `PriorSimply`).
That is stronger than their actual-world gloss; the source's *nec est
possibile* is a candidate basis for the modal reading of the first, with
attribution deferred. Restricting `v` to accessible histories would not remove
the need for this reading, because the consequent stays index-free. -/
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
