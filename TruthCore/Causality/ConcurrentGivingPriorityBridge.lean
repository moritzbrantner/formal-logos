module

public import TruthCore.Causality.MetricBeginningArrival
public import TruthCore.Causality.SelfCausationPriority

/-!
A causal-sense bridge for the modal Arrival B no-self-giving premise, with
Second Way support. Analyst formulation, attribution deferred.

**Registered (indexed) route.** Efficient causation is a supplied relation
`EfficientlyCausesAt v t c x r`, indexed by a history `v` and a moment `t`: in
history `v` at moment `t`, `c` is an efficient cause of `x`'s being `r`. For
each fixed `v` and `t` it is the here-and-now efficient causing of
EFFICIENT_CAUSING_2 (definition 69c0b23e), read in that history at that
moment. Giving of being (time-indexed `GivesAt`) and efficient causation are
DISTINCT senses; the only passage between them is the self-edge bridge
`SelfGivingIsEfficientSelfCauseAt`, which keeps both indices, so nothing is
moved from one history or moment to another. The two Second Way premises are
stated as their own all-accessible-histories, all-moments versions
(`NoEfficientSelfCauseOnAccessible`, `EfficientCauseIsPriorOnAccessible`),
not as re-readings of the existing selected-time statements. No
identification of the frame's `CausesIn` (cause of perfection) is made. The
simple-priority relation is the single unindexed frame field `F.PriorSimply`.

**Superseded (unregistered).** `SelfGivingIsEfficientSelfCause` maps
`GivesAt v c c t` to an index-free `EfficientlyCausesIn c c F.esse`. It and the
theorems over it are kept because the Challenge is frozen, but no corpus
argument uses them: they required re-reading the existing selected-time
premises modally.

All application premises remain OPEN; no claim of metaphysical establishment.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.MetricBeginningArrival (NoSelfGivingOnAccessible)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NothingIsEfficientCauseOfItselfReading EfficientCauseIsPriorToEffectReading)

/-- SUPERSEDED, not used by any corpus argument. Self-giving in any history at
any moment is mapped to an index-free efficient self-cause. On the here-and-now
gloss of EFFICIENT_CAUSING_2 (definition 69c0b23e) that would turn self-giving
in a merely possible history into an actual, present efficient self-cause; the
indices are kept in `SelfGivingIsEfficientSelfCauseAt`, which replaces it. -/
def SelfGivingIsEfficientSelfCause {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ v c t, F.GivesAt v c c t → EfficientlyCausesIn c c F.esse

/-- Self-edge bridge, indexed: in every history `v` accessible from `w` and at
every moment `t`, if `c` gives its OWN being (`GivesAt v c c t`), then in `v`
at `t` `c` is an efficient cause of its own being
(`EfficientlyCausesAt v t c c F.esse`). It concerns only the self-edge, not
distinct agents, and moves nothing between histories or moments. -/
def SelfGivingIsEfficientSelfCauseAt {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesAt : W → T → B → B → R → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v →
    ∀ c t, F.GivesAt v c c t → EfficientlyCausesAt v t c c F.esse

/-- In no history accessible from `w`, at no moment, is anything its own
efficient cause, in any respect. The all-histories, all-moments version of
the selected-time `NothingIsEfficientCauseOfItselfReading`. It is stronger than
that statement only given that `w` is accessible from itself (accessibility is
not reflexive by construction) and that the unindexed relation is read as
`EfficientlyCausesAt w t` at a selected moment `t`.
Analyst statement, attribution deferred (the *nec est possibile* of ST I q.2
a.3 is an unchecked candidate basis). -/
def NoEfficientSelfCauseOnAccessible {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesAt : W → T → B → B → R → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → ∀ t,
    NothingIsEfficientCauseOfItselfReading (EfficientlyCausesAt v t)

/-- In every history accessible from `w` and at every moment, whatever is then
and there an efficient cause of `x` is simply prior to `x` (the unindexed frame
field `F.PriorSimply`). The all-histories, all-moments version of
`EfficientCauseIsPriorToEffectReading`. Analyst statement, attribution
deferred: the Aquinas claim on the selected-time statement does not extend to
it. -/
def EfficientCauseIsPriorOnAccessible {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesAt : W → T → B → B → R → Prop) (w : W) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → ∀ t,
    EfficientCauseIsPriorToEffectReading (EfficientlyCausesAt v t) F.PriorSimply

namespace Control
open TruthCore.Causality.MetricBeginningArrival.Control (selfGivingFrame)
open TruthCore.Causality.MetricGrimReaper.Control (PosReal)

def noEfficientCause (_ _ : Int) (_ : Unit) : Prop := False

/-- Control for the superseded index-free bridge. In the self-giving model,
efficient causation and simple priority are empty, so both priority premises
hold; the missing bridge is exactly what permits self-GivesAt. -/
def Certificate : Prop :=
  TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
    noEfficientCause selfGivingFrame.PriorSimply ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading
    selfGivingFrame.PriorSimply ∧
  ¬ SelfGivingIsEfficientSelfCause selfGivingFrame noEfficientCause ∧
  ¬ NoSelfGivingOnAccessible selfGivingFrame true

/-- No efficient causation in any history at any moment. -/
def noIndexedEfficientCause (_ : Bool) (_ : PosReal) (_ _ : Int) (_ : Unit) : Prop :=
  False

/-- Indexed omission control. In the self-giving model with empty indexed
efficient causation and empty simple priority, both indexed Second Way premises
and nothing-prior-to-itself hold, and so does indexed no efficient
self-causation, while the indexed bridge and no-self-giving fail. So the bridge
cannot be omitted. Logical omission control only. -/
def IndexedCertificate : Prop :=
  EfficientCauseIsPriorOnAccessible selfGivingFrame noIndexedEfficientCause true ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading
    selfGivingFrame.PriorSimply ∧
  NoEfficientSelfCauseOnAccessible selfGivingFrame noIndexedEfficientCause true ∧
  ¬ SelfGivingIsEfficientSelfCauseAt selfGivingFrame noIndexedEfficientCause true ∧
  ¬ NoSelfGivingOnAccessible selfGivingFrame true

end Control
end TruthCore.Causality.ConcurrentGivingPriorityBridge
