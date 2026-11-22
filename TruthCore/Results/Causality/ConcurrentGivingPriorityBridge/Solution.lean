module

public import TruthCore.Causality.ConcurrentGivingPriorityBridge
public import TruthCore.Results.Causality.SelfCausationPriority.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.MetricBeginningArrival (NoSelfGivingOnAccessible)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A more directly reused node in the existing graph says that no being is
its own efficient cause in any respect. Read world- and time-neutrally (in no
history at no moment), as the index-free bridge requires (see
`SelfGivingIsEfficientSelfCause`), and with only that explicit self-edge
bridge, it prohibits strict concurrent self-giving of being throughout the
accessible histories. The modal reading is stronger than the here-and-now gloss
of definition 69c0b23e. The no-self-efficient-cause node retains its
direct-assumption option and its existing priority-based support route. -/
theorem noSelfGivingFromNoSelfCause {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) (w : W)
    (hBridge : SelfGivingIsEfficientSelfCause F EfficientlyCausesIn)
    (hNoSelfCause : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) :
    NoSelfGivingOnAccessible F w := by
  intro v _ c t hGive
  exact hNoSelfCause c F.esse (hBridge v c t hGive)

/-- Explicit causal-sense bridge + the Second Way's two OPEN priority premises
give the strict no-self-GivesAt premise needed by the causal Arrival B route.
This reuses noSelfCauseFromPriority; it does not recreate its proof. The
efficient-cause priority premise is used under the same world- and
time-neutral reading of `EfficientlyCausesIn` as the bridge. -/
theorem noSelfGivingFromEfficientPriority {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) (w : W)
    (hBridge : SelfGivingIsEfficientSelfCause F EfficientlyCausesIn)
    (hPrior : EfficientCauseIsPriorToEffectReading
      EfficientlyCausesIn F.PriorSimply)
    (hNoPrior : NothingPriorToItselfReading F.PriorSimply) :
    NoSelfGivingOnAccessible F w := by
  have hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn :=
    TruthCore.Results.Causality.SelfCausationPriority.noSelfCauseFromPriority
      EfficientlyCausesIn F.PriorSimply hPrior hNoPrior
  exact noSelfGivingFromNoSelfCause F EfficientlyCausesIn w hBridge hNoSelf

open TruthCore.Causality.ConcurrentGivingPriorityBridge.Control
open TruthCore.Causality.MetricBeginningArrival.Control (selfGivingFrame)
open TruthCore.Causality.MetricGrimReaper.Control (PosReal)

theorem controls : Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ h
    exact h.elim
  · intro _ h
    exact h
  · intro hBridge
    have hg : selfGivingFrame.GivesAt true 0 0 (⟨1, one_pos⟩ : PosReal) := rfl
    exact hBridge true 0 (⟨1, one_pos⟩ : PosReal) hg
  · intro hNoSelf
    exact hNoSelf true trivial 0 (⟨1, one_pos⟩ : PosReal) rfl

end TruthCore.Results.Causality.ConcurrentGivingPriorityBridge
