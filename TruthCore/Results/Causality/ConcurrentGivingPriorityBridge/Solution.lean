module

public import TruthCore.Causality.ConcurrentGivingPriorityBridge
public import TruthCore.Results.Causality.SelfCausationPriority.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.MetricBeginningArrival (NoSelfGivingOnAccessible)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- SUPERSEDED, not registered in the corpus. Over the index-free bridge
`SelfGivingIsEfficientSelfCause`, the hypothesis `NothingIsEfficientCauseOfItselfReading`
would have to be read in no history at no moment, which is stronger than the
selected-time statement it binds to. Replaced by
`noSelfGivingFromIndexedNoSelfCause`. -/
theorem noSelfGivingFromNoSelfCause {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) (w : W)
    (hBridge : SelfGivingIsEfficientSelfCause F EfficientlyCausesIn)
    (hNoSelfCause : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) :
    NoSelfGivingOnAccessible F w := by
  intro v _ c t hGive
  exact hNoSelfCause c F.esse (hBridge v c t hGive)

/-- SUPERSEDED, not registered in the corpus: it would use the selected-time
priority premise under a world- and time-neutral reading. Replaced by
`indexedNoSelfCauseFromPriority` composed with
`noSelfGivingFromIndexedNoSelfCause`. -/
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

/-- The indexed self-edge bridge and indexed no efficient self-causation give
strict no-self-giving throughout the accessible histories. Each `GivesAt v c c
t` is sent to `EfficientlyCausesAt v t c c F.esse` in the SAME history at the
SAME moment, where the second premise excludes it; no index is dropped. -/
theorem noSelfGivingFromIndexedNoSelfCause {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesAt : W → T → B → B → R → Prop) (w : W)
    (hBridge : SelfGivingIsEfficientSelfCauseAt F EfficientlyCausesAt w)
    (hNoSelfCause : NoEfficientSelfCauseOnAccessible F EfficientlyCausesAt w) :
    NoSelfGivingOnAccessible F w := by
  intro v hv c t hGive
  exact hNoSelfCause v hv t c F.esse (hBridge v hv c t hGive)

/-- The Second Way derivation, history by history and moment by moment: if in
every accessible history at every moment an efficient cause is simply prior to
its effect, and nothing is simply prior to itself, then in no accessible
history at no moment is anything its own efficient cause. Reuses
`SelfCausationPriority.noSelfCauseFromPriority` at each history and moment. -/
theorem indexedNoSelfCauseFromPriority {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesAt : W → T → B → B → R → Prop) (w : W)
    (hPrior : EfficientCauseIsPriorOnAccessible F EfficientlyCausesAt w)
    (hNoPrior : NothingPriorToItselfReading F.PriorSimply) :
    NoEfficientSelfCauseOnAccessible F EfficientlyCausesAt w := by
  intro v hv t
  exact TruthCore.Results.Causality.SelfCausationPriority.noSelfCauseFromPriority
    (EfficientlyCausesAt v t) F.PriorSimply (hPrior v hv t) hNoPrior

open TruthCore.Causality.ConcurrentGivingPriorityBridge.Control
open TruthCore.Causality.MetricBeginningArrival.Control (selfGivingFrame)
open TruthCore.Causality.MetricGrimReaper.Control (PosReal)

/-- SUPERSEDED, not registered in the corpus: control for the index-free
bridge `SelfGivingIsEfficientSelfCause`. Replaced by `indexedControls`. -/
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

theorem indexedControls : IndexedCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ h
    exact h.elim
  · intro _ h
    exact h
  · intro _ _ _ _ _ h
    exact h
  · intro hBridge
    exact hBridge true trivial 0 (⟨1, one_pos⟩ : PosReal) rfl
  · intro hNoSelf
    exact hNoSelf true trivial 0 (⟨1, one_pos⟩ : PosReal) rfl

end TruthCore.Results.Causality.ConcurrentGivingPriorityBridge
