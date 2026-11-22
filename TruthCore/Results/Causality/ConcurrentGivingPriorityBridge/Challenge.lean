import TruthCore.Causality.ConcurrentGivingPriorityBridge
import TruthCore.Results.Causality.SelfCausationPriority.Solution

namespace TruthCore.Results.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.ConcurrentGivingPriorityBridge
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.MetricBeginningArrival (NoSelfGivingOnAccessible)
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem noSelfGivingFromNoSelfCause {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) (w : W)
    (hBridge : SelfGivingIsEfficientSelfCause F EfficientlyCausesIn)
    (hNoSelfCause : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) :
    NoSelfGivingOnAccessible F w := by
  sorry

theorem noSelfGivingFromEfficientPriority {W B T R : Type}
    (F : CausalityFrame W B T R)
    (EfficientlyCausesIn : B → B → R → Prop) (w : W)
    (hBridge : SelfGivingIsEfficientSelfCause F EfficientlyCausesIn)
    (hPrior : EfficientCauseIsPriorToEffectReading
      EfficientlyCausesIn F.PriorSimply)
    (hNoPrior : NothingPriorToItselfReading F.PriorSimply) :
    NoSelfGivingOnAccessible F w := by
  sorry

open TruthCore.Causality.ConcurrentGivingPriorityBridge.Control
open TruthCore.Causality.MetricBeginningArrival.Control (selfGivingFrame)
open TruthCore.Causality.MetricGrimReaper.Control (PosReal)

theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.ConcurrentGivingPriorityBridge
