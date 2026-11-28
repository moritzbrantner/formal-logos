import TruthCore.Causality.ImitabilityGrounding

namespace TruthCore.Results.Causality.ImitabilityGrounding

open TruthCore.Causality.ImitabilityGrounding
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Explanation.PSRStrength (Arena Contingent)
open TruthCore.Explanation.TruthmakerTheories (Making WorldImmanent MakerNecessitation)

theorem noEffectGroundedGiving {W B T R F : Type}
    (K : CausalityFrame W B T R) (A : Arena W B F) (w : W)
    (source : B) (mode production : F) (t : T)
    (hAsym : FactPriorityAsymmetricAt A w)
    (hTrans : FactPriorityTransitiveAt A w)
    (hMode : ModeExplainsProductionAt A w mode production)
    (hGiving : GivingExercisePriorityAt K A w source production t) :
    NoEffectGroundedGivingAt K A w source mode t := by
  sorry

theorem makersOfContingentFactAreContingent {W B F : Type}
    (A : Arena W B F) (M : Making W B F) (w : W) (fact : F)
    (hActual : WorldImmanent A M)
    (hNec : MakerNecessitation A M)
    (hFact : Contingent A w fact) :
    EveryMakerContingentAt A M w fact := by
  sorry

theorem availabilityControl : AvailabilityControl.Certificate := by
  sorry

theorem cycleControls : CycleControl.Certificate := by
  sorry

theorem makerControls : MakerControl.Certificate := by
  sorry

end TruthCore.Results.Causality.ImitabilityGrounding
