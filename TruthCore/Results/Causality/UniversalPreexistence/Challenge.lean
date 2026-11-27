import TruthCore.Causality.UniversalPreexistence
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Case.Catholicism.AttributesFromEsse

/-!
# Preexistence at the universal source: results

Analyst formulations, attribution deferred; no premise is established.
-/

namespace TruthCore.Results.Causality.UniversalPreexistence

open TruthCore.Causality.UniversalPreexistence
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (CausesAllInGenus PerfectionsOfEffectPreexistInCauseReading
    MaximumInGenusCausesAllInGenusReading ActualityOnlyInsofarAsBeingReading)
open TruthCore.Case.Catholicism
  (UniversalCauseTransfersPerfections GodIsMaximalInBeing GodIsPerfect)
open TruthCore.Causality.CausalMapsBatch1 (CauseOfBeingHasWhatItGives)
open TruthCore.Causality.GodMaximalCausal (GodCausesBeingOfAllOthers)

/-- Universal-source preexistence from universal-scope transfer and
universal-source possession: a universal cause of `x`'s being causes each of
`x`'s perfections (`b26c10a0`), and a universal source has every perfection it
causes in a thing whose being it causes. No nonuniversal transfer is used. -/
theorem universalPreexistenceOfTransferAndPossession {W B T R : Type}
    (F : GradesFrame W B T R)
    (hTransfer : UniversalCauseTransfersPerfections F.InAct F.CausesIn F.esse)
    (hHas : UniversalSourceHasWhatItGives F) :
    UniversalSourcePreexistence F := by
  sorry

/-- Strength order: q.4 a.2 preexistence entails its restriction to universal
sources. -/
theorem universalPreexistenceOfPreexistence {W B T R : Type} (F : GradesFrame W B T R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) :
    UniversalSourcePreexistence F := by
  sorry

/-- Strength order: cause-of-being possession entails its restriction to
universal sources. -/
theorem universalPossessionOfCauseOfBeingPossession {W B T R : Type}
    (F : GradesFrame W B T R)
    (hHas : CauseOfBeingHasWhatItGives F.CausesIn F.InAct F.esse) :
    UniversalSourceHasWhatItGives F := by
  sorry

/-- Sibling of `AttributesFromEsse.perfectFromGodCause` with universal-source
preexistence in place of q.4 a.2 preexistence, which that proof applies only with
GOD_4, the cause of the being of every other being, as the cause. -/
theorem perfectFromGodCauseOfUniversalPreexistence {W B T R : Type}
    (F : GradesFrame W B T R) (IsGod : B → Prop)
    (hCause : GodCausesBeingOfAllOthers IsGod F.CausesIn F.esse)
    (hUniversal : UniversalSourcePreexistence F)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    TruthCore.Case.Catholicism.AttributesFromEsse.PerfectInFrame F IsGod := by
  sorry

/-- Strength order for the mode step: if an agent's power is a more perfect mode
than every other way of having a perfection, it is more perfect than material
potency. -/
theorem agentPowerAboveMaterialPotencyOfEveryOther
    (ModeAbove : HavingMode → HavingMode → Prop)
    (hStrong : AgentPowerAboveEveryOtherMode ModeAbove) :
    AgentPowerAboveMaterialPotency ModeAbove := by
  sorry

/-- The impersonal-source interpretation, checked by decision (with a larger instance budget). -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Causality.UniversalPreexistence
