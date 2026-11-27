import TruthCore.Causality.ModeOfBeingMiddleTerm

/-!
# The q.4 a.2 sentence as a middle term: results

Analyst formulations, attribution deferred; no premise is established.
-/

namespace TruthCore.Results.Causality.ModeOfBeingMiddleTerm

open TruthCore.Causality.ModeOfBeingMiddleTerm
open TruthCore.Causality.Grades (GradesFrame)

/-- The transfer pair is equivalent to its composite. Forward: compose. Backward:
read "mode of being" as "had in act". -/
theorem modesPairIffTotalTransfer {W B T R : Type} (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) :
    ModesPairIffTotalTransfer F TotalCauseOfBeing := by
  sorry

/-- The dependence reading moves the whole load of the transfer pair to the
total-cause premise. -/
theorem dependenceReading {W B T R : Type} (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) :
    DependenceReadingShiftsLoad F TotalCauseOfBeing := by
  sorry

/-- The subsistent-esse pair is equivalent to its composite. Forward: compose.
Backward: read "perfection of being" as "pure perfection". -/
theorem ownBeingPairIffEveryPure {B D : Type} (OwnBeing : B → Prop)
    (Has : B → D → Prop) (Pure : D → Prop) :
    OwnBeingPairIffEveryPure OwnBeing Has Pure := by
  sorry

/-- The two profiles, checked by decision. -/
theorem controls : Control.Controls := by
  sorry

/-- R-act₂ is `c4fb87a6` with "perfection of being" read as perfection of esse
(PERFECTION_OF_BEING_2): the two propositions coincide. Evidence for the
`logically_equivalent_to` registration; a definitional identity, not a derivation. -/
theorem intensiveEsseIffPurePertainsToEsse {D : Type} (I : IntensiveEsseFrame D)
    (Pure : D → Prop) :
    IntensiveEsse I Pure ↔
      TruthCore.Causality.WholePowerPerfection.PurePerfectionsPertainToBeing Pure I.OfEsse := by
  sorry

end TruthCore.Results.Causality.ModeOfBeingMiddleTerm
