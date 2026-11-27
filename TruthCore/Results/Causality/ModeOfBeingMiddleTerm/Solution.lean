module

public import TruthCore.Causality.ModeOfBeingMiddleTerm

/-!
# The q.4 a.2 sentence as a middle term: results

Analyst formulations, attribution deferred; no premise is established.
-/

@[expose] public section

namespace TruthCore.Results.Causality.ModeOfBeingMiddleTerm

open TruthCore.Causality.ModeOfBeingMiddleTerm
open TruthCore.Causality.Grades (GradesFrame)

/-- The transfer pair is equivalent to its composite. Forward: compose. Backward:
read "mode of being" as "had in act". -/
theorem modesPairIffTotalTransfer {W B T R : Type} (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) :
    ModesPairIffTotalTransfer F TotalCauseOfBeing := by
  constructor
  · rintro ⟨M, hModes, hTotal⟩ c x r hc hx
    exact hTotal c x r hc (hModes x r hx)
  · intro hComposite
    exact ⟨F.InAct, fun _ _ h => h, hComposite⟩

/-- The dependence reading moves the whole load of the transfer pair to the
total-cause premise. -/
theorem dependenceReading {W B T R : Type} (F : GradesFrame W B T R)
    (TotalCauseOfBeing : B → B → Prop) :
    DependenceReadingShiftsLoad F TotalCauseOfBeing := by
  intro hBeing
  refine ⟨fun x r hx => ⟨hx, hBeing x r hx⟩, ?_⟩
  constructor
  · intro hTotal c x r hc hx
    exact hTotal c x r hc ⟨hx, hBeing x r hx⟩
  · intro hComposite c x r hc hMode
    exact hComposite c x r hc hMode.1

/-- The subsistent-esse pair is equivalent to its composite. Forward: compose.
Backward: read "perfection of being" as "pure perfection". -/
theorem ownBeingPairIffEveryPure {B D : Type} (OwnBeing : B → Prop)
    (Has : B → D → Prop) (Pure : D → Prop) :
    OwnBeingPairIffEveryPure OwnBeing Has Pure := by
  constructor
  · rintro ⟨OfBeing, hWhole, hPure⟩ x hx d hd
    exact hWhole x hx d (hPure d hd)
  · intro hComposite
    exact ⟨Pure, hComposite, fun _ h => h⟩

/-- The two profiles, checked by decision. -/
theorem controls : Control.Controls := by
  dsimp [Control.Controls, OwnBeingHasEveryPurePerfection,
    TruthCore.Causality.WholePowerPerfection.OwnBeingLacksNoPerfectionOfBeing,
    TruthCore.Causality.WholePowerPerfection.PurePerfectionsPertainToBeing,
    Control.ownBeing, Control.pure, Control.hasThin, Control.ofBeingThin, Control.hasAct,
    FiniteEsseReceivedAndLimited, IntensiveEsse,
    TruthCore.Causality.ReceptionLimitation.OwnBeingIsNoRecipient,
    TruthCore.Causality.ReceptionLimitation.NonRecipientDeterminationsArePure,
    Control.recipient, Control.received, Control.limited]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end TruthCore.Results.Causality.ModeOfBeingMiddleTerm
