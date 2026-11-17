module

public import TruthCore.Causality.WholePowerClassification

@[expose] public section
namespace TruthCore.Results.Causality.WholePowerClassification
open TruthCore.Causality.WholePowerClassification

theorem classificationAudit : ClassificationAudit := by
  constructor
  · intro B D OwnBeing Recipient Has Pure OfBeing hWhole hPertain hNoRecipient hPurity n hn d
    constructor
    · intro hd
      exact hPurity n (hNoRecipient n hn) d (hWhole n hn d hd)
    · exact hPertain d
  · intro B D OwnBeing Has Has' OfBeing hWhole hExtend x hx d hd
    exact hExtend x d (hWhole x hx d hd)

theorem modeAudit : ModeAudit := by
  intro B P R p OwnBeing Received Limited Infinite n hn hOwn hScope hReceived hLimited hInfinite hUnlimited
  have hnInfinite := hInfinite n hOwn
  refine ⟨hn, hOwn, hnInfinite, hUnlimited n hnInfinite, ?_⟩
  intro x hx hxn
  obtain ⟨z, hz⟩ := hReceived n x (fun h => hxn h.symm) (hScope x hxn hx)
  have hxLimited := hLimited x z hz
  have hxNotInfinite : ¬ Infinite x := fun h => hUnlimited x h hxLimited
  exact ⟨hxLimited, hxNotInfinite, fun h => hxNotInfinite (hInfinite x h)⟩

end TruthCore.Results.Causality.WholePowerClassification
