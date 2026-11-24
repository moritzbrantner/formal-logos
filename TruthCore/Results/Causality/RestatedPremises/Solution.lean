module

public import TruthCore.Causality.RestatedPremises

/-!
# Restated premises: three equivalences (#1926)

The controls prove the three registered equivalences by `Iff.rfl`, each over
its stated carrier. No premise is proved here.
-/

@[expose] public section

namespace TruthCore.Results.Causality.RestatedPremises

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.RestatedPremises
open TruthCore.Causality.ComponentFirstness (ParticipatedHasOtherCause)
open TruthCore.Causality.Round2Grounding (ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.Round3CogitoBase (SelectedBearsOccurringThought)
open TruthCore.Causality.CartesianIdeaOfInfinite (IdeaFrame MeditatorThinks)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt)

variable {W B T R : Type}

/-- The ad 1 and co. readings of q.44 a.1 are the same proposition. -/
theorem participatedCauseReadingsIff {B R : Type} (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) :
    ParticipatedHasOtherCause Participated CausesIn esse ↔
      ParticipatedEsseHasDistinctCause Participated CausesIn esse :=
  Iff.rfl

/-- The meditator's cogito is the selected-bearer premise at the idea frame's
fields. -/
theorem meditatorThinksIff {B R Episode : Type} (I : IdeaFrame B R Episode) :
    MeditatorThinks I ↔ SelectedBearsOccurringThought I.Occurs I.Bears I.me :=
  Iff.rfl

/-- Some contingent concretum on a frame is the same proposition on its ground
profile, whatever the grounding relation. -/
theorem someContingentConcreteIff (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W) :
    SomeContingentConcreteAt F concrete w ↔
      SomeActualContingentAt (groundProfile F concrete grounds) w :=
  Iff.rfl

/-- The restated-premise controls. -/
theorem restatedPremisesControls : RestatedPremisesControls :=
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩

end TruthCore.Results.Causality.RestatedPremises
