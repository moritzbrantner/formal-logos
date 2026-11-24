import TruthCore.Causality.RestatedPremises

/-!
# Restated premises: instances of Aristotelian grounding and equivalences (#1926)

The universal Aristotelian grounding principle entails two of its
single-proposition instances that the Pruss routes use as bare premises, by
instantiation only. The controls prove the three registered equivalences by
`Iff.rfl`, show that the three grounding instances hold on a frame where the
universal principle fails, and that the universal principle is satisfiable on
the same frame. No premise is proved here.
-/

namespace TruthCore.Results.Causality.RestatedPremises

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.RestatedPremises
open TruthCore.Causality.ComponentFirstness (ParticipatedHasOtherCause)
open TruthCore.Causality.Round2Grounding (ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.Round3CogitoBase (SelectedBearsOccurringThought)
open TruthCore.Causality.CartesianIdeaOfInfinite (IdeaFrame MeditatorThinks)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.ModalGrounding (ActualAbsenceGrounded SomeContingentConcreteAt
  NoActualContingentConcreteIn NoContingentConcreteIn)
open TruthCore.Modal.PrussPowerPremises (ActualityGroundedAtAbsenceWorlds)

/-- The universal grounding principle gives P1′, its instance at `w` for the
joint absence of the concreta contingent at `w`. Instantiation only. -/
theorem actualAbsenceGroundedOfEverywhere (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hAll : AristotelianGroundingEverywhere F PowerFor) :
    ActualAbsenceGrounded F PowerFor concrete w := by
  sorry

/-- The universal grounding principle gives grounding, at each absence world,
of `w`'s obtaining. Instantiation only. -/
theorem actualityGroundedAtAbsenceWorldsOfEverywhere (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hAll : AristotelianGroundingEverywhere F PowerFor) :
    ActualityGroundedAtAbsenceWorlds F PowerFor concrete w := by
  sorry

/-- The ad 1 and co. readings of q.44 a.1 are the same proposition. -/
theorem participatedCauseReadingsIff {B R : Type} (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) :
    ParticipatedHasOtherCause Participated CausesIn esse ↔
      ParticipatedEsseHasDistinctCause Participated CausesIn esse := by
  sorry

/-- The meditator's cogito is the selected-bearer premise at the idea frame's
fields. -/
theorem meditatorThinksIff {B R Episode : Type} (I : IdeaFrame B R Episode) :
    MeditatorThinks I ↔ SelectedBearsOccurringThought I.Occurs I.Bears I.me := by
  sorry

/-- Some contingent concretum on a frame is the same proposition on its ground
profile, whatever the grounding relation. -/
theorem someContingentConcreteIff (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W) :
    SomeContingentConcreteAt F concrete w ↔
      SomeActualContingentAt (groundProfile F concrete grounds) w := by
  sorry

namespace Control

open TruthCore.Causality.RestatedPremises.Control
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 allC)

end Control

/-- The restated-premise controls. -/
theorem restatedPremisesControls : RestatedPremisesControls := by
  sorry

end TruthCore.Results.Causality.RestatedPremises
