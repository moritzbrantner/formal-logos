module

public import TruthCore.Causality.ComponentFirstness
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round3CogitoBase
public import TruthCore.Causality.CartesianIdeaOfInfinite
public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Modal.ModalGrounding

/-! Restated premises: which coincide and which only look alike (#1926, phase 2)

A consolidation slice. It adds no premise to any existing argument and no
bridge between distinct relations. It records which premises that a survey
reported as restatements of one another are the same proposition over a stated
carrier.

* `ComponentFirstness.ParticipatedHasOtherCause` (ST I q.44 a.1 ad 1) and
  `Round2Grounding.ParticipatedEsseHasDistinctCause` (q.44 a.1 co.) have the
  same body over the same parameters (`participatedCauseReadingsIff`,
  `Iff.rfl`). Both bodies are `CausesIn c x esse` with `c ≠ x`; the
  equivalence holds between the two declarations and does not identify the
  sense tags their records carry.
* `CartesianIdeaOfInfinite.MeditatorThinks I` is
  `Round3CogitoBase.SelectedBearsOccurringThought` at the idea frame's own
  occurrence, bearing and meditator fields (`meditatorThinksIff`, `Iff.rfl`).
* `ModalGrounding.SomeContingentConcreteAt F concrete w` is
  `ContingentBeingNode.SomeActualContingentAt` on the frame's ground profile
  `groundProfile F concrete grounds`, for every `grounds`
  (`someContingentConcreteIff`, `Iff.rfl`).

Each pair stays two records because their sources, carriers or routes differ;
the equivalence is registered, not merged.
-/

@[expose] public section

namespace TruthCore.Causality.RestatedPremises

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ComponentFirstness (ParticipatedHasOtherCause)
open TruthCore.Causality.Round2Grounding (ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.Round3CogitoBase (SelectedBearsOccurringThought)
open TruthCore.Causality.CartesianIdeaOfInfinite (IdeaFrame MeditatorThinks)
open TruthCore.Causality.ContingentBeingNode (SomeActualContingentAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt)

/-- Restated-premise controls: the three registered equivalences, each by
`Iff.rfl` over the stated carrier. -/
def RestatedPremisesControls : Prop :=
  (∀ (B R : Type) (Participated : B → Prop) (CausesIn : B → B → R → Prop) (esse : R),
    ParticipatedHasOtherCause Participated CausesIn esse ↔
      ParticipatedEsseHasDistinctCause Participated CausesIn esse) ∧
  (∀ (B R Episode : Type) (I : IdeaFrame B R Episode),
    MeditatorThinks I ↔ SelectedBearsOccurringThought I.Occurs I.Bears I.me) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W),
    SomeContingentConcreteAt F concrete w ↔
      SomeActualContingentAt (groundProfile F concrete grounds) w)

end TruthCore.Causality.RestatedPremises
