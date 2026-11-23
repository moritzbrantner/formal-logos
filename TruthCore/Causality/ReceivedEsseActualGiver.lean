module

public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Causality.TimeSymmetricGiving
public import TruthCore.Causality.UnderivedNonComposite

/-!
# Received esse and an actually present giver

Fixes the shared CausalityFrame, reading world, CAUSE_2 respect and bearer.
Reception in an intrinsic principle and causing that bearer's esse by a distinct
agent remain different relations. Actuality of the world-free esse-cause is
not built into either relation. See docs/notes/modal-spine.md.

The following stronger endpoint is not asserted as established; its two
support bundles and their OPEN causal/presence interfaces are explicit in the
Results module. The First Way consumes its weaker projection B2, so no
independent first-mover witness is introduced.
-/

@[expose] public section

namespace TruthCore.Causality.ReceivedEsseActualGiver

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- Stronger than B2: each contingent actual bearer has a distinct CAUSE_2 of
its esse which is itself actual at the same selected world. This says nothing
about whether receipt is into an essence, whether the cause is efficient or
sustaining, or whether the giver is itself metaphysically necessary. -/
def ContingentHasActualEsseGiverAt {W B T R : Type}
    (F : CausalityFrame W B T R) (w : W) : Prop :=
  ∀ x, ContingentAt F.history.ontic w x →
    ∃ c, c ≠ x ∧ F.history.ontic.ExistsAt w c ∧ F.CausesIn c x F.esse

end TruthCore.Causality.ReceivedEsseActualGiver
