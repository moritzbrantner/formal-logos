module

public import TruthCore.Causality.GivingChoice

@[expose] public section

namespace TruthCore.Causality.GivingChoiceNar

open TruthCore.Modal.STIT (BranchingFrame Cstit)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.GivingChoice (Produces)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- For the same actual root and necessary grounded actual concretum, an
accessible representative that retains the root cannot represent a cell
that withholds giving to that recipient. Only the representative's mapped
world is tested for accessibility and the root's presence. -/
def NoAdmissibleWithholdingCellForNecessaryGrounded
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    (F : CausalityFrame W B T R) (world : C.Through m → W)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ g x, ActualRoot (groundProfile F concrete G) w g →
    ActualConcrete (groundProfile F concrete G) w x →
    ActualConcreteGround (groundProfile F concrete G) w g x →
    NecessaryAt F.history.ontic w x →
    ∀ k, F.history.ontic.frame.access w (world k) →
      F.history.ontic.ExistsAt (world k) g →
      ¬ Cstit g k (fun j => ¬ Produces F world g x j)

end TruthCore.Causality.GivingChoiceNar
