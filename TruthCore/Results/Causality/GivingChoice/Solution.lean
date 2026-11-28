module

public import TruthCore.Causality.GivingChoice

@[expose] public section

namespace TruthCore.Results.Causality.GivingChoice

open TruthCore.Modal.STIT (BranchingFrame cstit_actual)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.GivingChoice (RootsHaveWithholdingCells RootHistoriesAdmissible)
open TruthCore.Causality.NarDerivation (ActualRootsWithholdEachGrounded)

theorem root_withholding_of_cells
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete : B → Prop} {G : W → B → B → Prop} {w : W}
    (admissible : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveWithholdingCells F world concrete G w) :
    ActualRootsWithholdEachGrounded F concrete G w := by
  intro g x root actual grounded
  obtain ⟨k, cell⟩ := cells g x root actual grounded
  obtain ⟨accessible, existsThere⟩ := admissible g root k
  exact ⟨world k, accessible, existsThere, cstit_actual cell⟩

end TruthCore.Results.Causality.GivingChoice
