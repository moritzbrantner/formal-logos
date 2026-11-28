import TruthCore.Results.Causality.GivingChoiceNar.Solution

namespace TruthCore.Results.Causality.GivingChoiceNecessary

open TruthCore.Modal.STIT (BranchingFrame)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.GivingChoice (RootHistoriesAdmissible RootsHaveWithholdingCells)
open TruthCore.Causality.GivingChoiceNar (NoAdmissibleWithholdingCellForNecessaryGrounded
  RootsHaveNecessaryWithholdingCells)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.HolderRootIdentification (NecessaryActualConcretaAreRoots)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)

theorem necessary_cells_of_all_cells
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete : B → Prop} {G : W → B → B → Prop} {w : W}
    (cells : RootsHaveWithholdingCells F world concrete G w) :
    RootsHaveNecessaryWithholdingCells F world concrete G w := by
  sorry

theorem nar_of_necessary_cells_and_recipient_exclusion
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete IsGod HasIntellect : B → Prop} {G : W → B → B → Prop} {w : W}
    (common : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (admit : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveNecessaryWithholdingCells F world concrete G w)
    (exclude : NoAdmissibleWithholdingCellForNecessaryGrounded F world concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  sorry

end TruthCore.Results.Causality.GivingChoiceNecessary
