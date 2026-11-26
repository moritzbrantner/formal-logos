import TruthCore.Causality.GivingChoiceNar
import TruthCore.Results.Causality.NarDerivation.Solution

namespace TruthCore.Results.Causality.GivingChoiceNar

open TruthCore.Modal.STIT (BranchingFrame cstit_actual)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.GivingChoice (RootHistoriesAdmissible RootsHaveWithholdingCells)
open TruthCore.Causality.GivingChoiceNar (NoAdmissibleWithholdingCellForNecessaryGrounded)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.HolderRootIdentification (NecessaryActualConcretaAreRoots)
open TruthCore.Causality.NarDerivation (ActualRootsGiveNecessaryGroundedWherever)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)

theorem rigidity_excludes_admissible_withholding_cell
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete : B → Prop} {G : W → B → B → Prop} {w : W}
    (rigid : ActualRootsGiveNecessaryGroundedWherever F concrete G w) :
    NoAdmissibleWithholdingCellForNecessaryGrounded F world concrete G w := by
  sorry

theorem nar_of_admissible_cells_and_recipient_exclusion
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete IsGod HasIntellect : B → Prop} {G : W → B → B → Prop} {w : W}
    (common : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (admit : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveWithholdingCells F world concrete G w)
    (exclude : NoAdmissibleWithholdingCellForNecessaryGrounded F world concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  sorry

end TruthCore.Results.Causality.GivingChoiceNar
