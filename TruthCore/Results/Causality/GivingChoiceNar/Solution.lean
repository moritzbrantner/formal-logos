module

public import TruthCore.Causality.GivingChoiceNar
public import TruthCore.Results.Causality.NarDerivation.Solution

@[expose] public section

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
  intro g x root _ grounded necessary k accessible present cell
  exact cstit_actual cell (rigid g x root grounded necessary (world k) accessible present)

theorem nar_of_admissible_cells_and_recipient_exclusion
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete IsGod HasIntellect : B → Prop} {G : W → B → B → Prop} {w : W}
    (common : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (admit : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveWithholdingCells F world concrete G w)
    (exclude : NoAdmissibleWithholdingCellForNecessaryGrounded F world concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  obtain ⟨g, root, reaches⟩ := NarDerivation.commonRoot_of_intellectual _ w IsGod HasIntellect common
  intro x actual necessary
  rcases reaches x actual with same | grounded
  · subst x
    exact root
  · obtain ⟨k, cell⟩ := cells g x root actual grounded
    obtain ⟨accessible, present⟩ := admit g root k
    exact (exclude g x root actual grounded necessary k accessible present cell).elim

end TruthCore.Results.Causality.GivingChoiceNar
