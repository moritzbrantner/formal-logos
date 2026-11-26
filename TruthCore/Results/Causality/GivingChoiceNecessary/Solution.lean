module

public import TruthCore.Results.Causality.GivingChoiceNar.Solution

@[expose] public section

namespace TruthCore.Results.Causality.GivingChoiceNecessary

open TruthCore.Modal.STIT (BranchingFrame)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.GivingChoice (RootHistoriesAdmissible RootsHaveWithholdingCells)
open TruthCore.Causality.GivingChoiceNar (NoAdmissibleWithholdingCellForNecessaryGrounded
  RootsHaveNecessaryWithholdingCells)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NarDerivation (ActualRootsGiveNecessaryGroundedWherever)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.HolderRootIdentification (NecessaryActualConcretaAreRoots)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)

theorem necessary_cells_of_all_cells
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete : B → Prop} {G : W → B → B → Prop} {w : W}
    (cells : RootsHaveWithholdingCells F world concrete G w) :
    RootsHaveNecessaryWithholdingCells F world concrete G w := by
  intro g x root actual grounded _
  exact cells g x root actual grounded

/-- Incompatibility at one directly grounded, necessary actual recipient.
The same frame and profile are used throughout. -/
theorem necessary_recipient_conflict
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete : B → Prop} {G : W → B → B → Prop} {w : W}
    (admit : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveNecessaryWithholdingCells F world concrete G w)
    (rigid : ActualRootsGiveNecessaryGroundedWherever F concrete G w)
    (witness : ∃ g x, ActualRoot (groundProfile F concrete G) w g ∧
      ActualConcrete (groundProfile F concrete G) w x ∧
      ActualConcreteGround (groundProfile F concrete G) w g x ∧
      NecessaryAt F.history.ontic w x) : False := by
  obtain ⟨g, x, root, actual, grounded, necessary⟩ := witness
  obtain ⟨k, cell⟩ := cells g x root actual grounded necessary
  obtain ⟨accessible, present⟩ := admit g root k
  exact GivingChoiceNar.rigidity_excludes_admissible_withholding_cell rigid
    g x root actual grounded necessary k accessible present cell

/-- Only bare common-root reach is needed to extend the cell exclusion to NAR. -/
theorem nar_of_common_root_and_necessary_cells
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete : B → Prop} {G : W → B → B → Prop} {w : W}
    (common : ActualCommonRootAt (groundProfile F concrete G) w)
    (admit : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveNecessaryWithholdingCells F world concrete G w)
    (exclude : NoAdmissibleWithholdingCellForNecessaryGrounded F world concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  obtain ⟨g, root, reaches⟩ := common
  intro x actual necessary
  rcases reaches x actual with same | grounded
  · subst x
    exact root
  · obtain ⟨k, cell⟩ := cells g x root actual grounded necessary
    obtain ⟨accessible, present⟩ := admit g root k
    exact (exclude g x root actual grounded necessary k accessible present cell).elim

theorem nar_of_necessary_cells_and_recipient_exclusion
    {W B T R M H : Type} {C : BranchingFrame M H B} {m : M}
    {F : CausalityFrame W B T R} {world : C.Through m → W}
    {concrete IsGod HasIntellect : B → Prop} {G : W → B → B → Prop} {w : W}
    (common : IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect)
    (admit : RootHistoriesAdmissible F world concrete G w)
    (cells : RootsHaveNecessaryWithholdingCells F world concrete G w)
    (exclude : NoAdmissibleWithholdingCellForNecessaryGrounded F world concrete G w) :
    NecessaryActualConcretaAreRoots (groundProfile F concrete G) w := by
  exact nar_of_common_root_and_necessary_cells
    (NarDerivation.commonRoot_of_intellectual _ w IsGod HasIntellect common) admit cells exclude

end TruthCore.Results.Causality.GivingChoiceNecessary
