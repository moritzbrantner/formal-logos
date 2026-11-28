module

public import TruthCore.Causality.GivingChoice
public import TruthCore.Causality.ActualCommonRoot

@[expose] public section

namespace TruthCore.Results.Causality.GivingChoice

open TruthCore.Modal.STIT (BranchingFrame cstit_actual)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.GivingChoice (RootsHaveWithholdingCells RootHistoriesAdmissible)
open TruthCore.Causality.NarDerivation (ActualRootsWithholdEachGrounded)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Modal.PrussPowerPremises (GivesTo)

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

/-- Structural boundary (#2103): when the profile has at most one actual root
at `w`, some branching frame, moment and history-to-world map satisfy both
STIT premises exactly when premise (a) holds. The converse uses the discrete
choice partition, whose cells are single histories, with one history for each
root, grounded concretum and withholding witness. With the frame and map
unconstrained the cell structure adds nothing to (a). Not a registered result. -/
theorem cellsRepresentationIff {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (unique : ∀ g g', ActualRoot (groundProfile F concrete G) w g →
      ActualRoot (groundProfile F concrete G) w g' → g = g') :
    (∃ (M H : Type) (C : BranchingFrame M H B) (m : M) (world : C.Through m → W),
        RootHistoriesAdmissible F world concrete G w ∧
          RootsHaveWithholdingCells F world concrete G w) ↔
      ActualRootsWithholdEachGrounded F concrete G w := by
  constructor
  · rintro ⟨M, H, C, m, world, admissible, cells⟩
    exact root_withholding_of_cells admissible cells
  · intro withhold
    let H := {t : B × B × W // ActualRoot (groundProfile F concrete G) w t.1 ∧
      F.history.ontic.frame.access w t.2.2 ∧ F.history.ontic.ExistsAt t.2.2 t.1 ∧
      ¬ GivesTo F t.2.2 t.1 t.2.1}
    let C : BranchingFrame Unit H B :=
      ⟨fun _ _ => True, fun _ _ => ⟨Eq, ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩⟩⟩
    refine ⟨Unit, H, C, (), fun k => k.1.1.2.2, ?_, ?_⟩
    · intro g root k
      obtain ⟨⟨⟨n, x, v⟩, nRoot, access, present, _⟩, _⟩ := k
      exact ⟨access, unique n g nRoot root ▸ present⟩
    · intro g x root actual grounded
      obtain ⟨v, access, present, notGiving⟩ := withhold g x root actual grounded
      refine ⟨⟨⟨(g, x, v), root, access, present, notGiving⟩, trivial⟩, ?_⟩
      intro j same
      cases same
      exact notGiving

/-- A common actual root leaves no second actual root, so the unique-root
hypothesis of `cellsRepresentationIff` holds on the common-root route. -/
theorem uniqueRootOfCommonRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (common : TruthCore.Causality.ActualCommonRoot.ActualCommonRootAt
      (groundProfile F concrete G) w) :
    ∀ g g', ActualRoot (groundProfile F concrete G) w g →
      ActualRoot (groundProfile F concrete G) w g' → g = g' := by
  obtain ⟨n, _, reach⟩ := common
  have toN : ∀ r, ActualRoot (groundProfile F concrete G) w r → r = n := by
    intro r root
    rcases reach r root.1 with same | grounded
    · exact same
    · exact absurd grounded (root.2 n)
  intro g g' root root'
  exact (toN g root).trans (toN g' root').symm

end TruthCore.Results.Causality.GivingChoice
