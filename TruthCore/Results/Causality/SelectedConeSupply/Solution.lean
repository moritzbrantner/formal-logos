module

public import TruthCore.Causality.SelectedConeSupply
public import TruthCore.Causality.MathlibBridges

@[expose] public section

open scoped ENNReal

namespace TruthCore.Results.Causality.SelectedConeSupply
open TruthCore.Causality (FiniteCausalPath finiteCausalPath_iff_reflTransGen)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.FiniteThroughput
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.ReceiptMatching
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.SelectedConeSupply
open TruthCore.Causality.SelectedSourcePath
open TruthCore.Causality.WorldSourceRegress (SourcePath overlap)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic.RootDescent (acc_of_map acc_of_subtype)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

variable {W B E N : Type}

private theorem sourcePath_of_actualPath {m : Profile W B} {w : W}
    {x s : {b // ActualConcrete m w b}} (path : GroundAncestor m w s.val x.val)
    (root : ∀ y, ¬ ActualConcreteGround m w y s.val) :
    HasSelectedSourcePath m w x := by
  have actual {y : B} (path : GroundAncestor m w y x.val) : ActualConcrete m w y := by
    cases path using Relation.ReflTransGen.head_induction_on with
    | refl => exact x.property
    | head edge _ _ => exact ⟨edge.1, edge.2.1⟩
  have liftPath {y : B} (hy : ActualConcrete m w y) (h : GroundAncestor m w y x.val) :
      FiniteCausalPath (coneGraph m w x.val).edge (selectedNode m w x) ⟨y, hy, h⟩ := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .same _
    | head edge rest ih =>
      apply (finiteCausalPath_iff_reflTransGen _ _ _).mpr
      exact ((finiteCausalPath_iff_reflTransGen _ _ _).mp
        (ih (actual rest))).tail edge.2.2
  refine ⟨⟨s.val, s.property, path⟩, liftPath s.property path, ?_⟩
  rintro ⟨y, edge⟩
  exact root y.val ⟨y.property.1.1, y.property.1.2, edge⟩

theorem sourcePath_of_receiptExit (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (sender receiver : E → {b // ActualConcrete m w b})
    (deficit : UnmatchedUpstream) (covered : GroundedCanMatch m w sender receiver)
    (exit : SelectedReceiptExit m w x sender receiver) :
    HasSelectedSourcePath m w x := by
  obtain ⟨align, mark, rfl, noReturn, finite⟩ := exit
  obtain ⟨s, path, unmatched⟩ := deficit sender receiver mark noReturn finite
  have endPath : Reaches sender receiver s (receiver mark) :=
    Relation.ReflTransGen.tail path ⟨mark, rfl, rfl⟩
  refine sourcePath_of_actualPath (m := m) (w := w) (s := s) (endPath.lift Subtype.val ?_) ?_
  · rintro a b ⟨e, rfl, rfl⟩
    exact ⟨(sender e).property.1, (sender e).property.2, align e⟩
  · exact fun y hy => unmatched (covered s ⟨y, hy⟩)

theorem sourcePath_of_throughputExit (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (flow : {b // ActualConcrete m w b} → {b // ActualConcrete m w b} → ℝ≥0∞)
    (cut : ReturnOrNetExport) (covered : GroundedExportCovered m w flow)
    (exit : SelectedThroughputExit m w x flow) :
    HasSelectedSourcePath m w x := by
  obtain ⟨align, finite, a, edge, noReturn⟩ := exit
  obtain ⟨s, path, excess⟩ := (cut flow finite edge).resolve_left noReturn
  refine sourcePath_of_actualPath (m := m) (w := w) (s := s)
    ((path.tail edge).lift Subtype.val fun u v h => ⟨u.property.1, u.property.2, align u v h⟩) ?_
  exact fun y hy => (not_le_of_gt excess) (covered s ⟨y, hy⟩)

end TruthCore.Results.Causality.SelectedConeSupply
