module

public import TruthCore.Causality.RootGroundComposition

@[expose] public section

namespace TruthCore.Results.Causality.RootGroundComposition

open TruthCore.Causality (FiniteCausalPath)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.RootGroundComposition (RootGroundsComposeAt)
open TruthCore.Causality.SourceForest (RootedAtUniqueSource)


/-- Compress each finite path on the actual grounding graph, keeping the
source, world and edge relation fixed. -/
theorem directRootOfAncestry {W B : Type} (m : Profile W B) (w : W)
    (hAncestry : RootedAtUniqueSource (graph m w))
    (hCompose : RootGroundsComposeAt m w) :
    ActualCommonRootAt m w := by
  obtain ⟨r, hSource, _, reach⟩ := hAncestry
  have hRoot : ActualRoot m w r.val :=
    ⟨r.property, fun y hy => hSource ⟨⟨y, hy.1, hy.2.1⟩, hy.2.2⟩⟩
  have compress {x s : {b // ActualConcrete m w b}}
      (p : FiniteCausalPath (graph m w).edge x s) :
      ActualRoot m w s.val → x.val = s.val ∨ ActualConcreteGround m w s.val x.val := by
    induction p with
    | same => exact fun _ => Or.inl rfl
    | @link x y s edge _ ih =>
      intro hs
      rcases ih hs with hSame | hFirst
      · exact Or.inr (hSame ▸ ⟨y.property.1, y.property.2, edge⟩)
      · exact Or.inr (hCompose s.val y.val x.val hs x.property
          hFirst ⟨y.property.1, y.property.2, edge⟩)
  exact ⟨r.val, hRoot, fun x hx => compress (reach ⟨x, hx⟩) hRoot⟩

end TruthCore.Results.Causality.RootGroundComposition
