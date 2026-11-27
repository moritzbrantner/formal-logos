module

public import TruthCore.Causality.ActualCommonRoot
public import TruthCore.Causality.ActualAncestralSource

@[expose] public section

namespace TruthCore.Causality.RootGroundComposition

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)

/-- Open composition law restricted to edges starting at an actual root.
Every edge is in the same selected relation at the same world. -/
def RootGroundsComposeAt {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ∀ r y x, ActualRoot m w r → ActualConcrete m w x →
    ActualConcreteGround m w r y → ActualConcreteGround m w y x →
    ActualConcreteGround m w r x

end TruthCore.Causality.RootGroundComposition
