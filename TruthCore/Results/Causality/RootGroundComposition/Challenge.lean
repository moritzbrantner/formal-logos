import TruthCore.Causality.RootGroundComposition

namespace TruthCore.Results.Causality.RootGroundComposition

open TruthCore.Causality (FiniteCausalPath)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.RootGroundComposition (RootGroundsComposeAt)
open TruthCore.Causality.SourceForest (RootedAtUniqueSource)

theorem directRootOfAncestry {W B : Type} (m : Profile W B) (w : W)
    (hAncestry : RootedAtUniqueSource (graph m w))
    (hCompose : RootGroundsComposeAt m w) :
    ActualCommonRootAt m w := by
  sorry

end TruthCore.Results.Causality.RootGroundComposition
