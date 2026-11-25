module

public import TruthCore.Causality.LocalSourceConfluence
public import TruthCore.Causality.ActualRootUniqueness

@[expose] public section

namespace TruthCore.Results.Causality.LocalSourceConfluence
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.LocalSourceConfluence
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)

theorem confluenceOfLocalForks {N : Type} (G : Graph N)
    (hWF : WellFoundedEdges G) (hFork : LocalForksJoin G) : UpstreamConfluent G := by
  sorry

theorem obstructionOfTwoSources {N : Type} (G : Graph N)
    (hWF : WellFoundedEdges G) (hConnected : WeaklyConnected G)
    (a b : N) (ha : G.Source a) (hb : G.Source b) (hne : a ≠ b) :
    ∃ x y z, G.edge y x ∧ G.edge z x ∧
      ¬ Relation.Join (Relation.ReflTransGen (fun u v => G.edge v u)) y z := by
  sorry

theorem uniqueActualOfSourceAgreement {W B : Type} (m : Profile W B) (w : W)
    (hRoot : ActualRootExistsAt m w) (hAgreement : AtMostOneSource (graph m w)) :
    UniqueActualRootAt m w := by
  sorry

theorem uniqueActualOfLocalForks {W B : Type} (m : Profile W B) (w : W)
    (hRoot : ActualRootExistsAt m w) (hWF : ActualGroundingWF m w)
    (hConnected : WeaklyConnected (graph m w)) (hFork : LocalForksJoin (graph m w)) :
    UniqueActualRootAt m w := by
  sorry

theorem alternatingSources : LadderControl := by
  sorry

end TruthCore.Results.Causality.LocalSourceConfluence
