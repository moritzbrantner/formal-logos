import TruthCore.Causality.GroundingEdgeScope
import TruthCore.Causality.MathlibBridges
import TruthCore.Results.Causality.WorldSourceRegress.Solution
import TruthCore.Results.Causality.SelectedAncestry.Solution

namespace TruthCore.Results.Causality.SelectedSourcePath
open TruthCore.Causality (FiniteCausalPath finiteCausalPath_iff_reflTransGen)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.SelectedSourcePath
open TruthCore.Causality.SourceForest
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic.RootDescent (acc_of_subtype)

/-- Any finite path ending upstream at a source entails accessibility
at the starting node when all immediate forks in the graph satisfy the rule. -/
theorem accessibleOfSourcePath {N : Type} (G : Graph N) (x : N)
    (hPath : SourcePath G x) (hFork : ForksJoinInOneStep G) : Acc G.edge x := by
  sorry

/-- Any two finite upstream paths to sources from the same starting bearer
have the same endpoint and the same length. -/
theorem maximalPathsAgree {N : Type} (G : Graph N) (hFork : ForksJoinInOneStep G)
    {s t x : N} (hs : G.Source s) (ht : G.Source t)
    (p : SupplierPath G s x)
    (q : SupplierPath G t x) :
    s = t ∧ p.length = q.length := by
  sorry

/-- One rooted path plus the one-step fork rule gives well-foundedness on
the complete selected cone. The source and the forks are of the same graph. -/
theorem coneWellFounded_of_sourcePath {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (hPath : HasSelectedSourcePath m w x) (hFork : SelectedForksJoinInOneStep m w x) :
    ConeWellFounded m w x.val := by
  sorry

/-- The necessary ancestor still uses the existing contingent-grounding
and excluded-middle premises at exactly the same world and selected bearer. -/
theorem necessaryRootAncestor_of_sourcePath {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (hPath : HasSelectedSourcePath m w x) (hFork : SelectedForksJoinInOneStep m w x)
    (hDep : ConeContingentGrounded m w x.val) (hEM : ExcludedMiddle) :
    NecessaryRootAncestor m w x.val := by
  sorry

theorem oneStepForks_of_uniquePredecessor {N : Type} (G : Graph N)
    (hUnique : UniquePredecessor G) : ForksJoinInOneStep G := by
  sorry

/-- The existing diamond really branches at its tip and satisfies the rule. -/
theorem diamondAllowsBranching : ForksJoinInOneStep diamond ∧ ¬ UniquePredecessor diamond := by
  sorry

/-- The existing common-source ray is acyclic and confluent. Even with the
same finitely reachable source from every node, the selected ray start is inaccessible
and fails the strict one-step rule. -/
theorem commonSourceAllowsRegress :
    (actualGraph overlap ()).NoCycles ∧
      RootedAtUniqueSource (actualGraph overlap ()) ∧
      UpstreamConfluent (actualGraph overlap ()) ∧
      ¬ Acc (actualGraph overlap ()).edge overlapNode ∧
      ¬ ForksJoinInOneStep (actualGraph overlap ()) := by
  sorry

/-- On the represented complete cone, replacing a ground edge by any positive
ancestral path preserves access to sources. It makes the strict fork rule
equivalent to having only the source as a positive ancestor of the recipient. -/
theorem ancestralForkCriterion {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) {s : {b // Cone m w x.val b}}
    (hs : (coneGraph m w x.val).Source s)
    (hsx : Relation.TransGen (coneGraph m w x.val).edge s (selectedNode m w x)) :
    ForksJoinInOneStep (TruthCore.Causality.GroundingEdgeScope.pathGraph (coneGraph m w x.val)) ↔
      ∀ y, Relation.TransGen (coneGraph m w x.val).edge y (selectedNode m w x) → y = s := by
  sorry

theorem ancestralEdgeControl :
    ∃ G : Graph (Fin 3), G.Source 0 ∧ G.edge 0 1 ∧ G.edge 1 2 ∧
      ForksJoinInOneStep G ∧ ¬ ForksJoinInOneStep (TruthCore.Causality.GroundingEdgeScope.pathGraph G) := by
  sorry

/-- Every vertex belongs to the selected cone. The middle vertices are
infinitely many distinct immediate suppliers of the tip and each has the
root as immediate supplier. The existing criterion gives well-foundedness. -/
theorem infiniteWidthControl :
    (∀ y, Cone wideConeProfile () .tip y) ∧
      (∃ f : Nat → {b // Cone wideConeProfile () .tip b},
        Function.Injective f ∧ ∀ n,
          (coneGraph wideConeProfile () .tip).edge (f n) (selectedNode wideConeProfile () wideConeTip) ∧
            WideConeGround .root (f n).val) ∧
      HasSelectedSourcePath wideConeProfile () wideConeTip ∧
      SelectedForksJoinInOneStep wideConeProfile () wideConeTip ∧
      ConeWellFounded wideConeProfile () .tip := by
  sorry

end TruthCore.Results.Causality.SelectedSourcePath
