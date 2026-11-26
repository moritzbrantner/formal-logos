module

public import TruthCore.Causality.MathlibBridges
public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Causality.SelectedSourcePath

/-! Replace each edge by a nonempty finite path on the same carrier. This
preserves sources, reachability, and accessibility. The strict one-step fork
rule depends on the selected edge relation. -/

@[expose] public section

namespace TruthCore.Causality.GroundingEdgeScope
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (GroundAncestor)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedAncestry (Cone)
open TruthCore.Causality.SelectedSourcePath (ForksJoinInOneStep coneGraph selectedNode)
open TruthCore.Causality.WorldSourceRegress (SourcePath)
open TruthCore.Logic.Regress (Graph)
open Relation (ReflTransGen TransGen)

variable {N : Type}

/-- On the original carrier, each nonempty finite path becomes one edge. -/
def pathGraph (G : Graph N) : Graph N := ⟨TransGen G.edge⟩

theorem source_pathGraph_iff (G : Graph N) (s : N) :
    (pathGraph G).Source s ↔ G.Source s := by
  constructor
  · intro hs
    rintro ⟨y, hy⟩
    exact hs ⟨y, .single hy⟩
  · intro hs
    rintro ⟨y, hy⟩
    change TransGen G.edge y s at hy
    cases hy with
    | single h => exact hs ⟨_, h⟩
    | tail _ h => exact hs ⟨_, h⟩

theorem reachable_pathGraph_iff (G : Graph N) (s x : N) :
    ReflTransGen (pathGraph G).edge s x ↔ ReflTransGen G.edge s x := by
  change ReflTransGen (TransGen G.edge) s x ↔ ReflTransGen G.edge s x
  rw [Relation.reflTransGen_transGen]

theorem sourcePath_pathGraph_iff (G : Graph N) (x : N) :
    SourcePath (pathGraph G) x ↔ SourcePath G x := by
  have path (s : N) : FiniteCausalPath (pathGraph G).edge x s ↔
      FiniteCausalPath G.edge x s := by
    rw [finiteCausalPath_iff_reflTransGen, finiteCausalPath_iff_reflTransGen]
    rw [Relation.reflTransGen_swap (r := (pathGraph G).edge),
      Relation.reflTransGen_swap (r := G.edge)]
    exact reachable_pathGraph_iff G s x
  simp only [SourcePath, path, source_pathGraph_iff]

theorem accessible_pathGraph_iff (G : Graph N) (x : N) :
    Acc (pathGraph G).edge x ↔ Acc G.edge x := acc_transGen_iff

theorem wellFounded_pathGraph_iff (G : Graph N) :
    WellFounded (pathGraph G).edge ↔ WellFounded G.edge :=
  ⟨fun h => ⟨fun x => (accessible_pathGraph_iff G x).mp (h.apply x)⟩,
    WellFounded.transGen⟩

private theorem source_fork_has_no_join (G : Graph N) {s y : N} (hs : G.Source s) :
    ¬ ∃ k, G.edge k y ∧ G.edge k s := fun ⟨k, _, hks⟩ => hs ⟨k, hks⟩

/-- An explicit fork with a source as one branch violates the strict rule. -/
theorem not_forksJoinInOneStep_of_source_fork (G : Graph N) {s x y : N}
    (hs : G.Source s) (hsx : G.edge s x) (hy : G.edge y x) (hne : y ≠ s) :
    ¬ ForksJoinInOneStep G :=
  fun hFork => source_fork_has_no_join G hs (hFork x y s hy hsx hne)

/-- A source that is an immediate supplier of `x` can only satisfy the local
fork rule when it is the sole immediate supplier. No edge can enter it. -/
theorem localForks_iff_only_source_parent (G : Graph N) {s x : N}
    (hs : G.Source s) (hsx : G.edge s x) :
    (∀ y z, G.edge y x → G.edge z x → y ≠ z → ∃ k, G.edge k y ∧ G.edge k z) ↔
      ∀ y, G.edge y x → y = s := by
  constructor
  · intro hFork y hy
    classical
    by_contra hne
    exact source_fork_has_no_join G hs (hFork y s hy hsx hne)
  · intro hOnly y z hy hz hne
    exact (hne ((hOnly y hy).trans (hOnly z hz).symm)).elim

/-- The one-step rule at `x` on the path graph holds exactly when `s` is its
only nonempty-path ancestor. -/
theorem localForks_pathGraph_iff (G : Graph N) {s x : N}
    (hs : G.Source s) (hsx : TransGen G.edge s x) :
    (∀ y z, (pathGraph G).edge y x → (pathGraph G).edge z x → y ≠ z →
      ∃ k, (pathGraph G).edge k y ∧ (pathGraph G).edge k z) ↔
      ∀ y, TransGen G.edge y x → y = s :=
  localForks_iff_only_source_parent (pathGraph G) ((source_pathGraph_iff G s).mpr hs) hsx

/-- If the carrier is the ancestry of `x`, the same criterion decides the
whole-graph rule. The only possible recipients are `x` and the source. -/
theorem forks_pathGraph_iff_of_reaches (G : Graph N) {s x : N}
    (hs : G.Source s) (hsx : TransGen G.edge s x)
    (hReach : ∀ y, ReflTransGen G.edge y x) :
    ForksJoinInOneStep (pathGraph G) ↔ ∀ y, TransGen G.edge y x → y = s := by
  constructor
  · intro hFork
    exact (localForks_pathGraph_iff G hs hsx).mp (hFork x)
  · intro hOnly a y z hy hz hne
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp (hReach a) with hax | ha
    · subst a
      exact (localForks_pathGraph_iff G hs hsx).mpr hOnly y z hy hz hne
    · have has := hOnly a ha
      subst a
      exact ((source_pathGraph_iff G s).mpr hs ⟨y, hy⟩).elim

private theorem reachesSelected {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) (y : {b // Cone m w x.val b}) :
    ReflTransGen (coneGraph m w x.val).edge y (selectedNode m w x) := by
  have lift (a : B) (h : GroundAncestor m w a x.val) :
      ∃ a' : {b // Cone m w x.val b}, a'.val = a ∧
        ReflTransGen (coneGraph m w x.val).edge a' (selectedNode m w x) := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨selectedNode m w x, rfl, .refl⟩
    | head hEdge hTail ih =>
      obtain ⟨b, hb, hPath⟩ := ih
      refine ⟨⟨_, ⟨hEdge.1, hEdge.2.1⟩, .head hEdge hTail⟩, rfl, .head ?_ hPath⟩
      simpa only [coneGraph, hb] using hEdge.2.2
  obtain ⟨a, ha, hPath⟩ := lift y.val y.property.2
  exact Subtype.ext ha ▸ hPath

/-- On the complete selected cone, changing the edges to positive ancestral
paths makes the global fork rule equivalent to having just one positive
ancestor of the selected bearer, whenever a source positively reaches it. -/
theorem selectedForks_pathGraph_iff {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) {s : {b // Cone m w x.val b}}
    (hs : (coneGraph m w x.val).Source s)
    (hsx : TransGen (coneGraph m w x.val).edge s (selectedNode m w x)) :
    ForksJoinInOneStep (pathGraph (coneGraph m w x.val)) ↔
      ∀ y, TransGen (coneGraph m w x.val).edge y (selectedNode m w x) → y = s :=
  forks_pathGraph_iff_of_reaches (coneGraph m w x.val) hs hsx (reachesSelected m w x)

private def chain : Graph (Fin 3) := ⟨ReflexiveDependenceScope.Control.chainPrior⟩

private theorem chain_edge_iff (y x : Fin 3) : chain.edge y x ↔ y.val + 1 = x.val := by
  unfold chain ReflexiveDependenceScope.Control.chainPrior ReflexiveDependenceScope.Control.chainD
  revert y x
  decide

/-- On the same three vertices `0 → 1 → 2`, two distinct branches appear at
`2` when paths count as edges. No path can enter the source `0`. -/
theorem threeVertexChainSeparates :
    ∃ (G : Graph (Fin 3)), G.Source 0 ∧ G.edge 0 1 ∧ G.edge 1 2 ∧
      ForksJoinInOneStep G ∧ ¬ ForksJoinInOneStep (pathGraph G) := by
  have hSource : chain.Source 0 := by
    rintro ⟨y, hy⟩
    have h := (chain_edge_iff y 0).mp hy
    exact Nat.succ_ne_zero y.val h
  have h01 : chain.edge 0 1 := (chain_edge_iff 0 1).mpr rfl
  have h12 : chain.edge 1 2 := (chain_edge_iff 1 2).mpr rfl
  refine ⟨chain, hSource, h01, h12, ?_, ?_⟩
  · intro x y z hy hz hne
    have hyz : y.val + 1 = z.val + 1 :=
      ((chain_edge_iff y x).mp hy).trans ((chain_edge_iff z x).mp hz).symm
    exact (hne (Fin.ext (Nat.succ.inj hyz))).elim
  · exact not_forksJoinInOneStep_of_source_fork (pathGraph chain)
      ((source_pathGraph_iff chain 0).mpr hSource) (.tail (.single h01) h12) (.single h12)
      (by decide : (1 : Fin 3) ≠ 0)

end TruthCore.Causality.GroundingEdgeScope
