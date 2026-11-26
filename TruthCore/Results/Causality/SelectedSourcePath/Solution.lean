module

public import TruthCore.Causality.SelectedSourcePath
public import TruthCore.Causality.MathlibBridges
public import TruthCore.Results.Causality.WorldSourceRegress.Solution
public import TruthCore.Results.Causality.SelectedAncestry.Solution

@[expose] public section

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

private theorem toQuiverPath {N : Type} {G : Graph N} {s x : N}
    (hPath : FiniteCausalPath G.edge x s) : Nonempty (SupplierPath G s x) := by
  induction hPath with
  | same => exact ⟨@Quiver.Path.nil N (supplierQuiver G) _⟩
  | link hy _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨@Quiver.Path.cons N (supplierQuiver G) _ _ _ p ⟨hy⟩⟩

/-- Moving upstream by any one edge shortens a route to the same source
by exactly one edge. A distinct supplier is handled by the immediate join. -/
private theorem shortenPath {N : Type} (G : Graph N) (hFork : ForksJoinInOneStep G)
    {s x : N} (hs : G.Source s) (p : SupplierPath G s x) :
    ∀ y, G.edge y x →
      ∃ q : SupplierPath G s y, q.length + 1 = p.length := by
  classical
  induction p with
  | nil => exact fun y hy => (hs ⟨y, hy⟩).elim
  | @cons a b p hba ih =>
    intro y hy
    by_cases h : y = a
    · subst y
      exact ⟨p, rfl⟩
    · obtain ⟨k, hky, hka⟩ := hFork b y a hy hba.down h
      obtain ⟨q, hq⟩ := ih k hka
      exact ⟨@Quiver.Path.cons N (supplierQuiver G) _ _ _ q ⟨hky⟩, congrArg Nat.succ hq⟩

private theorem accOfPath {N : Type} (G : Graph N) (hFork : ForksJoinInOneStep G)
    {s : N} (hs : G.Source s) (n : Nat) :
    ∀ {x}, (p : SupplierPath G s x) → p.length = n → Acc G.edge x := by
  induction n with
  | zero =>
    intro x p hLen
    cases p with
    | nil => exact ⟨_, fun y hy => (hs ⟨y, hy⟩).elim⟩
    | cons _ _ => exact (Nat.succ_ne_zero _ hLen).elim
  | succ n ih =>
    intro x p hLen
    refine ⟨_, fun y hy => ?_⟩
    obtain ⟨q, hq⟩ := shortenPath G hFork hs p y hy
    exact ih q (Nat.succ.inj (hq.trans hLen))

/-- Any finite path ending upstream at a source entails accessibility
at the starting node when all immediate forks in the graph satisfy the rule. -/
theorem accessibleOfSourcePath {N : Type} (G : Graph N) (x : N)
    (hPath : SourcePath G x) (hFork : ForksJoinInOneStep G) : Acc G.edge x := by
  obtain ⟨s, hPath, hs⟩ := hPath
  obtain ⟨p⟩ := toQuiverPath hPath
  exact accOfPath G hFork hs p.length p rfl

/-- Any two finite upstream paths to sources from the same starting bearer
have the same endpoint and the same length. -/
theorem maximalPathsAgree {N : Type} (G : Graph N) (hFork : ForksJoinInOneStep G)
    {s t x : N} (hs : G.Source s) (ht : G.Source t)
    (p : SupplierPath G s x)
    (q : SupplierPath G t x) :
    s = t ∧ p.length = q.length := by
  induction q with
  | nil =>
    cases p with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ h => exact (ht ⟨_, h.down⟩).elim
  | cons q h ih =>
    obtain ⟨p', hp'⟩ := shortenPath G hFork hs p _ h.down
    obtain ⟨hSource, hLength⟩ := ih p'
    exact ⟨hSource, hp'.symm.trans (congrArg Nat.succ hLength)⟩

/-- One rooted path plus the one-step fork rule gives well-foundedness on
the complete selected cone. The source and the forks are of the same graph. -/
theorem coneWellFounded_of_sourcePath {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (hPath : HasSelectedSourcePath m w x) (hFork : SelectedForksJoinInOneStep m w x) :
    ConeWellFounded m w x.val := by
  have hLocal := accessibleOfSourcePath (coneGraph m w x.val) (selectedNode m w x) hPath hFork
  have hSelected : Acc (ActualConcreteGround m w) x.val :=
    acc_of_subtype
      (fun _ _ hCone hEdge =>
        ⟨⟨⟨hEdge.1, hEdge.2.1⟩, Relation.ReflTransGen.head hEdge hCone.2⟩, hEdge.2.2⟩)
      (selectedNode m w x) hLocal
  have accessibleAncestor (y : B) (hPath : GroundAncestor m w y x.val) :
      Acc (ActualConcreteGround m w) y := by
    induction hPath using Relation.ReflTransGen.head_induction_on with
    | refl => exact hSelected
    | head hEdge _ ih => exact ih.inv hEdge
  exact (coneWellFounded_iff_acc m w x.val).mpr fun y hCone => accessibleAncestor y hCone.2

/-- The necessary ancestor still uses the existing contingent-grounding
and excluded-middle premises at exactly the same world and selected bearer. -/
theorem necessaryRootAncestor_of_sourcePath {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (hPath : HasSelectedSourcePath m w x) (hFork : SelectedForksJoinInOneStep m w x)
    (hDep : ConeContingentGrounded m w x.val) (hEM : ExcludedMiddle) :
    NecessaryRootAncestor m w x.val :=
  SelectedAncestry.necessaryRootAncestor m w x.val x.property
    (coneWellFounded_of_sourcePath m w x hPath hFork) hDep hEM

theorem oneStepForks_of_uniquePredecessor {N : Type} (G : Graph N)
    (hUnique : UniquePredecessor G) : ForksJoinInOneStep G :=
  fun _ _ _ hy hz hne => (hne (hUnique hy hz)).elim

/-- The existing diamond really branches at its tip and satisfies the rule. -/
theorem diamondAllowsBranching : ForksJoinInOneStep diamond ∧ ¬ UniquePredecessor diamond := by
  refine ⟨?_, fun h => DiamondNode.noConfusion
    (h (Or.inr ⟨Or.inl rfl, rfl⟩ : diamond.edge .left .tip)
      (Or.inr ⟨Or.inr rfl, rfl⟩ : diamond.edge .right .tip))⟩
  intro x y z hy hz hne
  cases x <;> cases y <;> cases z <;>
    simp_all [diamond]

/-- The existing common-source ray is acyclic and confluent. Even with the
same finitely reachable source from every node, the selected ray start is inaccessible
and fails the strict one-step rule. -/
theorem commonSourceAllowsRegress :
    (actualGraph overlap ()).NoCycles ∧
      RootedAtUniqueSource (actualGraph overlap ()) ∧
      UpstreamConfluent (actualGraph overlap ()) ∧
      ¬ Acc (actualGraph overlap ()).edge overlapNode ∧
      ¬ ForksJoinInOneStep (actualGraph overlap ()) := by
  let G := actualGraph overlap ()
  let s : Actual overlap () := ⟨none, trivial⟩
  have hs : G.Source s := by
    rintro ⟨y, hy⟩
    rcases y with ⟨(_ | n), _⟩ <;> exact hy
  have allPaths (x : Actual overlap ()) : FiniteCausalPath G.edge x s := by
    rcases x with ⟨(_ | n), _⟩
    · exact .same s
    · exact .link (y := s) trivial (.same s)
  have uniqueSource (t : Actual overlap ()) (ht : G.Source t) : t = s := by
    rcases t with ⟨(_ | n), _⟩
    · rfl
    · exact (ht ⟨s, trivial⟩).elim
  have reach (x : Actual overlap ()) :
      Relation.ReflTransGen (fun x y => G.edge y x) x s := by
    exact (finiteCausalPath_iff_reflTransGen G.edge x s).mp (allPaths x)
  have h := TruthCore.Results.Causality.WorldSourceRegress.overlapControl
  refine ⟨h.1 (), ⟨s, hs, uniqueSource, allPaths⟩, ?_, h.2.2.2.1, ?_⟩
  · exact fun _ y z _ _ => ⟨s, reach y, reach z⟩
  · intro hf
    let y : Actual overlap () := ⟨some 1, trivial⟩
    have distinct : s ≠ y := by
      intro he
      have hval : (none : Option Nat) = some 1 := congrArg Subtype.val he
      cases hval
    obtain ⟨k, hk, _⟩ := hf overlapNode s y trivial rfl distinct
    exact hs ⟨k, hk⟩

end TruthCore.Results.Causality.SelectedSourcePath
