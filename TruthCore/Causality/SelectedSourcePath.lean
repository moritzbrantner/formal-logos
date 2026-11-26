module

public import TruthCore.Causality.LocalSourceConfluence
public import TruthCore.Causality.SelectedAncestry
public import Mathlib.Combinatorics.Quiver.Path

@[expose] public section

namespace TruthCore.Causality.SelectedSourcePath
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedAncestry (Cone)
open TruthCore.Causality.WorldSourceRegress (SourcePath)
open TruthCore.Logic.Regress (Graph)

variable {W B N : Type}

/-- Two distinct immediate suppliers share a supplier that is immediate for both.
The common supplier may depend on the fork. -/
def ForksJoinInOneStep (G : Graph N) : Prop :=
  ∀ x y z, G.edge y x → G.edge z x → y ≠ z → ∃ k, G.edge k y ∧ G.edge k z

/-- Use all actual concrete ancestors of the selected bearer, with unchanged
one-step grounds at the selected world as edges. -/
def coneGraph (m : Profile W B) (w : W) (selected : B) :
    Graph {b // Cone m w selected b} :=
  ⟨fun y x => m.grounds w y.val x.val⟩

def selectedNode (m : Profile W B) (w : W) (x : {b // ActualConcrete m w b}) :
    {b // Cone m w x.val b} :=
  ⟨x.val, x.property, .refl⟩

/-- A single finite path in the cone to a bearer with no immediate supplier
there. Actual concrete suppliers of cone members are themselves in the cone. -/
def HasSelectedSourcePath (m : Profile W B) (w : W) (x : {b // ActualConcrete m w b}) :
    Prop :=
  SourcePath (coneGraph m w x.val) (selectedNode m w x)

/-- The immediate fork rule evaluated only on the complete selected cone. -/
def SelectedForksJoinInOneStep (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) : Prop :=
  ForksJoinInOneStep (coneGraph m w x.val)

/-- Regard grounds as quiver arrows from supplier to dependent so that
the last arrow of a Mathlib path is the first upstream step. -/
@[instance_reducible]
def supplierQuiver (G : Graph N) : Quiver.{0} N where
  Hom y x := PLift (G.edge y x)

abbrev SupplierPath (G : Graph N) (s x : N) :=
  @Quiver.Path N (supplierQuiver G) s x

abbrev SupplierPath.length {G : Graph N} {s x : N} (p : SupplierPath G s x) : Nat :=
  @Quiver.Path.length N (supplierQuiver G) s x p

/-- A two-edge-deep cone with one middle supplier for every natural number. -/
inductive WideConeNode
  | root
  | middle (n : Nat)
  | tip

inductive WideConeGround : WideConeNode → WideConeNode → Prop
  | toMiddle (n : Nat) : WideConeGround .root (.middle n)
  | toTip (n : Nat) : WideConeGround (.middle n) .tip

def wideConeProfile : Profile Unit WideConeNode where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ => WideConeGround

def wideConeTip : {b // ActualConcrete wideConeProfile () b} :=
  ⟨.tip, trivial, trivial⟩

end TruthCore.Causality.SelectedSourcePath
