module

public import TruthCore.Causality.SourceForest
public import TruthCore.Causality.ConcreteExistentialSupply
public import TruthCore.Causality.RootPositiveIntellectWill

@[expose] public section

namespace TruthCore.Causality.LocalSourceConfluence
open TruthCore.Causality.SourceForest
open TruthCore.Logic.Regress

/-- From two immediate suppliers of the same dependent, finite upstream
paths (possibly empty) reach one and the same node of the same relation. -/
def LocalForksJoin {N : Type} (G : Graph N) : Prop :=
  ∀ x y z, G.edge y x → G.edge z x →
    Relation.Join (Relation.ReflTransGen (fun a b => G.edge b a)) y z

/-- The relay at each stage also receives from one of two alternating sources. -/
inductive LadderNode
  | stage (n : Nat)
  | root (side : Bool)
  deriving DecidableEq

def side : Nat → Bool
  | 0 => false
  | n + 1 => !(side n)

inductive Feeds : LadderNode → LadderNode → Prop
  | relay (n : Nat) : Feeds (.stage (n + 1)) (.stage n)
  | origin (n : Nat) : Feeds (.root (side n)) (.stage n)

def ladder : Graph LadderNode := ⟨Feeds⟩

/-- Every stage has an immediate source even though its relay ancestry
continues without end. The two named sources are distinct. -/
def LadderControl : Prop :=
  WeaklyConnected ladder ∧ ladder.NoCycles ∧ LocalForksJoin ladder ∧
    (∀ x, ∃ s, ladder.Source s ∧ (x = s ∨ ladder.edge s x)) ∧
    ladder.Source (.root false) ∧ ladder.Source (.root true) ∧
    LadderNode.root false ≠ .root true ∧
    ¬ UpstreamConfluent ladder ∧ ¬ WellFoundedEdges ladder

end TruthCore.Causality.LocalSourceConfluence
