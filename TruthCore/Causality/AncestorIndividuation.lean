module

public import TruthCore.Causality.FullFirstCause
public import TruthCore.Causality.SourceForest

/-! At one selected population, an edge points from giver to recipient.
An ancestor reaches its target by a nonempty finite path. This excludes the
empty path, but a cycle can take an object back to itself. Well-foundedness
excludes such cycles in the comparison theorem. The interpretation
of these paths as all existential ancestry is an open application premise.
Individuation by all ancestors is stronger than requiring an origin for an
individual or restricting a criterion of identity to underived beings. -/

@[expose] public section

namespace TruthCore.Causality.AncestorIndividuation

open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.SourceForest (WellFoundedEdges)

def IdentityByAncestors {B : Type} (G : Graph B) : Prop :=
  ∀ x y, (∀ z, Relation.TransGen G.edge z x ↔ Relation.TransGen G.edge z y) → x = y

def ComparableByAncestry {B : Type} (G : Graph B) : Prop :=
  ∀ x y, Relation.TransGen G.edge x y ∨ x = y ∨ Relation.TransGen G.edge y x

/-- The graph and its three separate objects are the existing production
fixture. This tests the structure without assuming its edges give real esse. -/
def SiblingControl : Prop :=
  let G := FullFirstCause.Fixture.graph
  let source := FullFirstCause.Fixture.Object.origin
  let left := FullFirstCause.Fixture.Object.effect
  let right := FullFirstCause.Fixture.Object.other
  WellFoundedEdges G ∧ G.Source source ∧ (∀ s, G.Source s → s = source) ∧
    G.edge source left ∧ G.edge source right ∧ left ≠ right ∧
    (∀ z, Relation.TransGen G.edge z left ↔ Relation.TransGen G.edge z right) ∧
    ¬ IdentityByAncestors G ∧ ¬ ComparableByAncestry G

end TruthCore.Causality.AncestorIndividuation
