module

public import TruthCore.Causality.AncestorIndividuation

@[expose] public section

namespace TruthCore.Results.Causality.AncestorIndividuation

open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.SourceForest (WellFoundedEdges)
open TruthCore.Causality.AncestorIndividuation

/-- Induct on the two ends separately. If neither precedes the other, the
induction hypotheses put each ancestor of either strictly below the other. -/
theorem comparability {B : Type} (G : Graph B)
    (hEM : ExcludedMiddle) (hWF : WellFoundedEdges G)
    (hIdentity : IdentityByAncestors G) : ComparableByAncestry G := by
  let R := Relation.TransGen G.edge
  have wellFounded : WellFounded R := WellFounded.transGen hWF
  intro x
  refine wellFounded.induction (C := fun a => ∀ b, R a b ∨ a = b ∨ R b a) x ?_
  intro a belowA b
  refine wellFounded.induction (C := fun b => R a b ∨ a = b ∨ R b a) b ?_
  intro b belowB
  rcases hEM (R a b) with forward | noForward
  · exact Or.inl forward
  rcases hEM (R b a) with backward | noBackward
  · exact Or.inr (Or.inr backward)
  apply Or.inr
  apply Or.inl
  apply hIdentity
  intro z
  constructor
  · intro za
    rcases belowA z za b with zb | equal | bz
    · exact zb
    · exact (noBackward (equal ▸ za)).elim
    · exact (noBackward (bz.trans za)).elim
  · intro zb
    rcases belowB z zb with az | equal | za
    · exact (noForward (az.trans zb)).elim
    · exact (noForward (equal ▸ zb)).elim
    · exact za

open TruthCore.Causality.FullFirstCause.Fixture (Object graph)

private theorem originHasNoPredecessor (z : Object) : ¬ graph.edge z .origin := by
  intro h
  rcases h.2 with impossible | impossible <;> contradiction

private theorem ancestorIsOrigin {x y : Object} (h : Relation.TransGen graph.edge x y) :
    x = .origin := by
  induction h with
  | single e => exact e.1
  | tail _ _ ih => exact ih

theorem siblings : SiblingControl := by
  have leftEdge : graph.edge .origin .effect := ⟨rfl, Or.inl rfl⟩
  have rightEdge : graph.edge .origin .other := ⟨rfl, Or.inr rfl⟩
  have originAcc : Acc graph.edge .origin :=
    .intro _ (fun z h => (originHasNoPredecessor z h).elim)
  have wellFounded : WellFoundedEdges graph := by
    constructor
    intro x
    exact .intro x (fun z h => h.1 ▸ originAcc)
  have originSource : graph.Source .origin := by
    rintro ⟨z, h⟩
    exact originHasNoPredecessor z h
  have unique : ∀ s, graph.Source s → s = .origin := by
    intro s hs
    cases s with
    | origin => rfl
    | effect => exact (hs ⟨.origin, leftEdge⟩).elim
    | other => exact (hs ⟨.origin, rightEdge⟩).elim
  have same : ∀ z, Relation.TransGen graph.edge z .effect ↔
      Relation.TransGen graph.edge z .other := by
    intro z
    constructor
    · intro h
      exact ancestorIsOrigin h ▸ Relation.TransGen.single rightEdge
    · intro h
      exact ancestorIsOrigin h ▸ Relation.TransGen.single leftEdge
  refine ⟨wellFounded, originSource, unique, leftEdge, rightEdge, by decide, same, ?_, ?_⟩
  · intro identity
    exact Object.noConfusion (identity .effect .other same)
  · intro comparable
    rcases comparable .effect .other with h | h | h
    · exact Object.noConfusion (ancestorIsOrigin h)
    · exact Object.noConfusion h
    · exact Object.noConfusion (ancestorIsOrigin h)

private theorem sourceHasNoAncestor {B : Type} {G : Graph B} {x z : B}
    (hx : G.Source x) : ¬ Relation.TransGen G.edge z x := by
  intro h
  cases h with
  | single edge => exact hx ⟨_, edge⟩
  | tail _ edge => exact hx ⟨_, edge⟩

theorem atMostOneSource {B : Type} (G : Graph B) (hIdentity : IdentityByAncestors G) :
    TruthCore.Causality.SourceForest.AtMostOneSource G := by
  intro x y hx hy
  apply hIdentity
  intro z
  exact ⟨fun h => (sourceHasNoAncestor hx h).elim, fun h => (sourceHasNoAncestor hy h).elim⟩

end TruthCore.Results.Causality.AncestorIndividuation
