module

public import TruthCore.Results.Causality.SelectedPlgTheory.Solution
public import TruthCore.Results.Causality.DependenceStrictGroundMap.Solution
public import TruthCore.Explanation.EssenceReasonSeparation

@[expose] public section

namespace TruthCore.Models.SelectedPlgNegations

open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.SelectedPlgTheory
open TruthCore.Results.Causality.SelectedPlgTheory
open Relation Sequent

/-- A total labelling transfers any bearer witness to the selected atom type. -/
theorem populatedAtBearer {B Atom : Type} (label : B → Atom) (x : B) :
    PopulatedAtomType Atom := ⟨label x⟩

/-- The unpopulated case satisfies the path and return conditions vacuously.
Even the empty theory then lacks the underivable sequent required by PLG consistency. -/
theorem emptyPresentation (S : Set (Sequent Empty)) (D : Empty → Empty → Prop) :
    ¬ PopulatedAtomType Empty ∧ NoStrictReturn S ∧
    DependenceHasStrictPaths D id S ∧ ¬ Consistent S := by
  refine ⟨fun ⟨a⟩ => a.elim, fun a => a.elim, fun a => a.elim, ?_⟩
  intro ⟨s, _⟩
  cases s with
  | weakFull _ a | strictFull _ a | weakPartial _ a | strictPartial _ a => exact a.elim

/-- With consistency, a failed alignment names a particular uncovered dependence edge. -/
theorem missingMapIffUncovered {B Atom : Type} (D : B → B → Prop) (label : B → Atom)
    (S : Set (Sequent Atom)) (hc : Consistent S) :
    ¬ DependenceMapsToStrictExistenceGround D label S ↔
      ∃ x y, x ≠ y ∧ D x y ∧ ¬ StrictPath S (label y) (label x) := by
  classical
  unfold DependenceMapsToStrictExistenceGround
  simp only [not_forall, exists_prop, strictDerivabilityCriterion S hc]

/-- One initial self-step at the supplier, with no initial step into the recipient. -/
def supplierLoop : Set (Sequent Bool) := {strictPartial false false}

/-- Explosion supplies the map even for a distinct edge with no supporting path. -/
theorem loopMasksMissingPath :
    ¬ NoStrictReturn supplierLoop ∧ ¬ Consistent supplierLoop ∧
    DependenceMapsToStrictExistenceGround Control.dependence id supplierLoop ∧
    ¬ DependenceHasStrictPaths Control.dependence id supplierLoop := by
  have self : StrictEdge supplierLoop false false := Or.inl rfl
  have fails : ¬ NoStrictReturn supplierLoop := fun h => h false false self .refl
  refine ⟨fails, fun hc => fails ((consistencyCriterion supplierLoop).mp hc), ?_, ?_⟩
  · intro _ _ _ _
    exact Derivable.nonCircularity _ (Derivable.assumption (S := supplierLoop)
      (show strictPartial false false ∈ supplierLoop from rfl))
  · intro paths
    obtain ⟨u, v, _, step, after⟩ := paths true false (by decide) ⟨rfl, rfl⟩
    have endsFalse {a b : Bool} (h : WeakEdge supplierLoop a b) : b = false := by
      simp [WeakEdge, StrictEdge, supplierLoop] at h
      exact h.2
    have staysFalse {a b : Bool} (h : ReflTransGen (WeakEdge supplierLoop) a b) :
        a = false → b = false := by
      induction h with
      | refl => exact id
      | tail _ edge _ => exact fun _ => endsFalse edge
    exact Bool.noConfusion (staysFalse after (endsFalse (Or.inr (Or.inr step))))

open TruthCore.Explanation.EssenceReasonSeparation

/-- Changing either the labels or the consistent PLG presentation cannot recover a
universal strict map for this modal relation on the two necessarily coexisting bearers. -/
theorem modalControlExcludesMap {Atom : Type} (label : Bool → Atom) (S : Set (Sequent Atom))
    (hc : Consistent S) :
    ¬ DependenceMapsToStrictExistenceGround (ModalRequiresExistence directedNature false) label S := by
  intro mapped
  have nonmutual := TruthCore.Results.Causality.DependenceStrictGroundMap.nonmutualDependenceFromStrictGround
    _ label S hc mapped
  exact nonmutual true false (by decide) (fun _ _ _ => True.intro) (fun _ _ _ => True.intro)

end TruthCore.Models.SelectedPlgNegations
