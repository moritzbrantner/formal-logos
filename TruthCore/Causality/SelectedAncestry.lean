module

public import TruthCore.Causality.NecessaryRootFork

/-! One selected existent's COMPLETE actual grounding ancestry (#311/#613).
Reuse ActualConcreteGround and Mathlib ReflTransGen. No observed prefix, new
ontology or thought occurrence is substituted for this cone. All application
hypotheses remain explicit and source-free. -/

@[expose] public section

namespace TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.RootDescent (acc_exists_unmarked acc_of_subtype acc_of_map)

variable {W B : Type}

/-- Every actual concrete finite ground-ancestor, including the selected being.
The reflexive endpoint is required actual/concrete explicitly. -/
def Cone (m : Profile W B) (w : W) (selected : B) (x : B) : Prop :=
  ActualConcrete m w x ∧ GroundAncestor m w x selected

/-- Well-foundedness only on the complete cone; unrelated grounding can regress. -/
def ConeWellFounded (m : Profile W B) (w : W) (selected : B) : Prop :=
  WellFounded fun a b : {x // Cone m w selected x} => m.grounds w a.val b.val

/-- Contingent dependence only for actual concrete members of this full cone. -/
def ConeContingentGrounded (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∀ x, Cone m w selected x → ContingentAt m.ontic w x →
    ∃ y, ActualConcreteGround m w y x

/-- The existing GLOBAL actual-grounding premises imply both cone-local ones.
This compares scopes only; it does not establish any instance of either pair. -/
def ScopeComparison : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W) (selected : B),
    (ActualGroundingWF m w → ConeWellFounded m w selected) ∧
    (EveryContingentGroundedAt m w → ConeContingentGrounded m w selected)

/-- One actual concrete necessary ancestor, with no incoming actual concrete
ground at the selected world. It may have non-concrete/unmodelled explanation
or incoming grounds elsewhere; neither uniqueness nor God is asserted. -/
def NecessaryRootAncestor (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∃ x, Cone m w selected x ∧ NecessaryAt m.ontic w x ∧
    ∀ y, ¬ ActualConcreteGround m w y x

/-- The alternative actual contingent root has the same ancestry/minimality. -/
def ContingentRootAncestor (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∃ x, Cone m w selected x ∧ ContingentAt m.ontic w x ∧
    ∀ y, ¬ ActualConcreteGround m w y x

/-- Shared descent extracted from the existing thinker-local proof. This is
not an extra foundation assumption: accessibility and actual population are
explicit inputs. Both horns retain selected-world rootness. -/
theorem rootForkOfAccessibility (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hAcc : Acc (ActualConcreteGround m w) selected) (hEM : ExcludedMiddle) :
    NecessaryRootAncestor m w selected ∨ ContingentRootAncestor m w selected := by
  obtain ⟨x, hCone, hnone⟩ := acc_exists_unmarked (P := Cone m w selected)
    (Mark := fun x => ∃ y, ActualConcreteGround m w y x) (fun _ _ => hEM _)
    (fun _ hCone ⟨y, hy⟩ => ⟨y, hy, ⟨hy.1, hy.2.1⟩, Relation.ReflTransGen.head hy hCone.2⟩)
    hAcc ⟨hActual, Relation.ReflTransGen.refl⟩
  have hRoot : ∀ y, ¬ ActualConcreteGround m w y x := fun y hy => hnone ⟨y, hy⟩
  rcases hEM (ContingentAt m.ontic w x) with hcont | hncont
  · exact Or.inr ⟨x, hCone, hcont, hRoot⟩
  · refine Or.inl ⟨x, hCone, ?_, hRoot⟩
    intro v hv
    rcases hEM (m.ontic.ExistsAt v x) with h | h
    · exact h
    · exact (hncont ⟨hCone.1.2, v, hv, h⟩).elim

/-- `ConeWellFounded` in the generic form of `TruthCore.Logic.RootDescent`:
well-foundedness of the cone restriction is accessibility of every cone member
under `ActualConcreteGround`, since the cone is closed under actual concrete
grounds. A restatement, not a new premise. -/
theorem coneWellFounded_iff_acc (m : Profile W B) (w : W) (selected : B) :
    ConeWellFounded m w selected ↔
      ∀ x, Cone m w selected x → Acc (ActualConcreteGround m w) x :=
  ⟨fun h x hx => acc_of_subtype
      (fun _ _ hCone hEdge => ⟨⟨⟨hEdge.1, hEdge.2.1⟩, Relation.ReflTransGen.head hEdge hCone.2⟩,
        hEdge.2.2⟩) ⟨x, hx⟩ (h.apply _),
    fun h => ⟨fun a => acc_of_map Subtype.val
      (fun y _ hyx => ⟨y.2.1.1, y.2.1.2, hyx⟩) (h a.1 a.2)⟩⟩

/-- Completeness matters: every actual predecessor of a cone member remains
in the cone, so its restricted WF lifts to accessibility of the selected being. -/
theorem accessibleOfConeWellFounded (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected) (hWF : ConeWellFounded m w selected) :
    Acc (ActualConcreteGround m w) selected :=
  (coneWellFounded_iff_acc m w selected).mp hWF selected ⟨hActual, Relation.ReflTransGen.refl⟩

end TruthCore.Causality.SelectedAncestry
