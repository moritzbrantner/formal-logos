module

public import TruthCore.Causality.GroundedOccupantRegress
public import TruthCore.Results.Causality.SelectedAncestry.Solution
public import TruthCore.Results.Causality.WorldSourceRegress.Solution

@[expose] public section

namespace TruthCore.Results.Causality.SelectedConeRegress
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor cycleProfile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.SelectedAncestry
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.RootDescent (acc_of_map acc_of_subtype)

/-- Acyclicity makes any descending chain from this actual recipient
injective. Without such a chain the recipient is accessible, as is every
actual concrete member of its complete upstream cone. -/
theorem coneWellFounded_of_noAnchoredRegress {W B : Type} (m : Profile W B) (w : W)
    (x : {x // ActualConcrete m w x})
    (hAcyclic : ActualConcreteGroundingAcyclicAt m w)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x) :
    ConeWellFounded m w x.val := by
  have hAcc : Acc (graph m w).edge x := by
    classical
    by_contra hNotAcc
    obtain ⟨f, hStart, hStep⟩ := not_acc_iff_exists_descending_chain.mp hNotAcc
    exact hNoRegress ⟨f, hStart, WorldSourceRegress.chain_injective (graph m w) hAcyclic f hStep,
      hStep⟩
  have hSelected : Acc (ActualConcreteGround m w) x.val :=
    acc_of_subtype (fun _ _ _ hEdge => ⟨⟨hEdge.1, hEdge.2.1⟩, hEdge.2.2⟩) x hAcc
  have accessibleAncestor (y : B) (hPath : GroundAncestor m w y x.val) :
      Acc (ActualConcreteGround m w) y := by
    induction hPath using Relation.ReflTransGen.head_induction_on with
    | refl => exact hSelected
    | head hEdge _ ih => exact ih.inv hEdge
  exact (coneWellFounded_iff_acc m w x.val).mpr fun y hCone => accessibleAncestor y hCone.2

/-- Complete cone well-foundedness excludes an anchored regress at its
selected recipient without requiring acyclicity elsewhere. -/
theorem noAnchoredRegress_of_coneWellFounded {W B : Type} (m : Profile W B) (w : W)
    (x : {x // ActualConcrete m w x})
    (hWF : ConeWellFounded m w x.val) :
    NoAnchoredConcreteGroundingRegress m w x := by
  rintro ⟨f, hStart, _, hStep⟩
  have hAcc : Acc (graph m w).edge x :=
    acc_of_map Subtype.val (fun y _ hEdge => ⟨y.property.1, y.property.2, hEdge⟩)
      (accessibleOfConeWellFounded m w x.val x.property hWF)
  exact not_acc_iff_exists_descending_chain.mpr ⟨f, hStart, hStep⟩ hAcc

/-- Compose the new supply of cone well-foundedness with the existing
necessary-root result, retaining the original contingent-grounding and
excluded-middle inputs at the same selected world and bearer. -/
theorem necessaryRootAncestor_of_noAnchoredRegress {W B : Type}
    (m : Profile W B) (w : W) (x : {x // ActualConcrete m w x})
    (hAcyclic : ActualConcreteGroundingAcyclicAt m w)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x)
    (hDep : ConeContingentGrounded m w x.val)
    (hEM : ExcludedMiddle) :
    NecessaryRootAncestor m w x.val :=
  SelectedAncestry.necessaryRootAncestor m w x.val x.property
    (coneWellFounded_of_noAnchoredRegress m w x hAcyclic hNoRegress) hDep hEM

/-- The existing two-cycle has a repeating descending chain, hence no
well-founded cone at its selected recipient, but no injective infinite
chain can fit in the two-node graph. -/
theorem cyclicControl :
    NoAnchoredConcreteGroundingRegress cycleProfile true ⟨true, trivial, rfl⟩ ∧
      ¬ ConeWellFounded cycleProfile true true := by
  constructor
  · rintro ⟨f, _, hInj, _⟩
    exact not_injective_infinite_finite f hInj
  · intro hWF
    have hAcc := accessibleOfConeWellFounded cycleProfile true true ⟨trivial, rfl⟩ hWF
    let f : Nat → Bool := Nat.rec true (fun _ b => !b)
    have hStep (n : Nat) : ActualConcreteGround cycleProfile true (f (n + 1)) (f n) := by
      refine ⟨trivial, rfl, ?_⟩
      change (!f n) ≠ f n
      cases f n <;> decide
    exact not_acc_iff_exists_descending_chain.mpr ⟨f, rfl, hStep⟩ hAcc

end TruthCore.Results.Causality.SelectedConeRegress
