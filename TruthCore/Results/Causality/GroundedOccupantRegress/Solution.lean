module

public import TruthCore.Causality.GroundedOccupantRegress
public import TruthCore.Results.Causality.WorldSourceRegress.Solution

@[expose] public section

namespace TruthCore.Results.Causality.GroundedOccupantRegress
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Ontology.Naturalism (ConcreteNaturalism)
open TruthCore.Ontology.NaturalismConsequences (ConcreteNaturalismFails)
open TruthCore.Ontology.Spatiotemporal (Frame Located)

theorem unlocatedRootOrRegress {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x})
    (hAcyclic : ActualConcreteGroundingAcyclicAt m w)
    (hCoverage : LocatedActualConcreteGroundedAt m w F) :
    UnlocatedRootOrRegress m w F x := by
  rcases TruthCore.Results.Causality.WorldSourceRegress.source_or_regress
      (graph m w) hAcyclic x with ⟨s, hPath, hSource⟩ | hRegress
  · have hRoot : ActualRoot m w s.val :=
      ⟨s.property, fun y hy => hSource ⟨⟨y, hy.1, hy.2.1⟩, hy.2.2⟩⟩
    have hUnlocated : ¬ Located F s.val := by
      intro hLocated
      obtain ⟨y, hy⟩ := hCoverage s.val s.property hLocated
      exact hRoot.2 y hy
    exact Or.inl ⟨s, hPath, hRoot, hUnlocated⟩
  · exact Or.inr hRegress

theorem unlocatedRoot_of_noRegress {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x})
    (hFork : UnlocatedRootOrRegress m w F x)
    (hNoRegress : NoAnchoredConcreteGroundingRegress m w x) :
    UnlocatedRootPath m w F x :=
  hFork.resolve_right hNoRegress

theorem concreteNaturalismFails_of_unlocatedRoot {W B : Type} (m : Profile W B)
    (w : W) (F : Frame B) (x : {x // ActualConcrete m w x})
    (hRoot : UnlocatedRootPath m w F x) :
    ConcreteNaturalismFails m.ontic m.concrete (Located F) w := by
  intro hN2
  obtain ⟨s, _, _, hUnlocated⟩ := hRoot
  exact hUnlocated (hN2 s.val s.property.2 s.property.1)

theorem anchoredRegress_of_naturalism {W B : Type} (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x})
    (hFork : UnlocatedRootOrRegress m w F x)
    (hN2 : ConcreteNaturalism m.ontic m.concrete (Located F) w) :
    AnchoredConcreteGroundingRegress m w x :=
  hFork.resolve_left fun hRoot => concreteNaturalismFails_of_unlocatedRoot m w F x hRoot hN2

theorem successorControl : SuccessorControl := by
  refine ⟨fun _ _ _ => ⟨(), trivial⟩,
    fun x _ _ => ⟨x + 1, trivial, trivial, rfl⟩, ?_, ?_⟩
  · intro x hLoop
    exact TruthCore.Causality.FiniteRestriction.reverseSuccessorNoLoops x.val
      (Relation.TransGen.lift Subtype.val (fun _ _ hEdge => hEdge) x x hLoop)
  · refine ⟨fun n => ⟨n, trivial, trivial⟩, rfl, ?_, fun _ => rfl⟩
    intro i j hEq
    exact congrArg Subtype.val hEq

theorem fundamentalFieldControl : FundamentalFieldControl := by
  let m := TruthCore.Causality.NecessaryConcreteUnderived.witnessProfile
  have hRoot : ActualRoot m false false :=
    ⟨⟨trivial, Or.inl rfl⟩, fun y hy => Bool.noConfusion hy.2.2.2.1⟩
  have hAcyclic : ActualConcreteGroundingAcyclicAt m false := by
    have hEndpoints {y x : {b // ActualConcrete m false b}}
        (hp : Relation.TransGen (graph m false).edge y x) :
        y.val = false ∧ x.val = true := by
      induction hp with
      | single hEdge => exact ⟨hEdge.1, hEdge.2.1⟩
      | tail _ hEdge ih => exact ⟨ih.1, hEdge.2.1⟩
    intro x hLoop
    obtain ⟨hFalse, hTrue⟩ := hEndpoints hLoop
    exact Bool.noConfusion (hFalse.symm.trans hTrue)
  refine ⟨fun _ _ _ => ⟨(), trivial⟩, hAcyclic, ⟨trivial, Or.inl rfl, rfl, rfl, rfl⟩,
    hRoot, ?_, ?_⟩
  · rintro ⟨f, _, _, hStep⟩
    have hFalse : (f 1).val = false := (hStep 0).1
    have hTrue : (f 1).val = true := (hStep 1).2.1
    exact Bool.noConfusion (hFalse.symm.trans hTrue)
  · intro hCoverage
    obtain ⟨y, hy⟩ := hCoverage false hRoot.1 ⟨(), trivial⟩
    exact hRoot.2 y hy

end TruthCore.Results.Causality.GroundedOccupantRegress
