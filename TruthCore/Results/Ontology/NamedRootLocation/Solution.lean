module

public import TruthCore.Ontology.NamedRootLocation
public import TruthCore.Ontology.NaturalismConsequences

public import TruthCore.Results.Ontology.Naturalism.N1EntailsN2.Solution

@[expose] public section
namespace TruthCore.Results.Ontology.NamedRootLocation

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryClassicalGodRoot (NecessaryClassicalGodRootAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.SameSourceWitness (ClassicalGodRootWitnessAt classicalGodRoot_iff)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Ontology.NamedRootLocation
open TruthCore.Ontology.Naturalism (concreteNaturalism_excludes)
open TruthCore.Results.Ontology.Naturalism.N1EntailsN2 (n1EntailsN2)
open TruthCore.Ontology.NaturalismConsequences
  (ConcreteNaturalismFails ExistenceNaturalismFails)
open TruthCore.Ontology.SpacetimeGroundingBridge
open TruthCore.Ontology.Spatiotemporal (Frame Located)

/-- Pointwise nonoccupation needs the selected-world root and necessary
existence of that same candidate. -/
theorem actualRootUnlocated {W B : Type} (m : Profile W B) (w : W) (F : Frame B) (x : B)
    (hRoot : ActualRoot m w x) (hNecessary : NecessaryAt m.ontic w x)
    (hWhole : ActualConcreteWholeAt m w F) (hCont : ContingentWholeAt m w F)
    (hDep : OccupantsDependOnWholeAt m w F) : ¬ Located F x := by
  have hDistinct : x ≠ F.whole := by
    intro hEq
    rcases hCont.2 with ⟨v, hv, hAbsent⟩
    exact hAbsent (hEq ▸ hNecessary v hv)
  intro hLocated
  exact hRoot.2 F.whole ⟨hWhole.1, hWhole.2, hDep x hDistinct hRoot.1 hLocated⟩

/-- Preserve the named classical witness, including its full attribute body,
and add nonoccupation in the same frame as the spatial premises. -/
theorem derive {W P R : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (F : Frame σ.Being) (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hNamed : NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill)
    (hWhole : ActualConcreteWholeAt m w F) (hCont : ContingentWholeAt m w F)
    (hDep : OccupantsDependOnWholeAt m w F) :
    NecessaryClassicalGodRootUnlocatedAt σ m w F p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  rcases (classicalGodRoot_iff σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
    Composite MatterForm Infinite Eternal HasIntellect HasWill).mp hNamed with ⟨g, hg⟩
  exact ⟨g, hg, actualRootUnlocated m w F g hg.1.1 hg.1.2.1 hWhole hCont hDep⟩

/-- The actual concrete named witness refutes N2 and hence N1 for
dimensive occupation in this frame. -/
theorem occupantNaturalismFails {W P R : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (F : Frame σ.Being) (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hNamed : NecessaryClassicalGodRootUnlocatedAt σ m w F p GoodIn InPotency MoreIn PriorSimply
      ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill) :
    ConcreteNaturalismFails m.ontic m.concrete (Located F) w ∧
    ExistenceNaturalismFails m.ontic (Located F) w := by
  rcases hNamed with ⟨g, hg, hUnlocated⟩
  have hActual := hg.1.1.1
  have hN2 : ConcreteNaturalismFails m.ontic m.concrete (Located F) w :=
    fun h => concreteNaturalism_excludes h ⟨g, hActual.2, hActual.1, hUnlocated⟩
  exact ⟨hN2, fun h => hN2 (n1EntailsN2 m.ontic m.concrete (Located F) w h)⟩

open TruthCore.Case.Catholicism
open TruthCore.Causality.NecessaryClassicalGodRootControl
open TruthCore.Causality.RootPositiveIntellectWillControl
  (profile prior component composite matterForm intellect will)
open Separation

private theorem sourceWitness :
    ClassicalGodRootWitnessAt signature model false profile transferAct potency
      (transferMore true) prior component composite matterForm infinite eternal intellect will
      .source := by
  have hRoot : ActualRoot model false .source := by
    refine ⟨⟨trivial, Or.inl rfl⟩, ?_⟩
    intro y h
    rcases h.2.2 with ⟨_, hn⟩ | ⟨_, hn⟩
    · exact hn rfl
    · cases hn
  have hUnique : ∀ x, ActualRoot model false x → x = .source := by
    intro x hx
    by_cases h : x = .source
    · exact h
    · exact (hx.2 .source ⟨trivial, Or.inl rfl, Or.inl ⟨rfl, h⟩⟩).elim
  have hNecessary : NecessaryAt model.ontic false .source := fun _ _ => Or.inr (by decide)
  have hMax : IsMaximumIn profile.InAct (transferMore true) profile.esse .source := by
    refine ⟨trivial, ?_⟩
    intro y
    change ¬ transferMore true false y .source
    unfold transferMore transferRank
    cases y <;> decide
  have hPerfect : IsPerfect profile.InAct .source := fun _ _ _ => trivial
  have hFirst : IsFirstBeing prior .source := by
    intro y h
    rcases h with ⟨hy, _⟩ | ⟨_, hn⟩
    · exact hy
    · cases hn
  have hSimple : IsSimple composite .source := fun h => TransferRole.noConfusion h
  have hNine : attributes .source := by
    refine ⟨hSimple, hPerfect, ⟨trivial, ?_⟩, fun _ h => h, rfl, fun _ h => h, trivial,
      Or.inl rfl, Or.inl rfl⟩
    intro x r hx _
    cases r <;> exact Or.inl ⟨rfl, hx⟩
  exact ⟨⟨hRoot, hNecessary, hUnique, hMax, hPerfect⟩, rfl, hFirst, fun h => TransferRole.noConfusion h,
    fun _ h => TransferRole.noConfusion h.1, rfl, hNine, hNine⟩

theorem separation : Separation.Control := by
  have hNamed := sourceWitness
  have hWhole : ActualConcreteWholeAt model false frame := ⟨trivial, Or.inl rfl⟩
  have hCont : ContingentWholeAt model false frame := by
    refine ⟨hWhole.2, true, trivial, ?_⟩
    rintro (h | h)
    · cases h
    · exact h rfl
  have hDep : OccupantsDependOnWholeAt model false frame := by
    intro x hDistinct _ hLocated
    rcases hLocated with ⟨_, h | h⟩
    · exact (hDistinct h).elim
    · subst x
      exact Or.inr ⟨rfl, rfl⟩
  have hGround : model.grounds true .recipient .source := ⟨rfl, rfl⟩
  refine ⟨⟨.source, hNamed⟩, hWhole, hCont, hDep, by decide, ⟨trivial, Or.inl rfl⟩,
    ⟨(), Or.inr rfl⟩, Or.inr ⟨rfl, rfl⟩, hNamed,
    actualRootUnlocated model false frame .source hNamed.1.1 hNamed.1.2.1 hWhole hCont hDep,
    trivial, by decide, ⟨trivial, Or.inr (by decide)⟩, Or.inr (by decide), hGround, ?_⟩
  exact fun h => h.2.2.2 true .recipient trivial (Or.inr (by decide)) hGround

end TruthCore.Results.Ontology.NamedRootLocation
