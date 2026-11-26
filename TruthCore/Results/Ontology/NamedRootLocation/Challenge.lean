import TruthCore.Ontology.NamedRootLocation
import TruthCore.Ontology.NaturalismConsequences

namespace TruthCore.Results.Ontology.NamedRootLocation

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryClassicalGodRoot (NecessaryClassicalGodRootAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Ontology.NamedRootLocation
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
  sorry

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
  sorry

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
  sorry

theorem separation : Separation.Control := by
  sorry

end TruthCore.Results.Ontology.NamedRootLocation
