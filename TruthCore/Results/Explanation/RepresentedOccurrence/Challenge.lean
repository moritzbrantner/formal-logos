import TruthCore.Logic.AssertionRetorsion
import TruthCore.Logic.CogitoEsse
import TruthCore.Explanation.WellFoundedSource

namespace TruthCore.Results.Explanation.RepresentedOccurrence

open TruthCore.Explanation.ExistencePSR (Model)
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)
open TruthCore.Logic.AssertionRetorsion
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Ontology.ConcreteAbstract (HasEsseInRe)

/-- Both predicates quantify over exactly the same extension. -/
theorem population {W B : Type} (m : Model W B) (w : W)
    (h : SomeExistent (m.ontic.ExistsAt w)) : PopulatedAt m w := by
  sorry

/-- Exhibit the provenance forgotten by the two existential population statements. -/
theorem assertionWitness {W B A C E : Type} (m : Model W B) (w : W)
    (Asserts : A → C → Prop) (claim : C) (Occurs : E → Prop)
    (Realizes : A → C → E → Prop) (represent : E → B)
    (hMade : AssertionMade Asserts claim)
    (hRealizes : AssertionRealized Asserts claim Occurs Realizes)
    (hRep : OccurringThoughtIsRepresentedAsExisting Occurs (m.ontic.ExistsAt w) represent) :
    ∃ a e, Asserts a claim ∧ Occurs e ∧ Realizes a claim e ∧ m.ontic.ExistsAt w (represent e) := by
  sorry

/-- At the same world the adopted in-re contract classifies the population witness. -/
theorem concretePopulation {W B R : Type} (m : Model W B) (w : W)
    (InAct : B → R → Prop) (esse : R)
    (hPop : PopulatedAt m w) (hAct : ExistingInActAt m.ontic InAct esse w) :
    InhabitedConcreteAt m.ontic (HasEsseInRe InAct esse) w := by
  sorry

/-- The asserted denial is true in this interpretation: the sole existent lacks
the esse classification. The other candidate is classified but absent. Changing
the world also loses population, while keeping the very same representation. -/
theorem denialControl :
    ∃ (m : Model Bool Bool) (InAct : Bool → Unit → Prop)
      (Asserts : Unit → Prop → Prop) (Occurs : Unit → Prop)
      (Realizes : Unit → Prop → Unit → Prop) (represent : Unit → Bool),
      (fun denial => AssertionMade Asserts denial ∧ AssertionRealized Asserts denial Occurs Realizes ∧
        OccurringThoughtIsRepresentedAsExisting Occurs (m.ontic.ExistsAt false) represent ∧
        PopulatedAt m false ∧ denial ∧ ¬ ExistingInActAt m.ontic InAct () false ∧
        ¬ PopulatedAt m true) (¬ InhabitedConcreteAt m.ontic (HasEsseInRe InAct ()) false) := by
  sorry

end TruthCore.Results.Explanation.RepresentedOccurrence
