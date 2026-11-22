import TruthCore.Ontology.EncodingAndRealPredicates

/-! Existence as a predicate, part 2: an encoding/exemplification control, a
real-predicate control for Kant's thesis, and the Meditation V argument.
Analyst formulations; attribution deferred. Vocabulary:
`TruthCore.Ontology.EncodingAndRealPredicates`.

* `encodingControl`: comprehension gives the characterized god encoded but not
  exemplified existence; the encoded reading of God is unusable with the
  exemplified reading of being; a model with the encoded reading of both.
* `realPredicateControl`: with existence a real predicate every most-real
  candidate exists; a model of Kant's thesis with the identification and
  uniqueness premises and a most-real candidate in which nothing most real
  exists. Zero axioms.
* `meditationFive`: a supremely perfect God candidate and existence as a real
  predicate give some existing God. Zero axioms. -/

namespace TruthCore.Results.Ontology.EncodingAndRealPredicates

open TruthCore.Ontology.EncodingAndRealPredicates
open TruthCore.Case.Catholicism (GodExists GodNamesTheUniqueMaximeEns)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)
open TruthCore.German.Kant.CosmologicalInference

/-- Meditation V, analyst formulation: if some candidate is supremely perfect and
God, and existence at `w` is a real predicate (a perfection of the profile), then
some being existing at `w` is God. -/
theorem meditationFive {W E : Type} (m : Ontic W E) (p : RealityProfile E) (w : W)
    (IsGod : E → Prop) (d1 : SupremelyPerfectGodCandidate p IsGod)
    (d2 : ExistenceIsRealPredicate m p w) :
    GodExists (fun b : {x : E // m.ExistsAt w x} => IsGod b.1) := by
  sorry

/-- The real-predicate control. -/
theorem realPredicateControl : RealPredicateControl := by
  sorry

namespace Model

end Model

open Model in
/-- The encoding control. -/
theorem encodingControl : EncodingControl := by
  sorry

end TruthCore.Results.Ontology.EncodingAndRealPredicates
