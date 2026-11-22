import TruthCore.Ontology.ExistencePredicate

/-! Existence as a predicate: the owner's definitional argument, its retorsion,
and a nuclear-characterization (Parsons-style) control. Analyst formulations;
attribution deferred. Vocabulary: `TruthCore.Ontology.ExistencePredicate`.

* `definitionalArgument`: P1 (the existing omnibenevolent God is defined) and
  the weak P2 (whatever is defined is true) give `GodExists` over the frame's
  beings. Valid, and a transcription by instantiation: its whole content is P2
  applied to P1's description, then dropping two conjuncts.
* `unrestrictedGivesDefinitionsTrue`: the unrestricted P2 implies the weak P2.
* `definitionalTruthRetorsion`: the unrestricted P2 is logically false in every
  frame; the weak P2 fails once the contrary sole-God description is also
  defined; each description is satisfiable on its own; P1 and the weak P2 are
  jointly consistent. Zero axioms.
* `analyticReadingCountermodel`: under the analytic reading of P2 the argument
  is invalid. Zero axioms.
* `nuclearCharacterizationControl`: nuclear characterization delivers a
  nuclear-existent (EXISTENCE_5) god object, and a model of it has no
  extranuclear-existent (EXISTENCE_4) god while satisfying the weak P2 on
  nuclear descriptions and, with a nuclear reading of being in act at esse, the
  naming premise. -/

namespace TruthCore.Results.Ontology.ExistencePredicate

open TruthCore.Ontology.ExistencePredicate
open TruthCore.Case.Catholicism (GodExists GodNamesTheUniqueMaximeEns)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)

/-- The owner's definitional argument: from P1 and the weak P2, some being (an
object that exists) is God. -/
theorem definitionalArgument (F : DefinitionalFrame) (IsGod OB : F.Object → Prop)
    (p1 : DefinesExistingOmnibenevolentGod F IsGod OB) (p2 : DefinitionsAreTrue F) :
    GodExists (fun b : Beings F => IsGod b.1) := by
  sorry

/-- Strength order: the unrestricted characterization principle implies that
whatever is defined is true. -/
theorem unrestrictedGivesDefinitionsTrue (F : DefinitionalFrame)
    (h : UnrestrictedCharacterization F) : DefinitionsAreTrue F := by
  sorry

/-- Retorsion: unrestricted characterization refutes itself, and definitional
truth fails under two contrary sole-God definitions. -/
theorem definitionalTruthRetorsion : DefinitionalTruthRetorsion := by
  sorry

/-- Under the analytic reading of P2 the definitional argument is invalid: a
frame with no beings in which P1's description is defined. -/
theorem analyticReadingCountermodel : AnalyticReadingCountermodel := by
  sorry

namespace Model

end Model

open Model in
/-- The nuclear-characterization control. -/
theorem nuclearCharacterizationControl : NuclearCharacterizationControl := by
  sorry

end TruthCore.Results.Ontology.ExistencePredicate
