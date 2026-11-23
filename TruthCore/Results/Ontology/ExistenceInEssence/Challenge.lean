import TruthCore.Ontology.ExistenceInEssence

/-! Does existence belong to an essence when essence is identical with esse?
(#1887): the factorization of the unconditional bridge `565ccd6c` into the
act–fact link and exercise in the nature, the Kant-adequacy route to the
"possibly absent" verdict at the foundational case, laws and models.
Analyst formulations; attribution deferred. -/

namespace TruthCore.Results.Ontology.ExistenceInEssence
open TruthCore.Ontology.ExistenceInEssence
open TruthCore.Ontology.ExistenceInEssence.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Modal.ModalGrounding (EssentialTruth EntailsExistence EssenceGroundsNecessity
  EsseEssenceIsEssentialExistence ExistenceConditionalEssences EssentialExclusionAccount
  FoundationalExistenceUnrequiredByOthers FoundationalBeingsContingentAt FoundationalAt)
open TruthCore.Modal.ModalGrounding.Model (frameOn toTrue univ bothHere bothContingent lockedF
  fEssentialExistence noEssence otherRequiresF FoundationalF onlyFHere)
open TruthCore.Causality.FirstMoverNecessity.Model (noCause noPrior receivedNone esseTrue
  essenceByBeing noneHolds xContingent)
open TruthCore.Causality.ContingencyGrounding.Model (heatFail noPower)
open TruthCore.Causality.ContingencyGrounding (PowerOverEsse)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing)
open TruthCore.Latin.Aquinas.InMetaphysicam (IncorruptibleSimply)

/-- Argument 1, the factorization of `565ccd6c`. For `x` with esse equal to
essence, exercise in the nature puts into `x`'s nature the proposition that
its act of being is exercised; the act–fact link makes that proposition the
proposition that `x` exists (pointwise equivalence, hence equality of
world-propositions). -/
theorem exerciseInNatureGivesEssentialExistence {W B T R P : Type}
    (F : CausalityFrame W B T R) (essenceOf esseOf : B → P)
    (Essential : B → (W → Prop) → Prop) (Exercised : W → P → Prop)
    (hLink : EsseExercisedWhereExists F Exercised esseOf)
    (hAN : IdentityPutsExerciseInNature Exercised Essential essenceOf esseOf) :
    EsseEssenceIsEssentialExistence F essenceOf esseOf Essential := by
  sorry

/-- Argument 2, the Kant-adequacy route to "possibly absent". For a
foundational `f`, no essential truth entails its existence: one of `f`'s own
would be contained in the concept (adequacy) and so, by Kant's thesis, not
entail it; no other being's does (unrequired by others). The essentialist
account then makes `f` absent at some accessible world. Constructive; esse =
essence plays no role. -/
theorem kantAdequacyFoundationalContingent {W B T R P : Type}
    (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P) (Received : B → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) (Contains Essential : B → (W → Prop) → Prop)
    (hKT : ExistenceNotConceptual F Contains)
    (hAdeq : ConceptAdequateToEssence Contains Essential)
    (hEPP : EssentialExclusionAccount F w Essential)
    (hOthers : FoundationalExistenceUnrequiredByOthers F w essenceOf esseOf Received
      ComposedOfMatterAndForm CanFailToBe PowerOver Essential) :
    FoundationalBeingsContingentAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver := by
  sorry

/-! ## Laws -/

/-! ## Models -/

macro "eie_unfold" : tactic => `(tactic|
  simp only [FoundationalAt, FoundationalBeingsContingentAt, EntailsExistence,
    EssenceGroundsNecessity, EsseEssenceIsEssentialExistence, ExistenceConditionalEssences,
    EssentialExclusionAccount, FoundationalExistenceUnrequiredByOthers, EssentialTruth,
    ConceptContent, EsseExercisedAt, ConceptContainsExistence, EssentialExistence,
    EsseIsEssence, NatureEntailsExistence, ExistenceNotConceptual, ConceptAdequateToEssence,
    IdentityInConcept, EsseExercisedWhereExists, IdentityPutsExerciseInNature, PowerOverEsse,
    IsFirstBeing, IncorruptibleSimply, NecessaryAt, ContingentAt, kantFrame, requiredFrame,
    effectConcept, exercisedHere, exercisedEverywhere, conditionalExercise, everywhereExercise,
    bothContingent, lockedF, frameOn, toTrue, univ, bothHere, onlyFHere, xContingent,
    fEssentialExistence, noEssence, otherRequiresF, noCause, noPrior, receivedNone, esseTrue,
    essenceByBeing, noneHolds, heatFail, noPower])

/-- Closes the goals `simp` leaves over predicates `φ : Bool → Prop`: universal
ones by `simp_all`, function (in)equalities by evaluation at a point,
existential ones with the witness "true exactly at point `true`". -/
macro "eie_finish" : tactic => `(tactic| first
  | done
  | (intros; simp_all; done)
  | (intro h; have h' := congrFun h false; simp at h'; done)
  | (intro h; have h' := congrFun h true; simp at h'; done)
  | (exact ⟨fun v => v = true, by simp⟩))

macro "eie_bool" : tactic => `(tactic|
  (eie_unfold <;> simp [Bool.forall_bool, Bool.exists_bool] <;> eie_finish))

theorem controls : Controls := by
  sorry

end TruthCore.Results.Ontology.ExistenceInEssence
