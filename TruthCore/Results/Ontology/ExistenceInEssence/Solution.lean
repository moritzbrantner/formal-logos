module

public import TruthCore.Ontology.ExistenceInEssence

/-! Does existence belong to an essence when essence is identical with esse?
(#1887): the factorization of the unconditional bridge `565ccd6c` into the
act–fact link and exercise in the nature, the Kant-adequacy route to the
"possibly absent" verdict at the foundational case, laws and models.
Analyst formulations; attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Ontology.ExistenceInEssence
open TruthCore.Ontology.ExistenceInEssence
open TruthCore.Ontology.ExistenceInEssence.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Modal.ModalGrounding (EssentialTruth EntailsExistence EssenceGroundsNecessity
  EsseEssenceIsEssentialExistence ExistenceConditionalEssences EssentialExclusionAccount
  FoundationalExistenceUnrequiredByOthers FoundationalBeingsContingentAt FoundationalAt)
open TruthCore.Modal.ModalGrounding.Model (frameOn toTrue univ bothHere bothContingent lockedF
  fEssentialExistence noEssence otherRequiresF FoundationalF onlyFHere Pt ptEx gCausesC gPriorC)
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
  intro x hx
  have h := hAN x hx
  have heq : (fun v => EsseExercisedAt Exercised v (esseOf x)) =
      (fun v => F.history.ontic.ExistsAt v x) :=
    funext fun v => propext (hLink v x)
  unfold EssentialTruth at h
  rw [heq] at h
  exact h

/-- Argument 2, the Kant-adequacy route to "possibly absent". For a
foundational `f`, no essential truth entails its existence: one of `f`'s own
would be contained in the concept (adequacy) and so, by Kant's thesis, not
entail it; no other being's does (unrequired by others). The essentialist
account then makes `f` absent at some accessible world. Constructive; esse =
essence plays no role. -/
theorem kantAdequacyFoundationalContingent {W B T R P : Type}
    (F : CausalityFrame W B T R) (w : W) (essenceOf esseOf : B → P) (Received : B → P → Prop)
    (ComposedOfMatterAndForm : B → Prop) (CanFailToBe : B → R → Prop)
    (PowerOver : B → B → R → Prop) (C : ConceptRelation W B)
    (Essential : B → (W → Prop) → Prop)
    (hKT : ExistenceNotConceptual F C)
    (hAdeq : ConceptAdequateToEssence C Essential)
    (hEPP : EssentialExclusionAccount F w Essential)
    (hOthers : FoundationalExistenceUnrequiredByOthers F w essenceOf esseOf Received
      ComposedOfMatterAndForm CanFailToBe PowerOver Essential) :
    FoundationalBeingsContingentAt F w essenceOf esseOf Received ComposedOfMatterAndForm
      CanFailToBe PowerOver := by
  intro f hf
  refine ⟨hf.1, hEPP f hf.1 fun y φ hE hEnt => ?_⟩
  refine hOthers f hf y φ (fun hyf => ?_) hE hEnt
  subst hyf
  exact hKT y φ (hAdeq y φ hE) hEnt

/-! ## Laws -/

theorem laws : Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B T R F C hKT x h
    exact hKT x _ h fun _ hv => hv
  · rintro W B T R F C Essential hKT hAd x ⟨φ, hE, hEnt⟩
    exact hKT x φ (hAd x φ hE) hEnt
  · intro W B T R P F C Essential essenceOf esseOf hKT hAd hBr x hx
    exact hKT x _ (hAd x _ (hBr x hx)) fun _ hv => hv
  · intro W B T R P F C essenceOf esseOf hKT hId x hx
    exact hKT x _ (hId x hx) fun _ hv => hv
  · intro W B T R F C w hKT hAcc x φ hx hC
    refine ⟨hx, Classical.byContradiction fun h => hKT x φ hC fun v _ => ?_⟩
    exact Classical.byContradiction fun hv => h ⟨v, hAcc v, hv⟩
  · rintro W B T R P F Essential Exercised essenceOf esseOf hEC hLink hAN x hx ⟨v, hv⟩
    exact hv ((hLink v x).1 (hEC x _ (hAN x hx) v hv))
  · intro W B T R P F Exercised essenceOf esseOf hLink x hx v hv
    have h := (hLink v x).2 hv
    unfold EsseIsEssence at hx
    rw [hx] at h
    exact h
  · intro W B T R F Essential x h
    exact ⟨_, h, fun _ hv => hv⟩
  · rintro W B T R F w Essential x hEGN ⟨φ, hE, hEnt⟩ v hv
    exact hEnt v (hEGN x φ hE v hv)
  · rintro W B T R F w Essential x hEGN ⟨_, v, hv, hAbs⟩ ⟨φ, hE, hEnt⟩
    exact hAbs (hEnt v (hEGN x φ hE v hv))
  · intro W B T R F w Essential x hEM hEGN hEPP hOthers hx
    refine ⟨fun ⟨φ, hE, hEnt⟩ v hv => hEnt v (hEGN x φ hE v hv), fun hNec => ?_⟩
    rcases hEM (NatureEntailsExistence F Essential x) with h | h
    · exact h
    · exfalso
      obtain ⟨v, hv, hAbs⟩ := hEPP x hx fun y φ hE hEnt =>
        hOthers y φ (fun hyx => by subst hyx; exact h ⟨φ, hE, hEnt⟩) hE hEnt
      exact hAbs (hNec v hv)
  · rintro W B T R F w Essential x hEGN hSA ⟨φ, hE⟩ v hv
    exact hSA φ hE v (hEGN x φ hE v hv)
  · intro W B T R F C Essential hCNC hAd x φ hE v hv
    exact hCNC x φ (hAd x φ hE) v hv
  · rintro W B T R F C x hCNC ⟨v, hv⟩ φ hC hEnt
    exact hv (hEnt v (hCNC x φ hC v hv))
  · intro W B T R P F Essential Exercised essenceOf esseOf hLink hBr x hx
    have h := hBr x hx
    have heq : (fun v => EsseExercisedAt Exercised v (esseOf x)) =
        (fun v => F.history.ontic.ExistsAt v x) :=
      funext fun v => propext (hLink v x)
    unfold EssentialTruth
    rw [heq]
    exact h

/-! ## Models -/

theorem pt_forall (p : Pt → Prop) : (∀ v, p v) ↔ p .a ∧ p .b ∧ p .c :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨ha, hb, hc⟩ v => by cases v <;> assumption⟩

theorem pt_exists (p : Pt → Prop) : (∃ v, p v) ↔ p .a ∨ p .b ∨ p .c :=
  ⟨fun ⟨v, h⟩ => by cases v <;> simp_all, fun h => by
    rcases h with h | h | h <;> exact ⟨_, h⟩⟩

macro "eie_unfold" : tactic => `(tactic|
  simp only [FoundationalAt, FoundationalBeingsContingentAt, EntailsExistence,
    EssenceGroundsNecessity, EsseEssenceIsEssentialExistence, ExistenceConditionalEssences,
    EssentialExclusionAccount, FoundationalExistenceUnrequiredByOthers, EssentialTruth,
    ConceptContent, EsseExercisedAt, ConceptContainsExistence, EssentialExistence,
    EsseIsEssence, NatureEntailsExistence, ExistenceNotConceptual, ConceptAdequateToEssence,
    ConceptualNecessityConditional, IdentityInConcept, EsseExercisedWhereExists,
    IdentityPutsExerciseInNature, PowerOverEsse, IsFirstBeing, IncorruptibleSimply, NecessaryAt,
    ContingentAt, kantFrame, kaAccess, requiredFrame, effectConcept, adequateConcept,
    emptyConcept, exercisedBy, exercisedEverywhere, conditionalExercise, everywhereExercise,
    esseOfB, essenceOfB, receivedNoneP, bothContingent, lockedF, frameOn, toTrue, univ,
    bothHere, onlyFHere, xContingent, ptEx, gCausesC, gPriorC, fEssentialExistence, noEssence,
    otherRequiresF, noCause, noPrior, receivedNone, esseTrue, essenceByBeing, noneHolds,
    heatFail, noPower])

/-- Closes the goals `simp` leaves over predicates `φ` on points: universal
ones by `simp_all`, function (in)equalities by evaluation at a point,
existential ones with the witness "true exactly at point `true`". -/
macro "eie_finish" : tactic => `(tactic| first
  | done
  | (intros; simp_all; done)
  | (intro h; have h' := congrFun h false; simp at h'; done)
  | (intro h; have h' := congrFun h true; simp at h'; done)
  | (intro h; have h' := congrFun h Pt.c; simp at h'; done)
  | (intro h; have h' := congrFun h Pt.a; simp at h'; done)
  | (exact ⟨fun v => v = true, by simp⟩))

macro "eie_bool" : tactic => `(tactic|
  (eie_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, pt_forall, pt_exists] <;>
    eie_finish))

theorem kantAquinasModel : KantAquinasModel := by
  unfold KantAquinasModel FoundationalPr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> eie_bool

theorem conditionalIdentityModel : ConditionalIdentityModel := by
  unfold ConditionalIdentityModel FoundationalPr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> eie_bool

theorem kantAdequacyOmissions : KantAdequacyOmissions := by
  unfold KantAdequacyOmissions FoundationalF
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> eie_bool

theorem factorizationOmissions : FactorizationOmissions := by
  unfold FactorizationOmissions
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> eie_bool

theorem models : Models :=
  ⟨kantAquinasModel, conditionalIdentityModel, kantAdequacyOmissions, factorizationOmissions⟩

theorem controls : Controls := ⟨laws, models⟩

end TruthCore.Results.Ontology.ExistenceInEssence
