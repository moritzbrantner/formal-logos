module

public import TruthCore.Ontology.EssenceActFactInvariance
import TruthCore.Results.Ontology.ExistenceInEssence.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.EssenceActFactInvariance

open TruthCore.Logic.ContentInterpretation (extensionCriterion)
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)
open TruthCore.Modal.ModalGrounding (EsseEssenceIsEssentialExistence)
open TruthCore.Modal.ModalGrounding.Model (bothContingent)
open TruthCore.Ontology.EssenceActFactInvariance
open TruthCore.Ontology.ExistenceInEssence.Model
  (Pr conditionalExercise essenceOfB esseOfB exercisedBy)
open TruthCore.Results.Ontology.ExistenceInEssence
  (conditionalIdentityModel exerciseInNatureGivesEssentialExistence)

private theorem transfer : TransferUnderExtensionCriterion := by
  intro _ I J hSame hCriterion
  exact (extensionCriterion I J).mp hCriterion .exercise .existence hSame

private theorem model : Controls := by
  have same : extension .exercise = extension .existence := rfl
  have apart : extension .exercise ≠ extension .conditionalExercise := by
    intro h
    have hConditional : extension .conditionalExercise false := fun hExists => hExists
    have hExercise : extension .exercise false := (congrFun h false).symm ▸ hConditional
    exact Bool.noConfusion hExercise
  have conditionalIn : conditionalNature .conditionalExercise := ⟨rfl, rfl⟩
  have exerciseOut : ¬ conditionalNature .exercise := fun h => apart h.2
  have existenceOut : ¬ conditionalNature .existence := fun h => apart (same.trans h.2)
  have conditionalCriterion : AdmitsCriterion extension conditionalNature :=
    ⟨conditionalExercise bothContingent true, fun _ => Iff.rfl⟩
  have exerciseIn : exerciseNature .exercise := Or.inr rfl
  have factOut : ¬ exerciseNature .existence := by
    rintro (h | h)
    · exact existenceOut h
    · cases h
  have noCriterion : ¬ AdmitsCriterion extension exerciseNature :=
    fun h => factOut ((transfer Bool extension exerciseNature same h).mp exerciseIn)
  have projected : EsseEssenceIsEssentialExistence bothContingent essenceOfB esseOfB
      (projectedNature exerciseNature) := by
    refine exerciseInNatureGivesEssentialExistence bothContingent essenceOfB esseOfB
      (projectedNature exerciseNature) (exercisedBy bothContingent)
      conditionalIdentityModel.2.2.1 ?_
    intro x hIdentity
    cases x
    · change Pr.creatureEsse = Pr.creatureEssence at hIdentity
      cases hIdentity
    · exact ⟨rfl, .exercise, exerciseIn, rfl⟩
  exact ⟨conditionalIdentityModel, same, apart, conditionalIn, exerciseOut, existenceOut,
    conditionalCriterion, Or.inl conditionalIn, exerciseIn, factOut, noCriterion, projected⟩

theorem fixedBearerControls : FixedBearerControls := ⟨transfer, model⟩

end TruthCore.Results.Ontology.EssenceActFactInvariance
