module

public import TruthCore.Logic.ContentInterpretation
public import TruthCore.Ontology.ExistenceInEssence

/-! Act and fact contents for the one identity bearer of the existing
conditional-exercise model. The content tags distinguish the inputs to a
nature judgment before interpreting them as predicates of worlds. -/

@[expose] public section

namespace TruthCore.Ontology.EssenceActFactInvariance

open TruthCore.Logic.ContentInterpretation (Interpretation)
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.ModalGrounding.Model (bothContingent)
open TruthCore.Ontology.ExistenceInEssence
open TruthCore.Ontology.ExistenceInEssence.Model

/-- The three contents all concern the same selected bearer. These tags
specify the model's inputs, with no claim that actual nature judgments
individuate contents this way. -/
inductive Content where
  | exercise
  | existence
  | conditionalExercise
  deriving DecidableEq

/-- The conditional model's bearer is `true`. At `false` it is absent and
its act is unexercised, while the conditional holds there. -/
def extension : Interpretation Bool Content
  | .exercise => fun v => EsseExercisedAt (exercisedBy bothContingent) v (esseOfB true)
  | .existence => fun v => bothContingent.history.ontic.ExistsAt v true
  | .conditionalExercise => fun v =>
      bothContingent.history.ontic.ExistsAt v true → exercisedBy bothContingent v (esseOfB true)

/-- Pull the existing nature judgment for `true` back along the interpretation. -/
def conditionalNature (c : Content) : Prop :=
  conditionalExercise bothContingent true (extension c)

/-- Keep the conditional and add unconditional exercise as individuated
content. This changes the nature judgment while keeping bearer and frame. -/
def exerciseNature (c : Content) : Prop :=
  conditionalNature c ∨ c = .exercise

/-- What a world-predicate judgment sees when it records the extension of
each accepted content. The selected bearer alone receives such entries. -/
def projectedNature (J : Content → Prop) (x : Bool) (φ : Bool → Prop) : Prop :=
  x = true ∧ ∃ c, J c ∧ extension c = φ

/-- Global factorization through world extensions suffices for substitution
of this pair. The judgment is supplied at one fixed bearer. -/
def TransferUnderExtensionCriterion : Prop :=
  ∀ (W : Type) (I : Interpretation W Content) (J : Content → Prop),
    I .exercise = I .existence → AdmitsCriterion I J → (J .exercise ↔ J .existence)

/-- The established conditional model, its lifted nature judgment, and
a changed judgment whose projection reports essential existence despite
the absence of the existence content. -/
def Controls : Prop :=
  ConditionalIdentityModel ∧
  extension .exercise = extension .existence ∧
  extension .exercise ≠ extension .conditionalExercise ∧
  conditionalNature .conditionalExercise ∧
  ¬ conditionalNature .exercise ∧ ¬ conditionalNature .existence ∧
  AdmitsCriterion extension conditionalNature ∧
  exerciseNature .conditionalExercise ∧
  exerciseNature .exercise ∧ ¬ exerciseNature .existence ∧
  ¬ AdmitsCriterion extension exerciseNature ∧
  EsseEssenceIsEssentialExistence bothContingent essenceOfB esseOfB (projectedNature exerciseNature)

/-- The general transfer condition and its finite scope test. -/
def FixedBearerControls : Prop :=
  TransferUnderExtensionCriterion ∧ Controls

end TruthCore.Ontology.EssenceActFactInvariance
