module

public import TruthCore.Causality.GradesFrame
public import TruthCore.Causality.GodMaximalCausal
public import TruthCore.Case.Catholicism.ClassicalAttributesJointWitness

@[expose] public section
namespace TruthCore.Case.Catholicism.AttributesFromEsse
open TruthCore.Causality.Grades

/-- The single actuality field is kept fixed at the effect and its source.
Formal, virtual and inclusive determinations remain open. -/
def PerfectInFrame {W B T R : Type} (F : GradesFrame W B T R) (IsGod : B → Prop) : Prop :=
  GodIsPerfect IsGod F.InAct


namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.GodMaximalCausal
open TruthCore.Greek.Aristotle.Metaphysics

def named (x : Bool) : Prop := x = false
def edge (c x : Bool) : Prop := c = false ∧ x = true
def gift (c x r : Bool) : Prop := edge c x ∧ r = false
def higher (r c x : Bool) : Prop := gift c x r
def empty (_ _ _ : Bool) : Prop := False
def allAct (_ _ : Bool) : Prop := True
def extra (x r : Bool) : Prop := x = true ∨ r = false
def splitAct (x r : Bool) : Prop := x = r

/-- Full-description naming is exercised at a real source, with a distinct actual recipient.
Reuse the complete original nonlogical stage-two assignment. -/
def Joint : Prop :=
  let A := ClassicalAttributesJointWitness.InAct
  let C := ClassicalAttributesJointWitness.CausesIn
  let M := ClassicalAttributesJointWitness.MoreIn
  let component := ClassicalAttributesJointWitness.ComponentOf
  MaximeEnsCausesBeingOfAllReading A M C false ∧
  GodCausesBeingOfAllOthers named C false ∧
  GodNamesTheFullyDescribedPrinciple A M C false component named ∧
  IsMaximumIn A M false false ∧ CausesAllInGenus A C false false ∧
  CausesEveryPerfectionOfOthers A C false ∧ RemoteFromAll component false ∧
  (∀ k, IsMaximumIn A M false k → k = false) ∧ named false ∧
  A true false ∧ C false true false ∧
  GodIsPerfect named A ∧ GodIsSupremelyGood named A A C false

/-- Separate the two directions of the genus/converse comparison. The second model
has an inactive other carrier; the last model has a represented actuality there
in a different respect, exposing the actuality-to-being premise. -/
def Scope : Prop :=
  (GodCausesBeingOfAllOthers named gift false ∧
    ¬ MaximumInGenusCausesAllInGenusReading allAct higher gift) ∧
  (let A := fun x (_ : Bool) => named x
   MaximumInGenusCausesAllInGenusReading A empty empty ∧
   MaximeEnsCausesBeingOfAllReading A empty empty false ∧ named false ∧
   ¬ GodCausesBeingOfAllOthers named empty false) ∧
  (MaximeEnsCausesBeingOfAllReading splitAct empty empty false ∧
    GodIsMaximalInBeing named splitAct empty false ∧
    CauseOfQualityInAnotherIsMoreSuchReading empty empty ∧
    PerfectionsOfEffectPreexistInCauseReading splitAct empty false ∧
    GoodnessIsActualityReading splitAct splitAct ∧
    UniversalCauseTransfersPerfections splitAct empty false ∧
    ¬ ActualityOnlyInsofarAsBeingReading splitAct false ∧
    ¬ GodIsPerfect named splitAct ∧ ¬ GodIsSupremelyGood named splitAct splitAct empty false)

/-- Each conjunct retains the remaining nonlogical inputs of the named strong
attribute proof. The first row drops the common cause input of both proofs. -/
def Omissions : Prop :=
  (GodIsMaximalInBeing named extra empty false ∧ GoodnessIsActualityReading extra extra ∧
    CauseOfBeingCausesEveryPerfection extra empty false ∧
    PerfectionsOfEffectPreexistInCauseReading extra empty false ∧
    ¬ GodIsPerfect named extra ∧ ¬ GodIsSupremelyGood named extra extra empty false) ∧
  (GodCausesBeingOfAllOthers named gift false ∧ ¬ GodIsPerfect named extra) ∧
  (let A := fun (_ : Bool) (r : Bool) => r = true
   let C := fun c x (_ : Bool) => edge c x
   GodCausesBeingOfAllOthers named C false ∧ GoodnessIsActualityReading A A ∧
   CauseOfBeingCausesEveryPerfection A C false ∧ ¬ GodIsSupremelyGood named A A C false) ∧
  (let G := fun (_ _ : Bool) => False
   let C := fun c x (_ : Bool) => edge c x
   GodCausesBeingOfAllOthers named C false ∧ GodIsMaximalInBeing named allAct empty false ∧
   CauseOfBeingCausesEveryPerfection allAct C false ∧ ¬ GodIsSupremelyGood named allAct G C false) ∧
  (GodCausesBeingOfAllOthers named gift false ∧ GodIsMaximalInBeing named allAct higher false ∧
    GoodnessIsActualityReading allAct allAct ∧ ¬ GodIsSupremelyGood named allAct allAct gift false)

def Checks : Prop := Joint ∧ Scope ∧ Omissions
end Control

end TruthCore.Case.Catholicism.AttributesFromEsse
