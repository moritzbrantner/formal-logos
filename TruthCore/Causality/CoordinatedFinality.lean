module

public import TruthCore.Causality.PracticalSpecification
public import TruthCore.Causality.StructuralCausalAdapters
public import TruthCore.Science.Identifiability

/-!
# Coordinated fulfillment and operative specification

Two matched, stipulated tests of the joint-specification and proper-manifestation
arguments in the existing teleology and creation notes. Reuse the actual Plan
language, the existing SCM and its intervention selector. Boolean variables
represent reported roles, not concrete beings or the source's intrinsic parts.
No metaphysical admissibility, intellect or actuality is inferred from the
choice of a structural equation. In the second test the same profile index
selects a pre-existing practical-plan fixture and an intervention mechanism;
that pairing is supplied data, not a general definition of intentional action.
-/

@[expose] public section

namespace TruthCore.Causality.CoordinatedFinality

open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.StructuralCausalModel
open TruthCore.Causality.InterventionTransitivity (Variable)
open TruthCore.Explanation.MechanismInterventionParity (Observation TwoState natural)
open TruthCore.Science.Identifiability
open TruthCore.Causality.CounterfactualDependence (interventionSelection)
open TruthCore.Modal.CounterfactualSelection (HasSelection Would)

namespace Coordination

/-- The two output slots are independently assessed; the end-placement of the
second is an additional required fit. These are clauses, not an ontology. -/
def assessment (o : Observation) : Clause Bool Unit Unit → Prop
  | .output false => o.a = true
  | .output true => o.b = true
  | .benefit _ _ => False
  | .toward x _ => x = true ∧ o.effect = true

/-- The independently fixed success conditions require both outputs and their
selected fit. Neither apprehension nor operative use is asserted by this
fixture: the question here is whether component observations recover success. -/
def jointPlan : Plan Observation Bool Unit Unit Unit where
  Requirement := fun _ c => match c with
    | .output _ => True
    | .benefit _ _ => False
    | .toward x _ => x = true
  ApprehendsAsGood := fun _ _ _ => False
  SpecifiesGiving := fun _ _ _ _ => False
  Realized := fun o _ _ => assessment o

/-- Component availability is fixed. The explicitly varied background bit
controls fit in the third equation. The setting is natural in both contexts. -/
def jointModel : Model Variable Bool Bool :=
  three (fun _ => true) (fun _ _ => true) (fun fit a b => (a && b) && fit)

def report (fit : Bool) : Observation :=
  Mechanism.readout (jointModel.response fit (fun _ => none))

def components (fit : Bool) : Bool × Bool :=
  ((report fit).a, (report fit).b)

def fulfilled (fit : Bool) : Prop :=
  Meets jointPlan () (assessment (report fit))

def Boundary : Prop :=
  (∀ o : Observation, Meets jointPlan () (assessment o) ↔
    o.a = true ∧ o.b = true ∧ o.effect = true) ∧
  report true = ⟨true, true, true⟩ ∧
  report false = ⟨true, true, false⟩ ∧
  fulfilled true ∧ ¬ fulfilled false ∧
  ¬ Identifies components fulfilled ∧ Identifies report fulfilled

end Coordination

namespace Operation

/-- The existing positive and omission Plan controls, now paired with the
responsive and idle structural mechanisms by the SAME supplied profile bit.
It does not follow from the mechanisms alone that this pairing is correct. -/
def operativeCoverage (mode : Bool) : Prop :=
  Control.coverage (Control.plan mode true true)

def mechanism (mode : Bool) : Model Variable TwoState Bool :=
  if mode then Mechanism.responsive else Mechanism.background

def context : TwoState := ⟨true, true⟩

def naturalReportAt (mode : Bool) (u : TwoState) : Observation :=
  Mechanism.readout ((mechanism mode).response u (Mechanism.setting natural))

def naturalReport (mode : Bool) : Observation := naturalReportAt mode context

/-- Withdraw just the public second input, interpreted in this experiment as
the appraisal report. This is not a possible loss of divine intellect. -/
def cutSetting : Setting Variable Bool := Mechanism.setting ⟨none, some false⟩

def cutReport (mode : Bool) : Observation :=
  Mechanism.readout ((mechanism mode).response context cutSetting)

abbrev ValuationWorld := TwoState × (Variable → Bool)

def origin (mode : Bool) : ValuationWorld :=
  (context, (mechanism mode).response context (Mechanism.setting natural))

def selector (mode : Bool) :=
  interventionSelection (responseWorld (mechanism mode) cutSetting)

def appraisalOff : Set ValuationWorld := {v | v.2 .y = false}
def fitLost : Set ValuationWorld := {v | v.2 .z = false}

def Boundary : Prop :=
  (∀ u, naturalReportAt true u = naturalReportAt false u) ∧
  naturalReport true = ⟨true, true, true⟩ ∧
  cutReport true = ⟨true, false, false⟩ ∧
  cutReport false = ⟨true, false, true⟩ ∧
  (∀ mode, (Control.plan mode true true).ApprehendsAsGood false false () ∧
    Meets (Control.plan mode true true) ()
      ((Control.plan mode true true).Realized false false true)) ∧
  operativeCoverage true ∧ ¬ operativeCoverage false ∧
  ¬ Identifies naturalReport operativeCoverage ∧
  Identifies (fun mode => (naturalReport mode, cutReport mode)) operativeCoverage ∧
  (∀ mode, HasSelection (selector mode) (origin mode) appraisalOff ∧
    (Would (selector mode) (origin mode) appraisalOff fitLost ↔ operativeCoverage mode))

end Operation

def Boundary : Prop := Coordination.Boundary ∧ Operation.Boundary

end TruthCore.Causality.CoordinatedFinality
