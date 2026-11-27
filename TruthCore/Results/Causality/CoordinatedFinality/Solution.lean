module

public import TruthCore.Causality.CoordinatedFinality
public import TruthCore.Results.Causality.PracticalSpecification.Solution

@[expose] public section

namespace TruthCore.Results.Causality.CoordinatedFinality

open TruthCore.Causality.CoordinatedFinality
open TruthCore.Causality.PracticalSpecification
open TruthCore.Causality.StructuralCausalModel
open TruthCore.Explanation.MechanismInterventionParity (Observation natural)
open TruthCore.Science.Identifiability
open TruthCore.Modal.CounterfactualSelection (HasSelection Would)

namespace CoordinationProof

open TruthCore.Causality.CoordinatedFinality.Coordination

theorem meets_iff (o : Observation) : Meets jointPlan () (assessment o) ↔
    o.a = true ∧ o.b = true ∧ o.effect = true := by
  constructor
  · intro h
    exact ⟨h (.output false) trivial, h (.output true) trivial,
      (h (.toward true ()) rfl).2⟩
  · rintro ⟨ha, hb, hf⟩ c hc
    cases c with
    | output x =>
      cases x
      · exact ha
      · exact hb
    | benefit x r => exact False.elim hc
    | toward x e => exact ⟨hc, hf⟩

theorem report_true : report true = ⟨true, true, true⟩ := by
  rw [report, jointModel, three_response]
  rfl

theorem report_false : report false = ⟨true, true, false⟩ := by
  rw [report, jointModel, three_response]
  rfl

theorem fulfilled_true : fulfilled true := by
  unfold fulfilled
  rw [meets_iff, report_true]
  exact ⟨rfl, rfl, rfl⟩

theorem not_fulfilled_false : ¬ fulfilled false := by
  unfold fulfilled
  rw [meets_iff, report_false]
  intro h
  exact Bool.noConfusion h.2.2

theorem same_components : components true = components false := by
  simp only [components, report_true, report_false]

theorem no_component_identification : ¬ Identifies components fulfilled := by
  intro identifies
  exact not_fulfilled_false (Eq.mp (identifies true false same_components) fulfilled_true)

theorem full_identification : Identifies report fulfilled := by
  intro a b h
  unfold fulfilled
  rw [h]

theorem boundary : Coordination.Boundary :=
  ⟨meets_iff, report_true, report_false, fulfilled_true, not_fulfilled_false,
    no_component_identification, full_identification⟩

end CoordinationProof

namespace OperationProof

open TruthCore.Causality.CoordinatedFinality.Operation

theorem coverage_iff (mode : Bool) : operativeCoverage mode ↔ mode = true := by
  cases mode
  · have noCoverage : ¬ operativeCoverage false :=
      TruthCore.Results.Causality.PracticalSpecification.controls.2.1.2.2.1
    exact ⟨fun h => (noCoverage h).elim, fun h => by cases h⟩
  · have yesCoverage : operativeCoverage true :=
      TruthCore.Results.Causality.PracticalSpecification.controls.2.2.2.2.2.1
    exact ⟨fun _ => rfl, fun _ => yesCoverage⟩

theorem natural_agreement (u : TruthCore.Explanation.MechanismInterventionParity.TwoState) :
    naturalReportAt true u = naturalReportAt false u :=
  Mechanism.single_channel_contrast.1 u

theorem natural_true : naturalReport true = ⟨true, true, true⟩ := by
  change Mechanism.readout (Mechanism.responsive.response context (Mechanism.setting natural)) = _
  rw [Mechanism.responsive_matches]
  rfl

theorem cut_reports :
    cutReport true = ⟨true, false, false⟩ ∧ cutReport false = ⟨true, false, true⟩ :=
  Mechanism.single_channel_contrast.2

theorem coverage_iff_cut (mode : Bool) :
    operativeCoverage mode ↔ (cutReport mode).effect = false := by
  rw [coverage_iff]
  cases mode
  · simp only [cut_reports.2, Bool.false_eq_true, Bool.true_eq_false]
  · rw [cut_reports.1]

theorem appraises_and_meets (mode : Bool) :
    (Control.plan mode true true).ApprehendsAsGood false false () ∧
      Meets (Control.plan mode true true) ()
        ((Control.plan mode true true).Realized false false true) :=
  ⟨rfl, fun _ _ => trivial⟩

theorem yes_coverage : operativeCoverage true := (coverage_iff true).mpr rfl

theorem no_coverage : ¬ operativeCoverage false := by
  intro h
  exact Bool.noConfusion ((coverage_iff false).mp h)

theorem natural_not_identifies : ¬ Identifies naturalReport operativeCoverage := by
  intro identifies
  exact no_coverage (Eq.mp (identifies true false (natural_agreement context)) yes_coverage)

theorem augmented_identifies :
    Identifies (fun mode => (naturalReport mode, cutReport mode)) operativeCoverage := by
  intro a b same
  have cuts : cutReport a = cutReport b := congrArg Prod.snd same
  apply propext
  simp only [coverage_iff_cut]
  rw [cuts]

theorem selected_cut (mode : Bool) :
    HasSelection (selector mode) (origin mode) appraisalOff ∧
      (Would (selector mode) (origin mode) appraisalOff fitLost ↔ operativeCoverage mode) := by
  have h : HasSelection (selector mode) (origin mode) appraisalOff ∧
      (Would (selector mode) (origin mode) appraisalOff fitLost ↔ (cutReport mode).effect = false) :=
    selection_forced (mechanism mode) cutSetting (origin mode) (v := .y) (a := false) rfl fitLost
  exact ⟨h.1, h.2.trans (coverage_iff_cut mode).symm⟩

theorem boundary : Operation.Boundary :=
  ⟨natural_agreement, natural_true, cut_reports.1, cut_reports.2, appraises_and_meets,
    yes_coverage, no_coverage, natural_not_identifies, augmented_identifies, selected_cut⟩

end OperationProof

theorem boundary : TruthCore.Causality.CoordinatedFinality.Boundary :=
  ⟨CoordinationProof.boundary, OperationProof.boundary⟩

end TruthCore.Results.Causality.CoordinatedFinality
