module

public import TruthCore.Logic.DarwinianEpistemicDebunking

/-! Analyst reconstruction for #1615. A report identifies the production of
one basis's verdict by a cue that bypasses a specified local comparison.
Whether the cue itself is informative is a further question. -/

@[expose] public section

namespace TruthCore.Logic.DarwinianEpistemicDebunking.BasisDefeat

open TruthCore.Logic.GlobalThesisBoundaries

/-- An interpretation, supplied separately for each application. The report
for E describes cue-based production bypassing the specified comparison in
the target class. 'reliesOnAdequateOutside a b E' says that a actually uses b for this
report and b supplies sufficient grounds for it apart from the suspect operation of E.
A different basis label alone does not establish either condition. -/
structure Audit (f : ReliabilityFrame) where
  profile : f.Basis → DarwinianProfile
  report : f.Basis → f.Content
  reliesOnAdequateOutside : f.Agent → f.Basis → f.Basis → Prop

/-- The subject accepts the warranted process report and has a surviving
basis actually used and adequate apart from the targeted operation. Report content
and evidential provenance are application inputs. -/
def AuditedBypass (f : ReliabilityFrame) (audit : Audit f) (a : f.Agent) (E : f.Basis) : Prop :=
  f.accepts a (audit.report E) ∧ f.warranted a (audit.report E) ∧
    ∃ b, f.supports a b (audit.report E) ∧ ¬ f.undercuts a b ∧ audit.reliesOnAdequateOutside a b E

/-- Contested sufficient condition for full local defeat. Uniform over the
fixed subject's roster. Neither actual falsity nor mere report availability
meets this antecedent. -/
def AuditedCrossHistoryPolicy (f : ReliabilityFrame) (audit : Audit f) (a : f.Agent) : Prop :=
  ∀ E, CorrectnessConstant (audit.profile E) → VerdictVariesAcrossHistories (audit.profile E) →
    AuditedBypass f audit a E → BasisUndercut f a E

/-- One subject accepts the report (false-labelled content) and the target
(true-labelled content). Reuse the reliability controls' supporting bases. -/
def auditFrame (defeat independent : Bool) : ReliabilityFrame :=
  { reliabilityControl true defeat independent with accepts := fun _ _ => True }

def cueAudit (defeat independent : Bool) : Audit (auditFrame defeat independent) where
  profile := fun (E : Bool) => if E then crossHistory else fixedTrue
  report := fun _ => false
  reliesOnAdequateOutside := fun _ b E => b = false ∧ E = true

/-- A report on a constantly mistaken verdict. Preserve the report and
provenance inputs and change only the profiles in the no-defeat frame. -/
def mistakenAudit : Audit (auditFrame false false) :=
  { cueAudit false false with profile := fun _ => { fixedTrue with verdict := fun _ => false } }

/-- The same fixed truth, variation and independently warranted report can
accompany rejection of the policy, or acceptance with other support for the
target. Truth and warrant are independent fields in these controls. -/
def AuditedPolicyControls : Prop :=
  let f := auditFrame false false
  let u := cueAudit false false
  let g := auditFrame true true
  let v := cueAudit true true
  let h := auditFrame true false
  let w := cueAudit true false
  (AuditedCrossHistoryPolicy h w () ∧ CorrectnessConstant (w.profile true) ∧
    VerdictVariesAcrossHistories (w.profile true) ∧ AuditedBypass h w () true ∧
    SoleSupportingBasis h () true true ∧ WarrantNeedsUndefeatedSupport h () true ∧
    LacksTargetWarrant h () true ∧ h.holds true) ∧
  (CorrectnessConstant (u.profile true) ∧ VerdictVariesAcrossHistories (u.profile true) ∧
    AuditedBypass f u () true ∧ ¬ BasisUndercut f () true ∧ ¬ AuditedCrossHistoryPolicy f u ()) ∧
  (AuditedCrossHistoryPolicy g v () ∧ AuditedBypass g v () true ∧
    BasisUndercut g () true ∧ ¬ SoleSupportingBasis g () true true ∧
    UndefeatedSupport g () true ∧ g.warranted () true) ∧
  (¬ ActuallyAccurate (mistakenAudit.profile true) ∧ AuditedBypass f mistakenAudit () true ∧
    AuditedCrossHistoryPolicy f mistakenAudit () ∧ ¬ BasisUndercut f () true)

/-- Truth supervenes on F within this profile: equal factor values imply
equal correctness. This constraint leaves the direction of calibration open. -/
def TruthSupervenesOn {X : Type} (p : DarwinianProfile) (F : p.Scenario → X) : Prop :=
  ∀ s t, F s = F t → p.correct s = p.correct t

/-- The selected verdict is stable within each factor value in this class. -/
def VerdictStableOn {X : Type} (p : DarwinianProfile) (F : p.Scenario → X) : Prop :=
  ∀ s t, F s = F t → p.verdict s = p.verdict t

/-- A designated calibration panel covers every realized factor value. -/
def PanelCovers {X : Type} (p : DarwinianProfile) (F : p.Scenario → X)
    (panel : p.Scenario → Prop) : Prop :=
  ∀ s, ∃ t, panel t ∧ F s = F t

/-- Verdicts agree with correctness on the specified calibration panel. -/
def PanelAccurate (p : DarwinianProfile) (panel : p.Scenario → Prop) : Prop :=
  ∀ t, panel t → p.verdict t = p.correct t

/-- No incorrect verdict in the represented class. -/
def NoScenarioMismatch (p : DarwinianProfile) : Prop := ¬ ScenarioMismatch p

end TruthCore.Logic.DarwinianEpistemicDebunking.BasisDefeat
