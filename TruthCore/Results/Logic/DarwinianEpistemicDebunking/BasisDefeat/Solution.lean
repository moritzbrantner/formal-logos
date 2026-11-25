module

public import TruthCore.Logic.DarwinianEpistemicDebunking.BasisDefeat
public import TruthCore.Results.Logic.DarwinianEpistemicDebunking.CrossHistory.Solution
public import TruthCore.Results.Logic.GlobalThesisBoundaries.Solution

@[expose] public section

namespace TruthCore.Results.Logic.DarwinianEpistemicDebunking.BasisDefeat

open TruthCore.Logic.GlobalThesisBoundaries
open TruthCore.Logic.DarwinianEpistemicDebunking
open TruthCore.Logic.DarwinianEpistemicDebunking.BasisDefeat

theorem auditedSelfApplication (f : ReliabilityFrame) (audit : Audit f) (a : f.Agent)
    (E : f.Basis) (target : f.Content) :
    AuditedCrossHistoryPolicy f audit a →
    CorrectnessConstant (audit.profile E) →
    VerdictVariesAcrossHistories (audit.profile E) →
    AuditedBypass f audit a E →
    SoleSupportingBasis f a target E →
    WarrantNeedsUndefeatedSupport f a target →
    LacksTargetWarrant f a target := by
  intro policy fixed varies audited only needs
  exact GlobalThesisBoundaries.undercutSoleBasisPrecludesWarrant f a target E
    (policy E fixed varies audited) only needs

theorem auditedPolicyControls : AuditedPolicyControls := by
  have report (d i : Bool) : AuditedBypass (auditFrame d i) (cueAudit d i) () true :=
    ⟨True.intro, Or.inl rfl, false, Or.inr ⟨rfl, Or.inl rfl⟩,
      fun h => Bool.noConfusion h.1, rfl, rfl⟩
  obtain ⟨⟨fixed, varies, _⟩, _⟩ := CrossHistory.crossHistoryControls
  have retained : ¬ BasisUndercut (auditFrame false false) () true :=
    fun h => Bool.noConfusion h.2
  have policy (i : Bool) : AuditedCrossHistoryPolicy (auditFrame true i) (cueAudit true i) () := by
    intro E _ _ audited
    obtain ⟨_, _, b, _, _, outside⟩ := audited
    exact ⟨outside.2, rfl⟩
  obtain ⟨⟨_, _, _, only, needs, lacks, holds, _⟩, _⟩ := GlobalThesisBoundaries.reliabilityControls
  refine ⟨⟨policy false, fixed, varies, report true false, only, needs, lacks, holds⟩,
    ⟨fixed, varies, report false false, retained, fun policy =>
    retained (policy true fixed varies (report false false))⟩, ?_⟩
  have other : (auditFrame true true).supports () false true :=
    Or.inr ⟨rfl, Or.inr rfl⟩
  refine ⟨⟨policy true, report true true, ⟨rfl, rfl⟩,
    fun only => Bool.noConfusion (only false other),
    ⟨false, other, fun h => Bool.noConfusion h.1⟩, Or.inr (Or.inr rfl)⟩,
    fun h => Bool.noConfusion h, report false false, ?_, retained⟩
  intro E _ ⟨s, _, differs⟩
  exact False.elim (differs rfl)

theorem calibratedSupervenience {X : Type} (p : DarwinianProfile) (F : p.Scenario → X)
    (panel : p.Scenario → Prop) :
    TruthSupervenesOn p F →
    VerdictStableOn p F →
    PanelCovers p F panel →
    PanelAccurate p panel →
    NoScenarioMismatch p := by
  intro supervenes stable covers accurate ⟨s, wrong⟩
  obtain ⟨t, member, sameFactor⟩ := covers s
  exact wrong ((stable s t sameFactor).trans
    ((accurate t member).trans (supervenes s t sameFactor).symm))

end TruthCore.Results.Logic.DarwinianEpistemicDebunking.BasisDefeat
