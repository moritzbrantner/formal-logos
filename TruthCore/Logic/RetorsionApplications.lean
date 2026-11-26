module

public import TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial.Solution
public import TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails.Solution
public import TruthCore.Logic.TruthNontriviality
public import TruthCore.Logic.EpistemicReasonBearer
public import TruthCore.Logic.ScientismScopeBoundary

/-!
# Applications of performed denial and its scope limits

The examples distinguish the content a token denies, a designated truth bearer,
a particular subject's reason, and the scope of an empirical norm.
-/

@[expose] public section

namespace TruthCore.Logic.RetorsionApplications

open TruthCore.Logic.PerformedDenial
open TruthCore.Logic.TruthPilot
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
open TruthCore.Logic.GlobalThesisBoundaries
open TruthCore.Logic.EpistemicReasonBearer
open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.Scientism
open TruthCore.Logic.ScientismScopeBoundary
open TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial

theorem speakingCanDenySinging : ∃ (speaks sings deniesSinging : Unit → Prop) (e : Unit),
    speaks e ∧ deniesSinging e ∧ NoEpisodeOccurs sings := by
  exact ⟨fun _ => True, fun _ => False, fun _ => True, (), trivial, trivial,
    fun ⟨_, h⟩ => h⟩

-- Bool.true indexes the same-token theorem; Bool.false indexes the file report.
theorem fileReportAndPerformedDenial (FileReport : Prop) (readLine : FileReport) :
    let E : EpistemicFrame Bool :=
      ⟨(fun c => if c then ∀ O D : Unit → Prop, AccurateDenialImpossible O D else FileReport),
       (fun c => c = false ∧ FileReport)⟩
    SomeNonEmpiricalEstablished E ∧ ¬ ScopedScientism E (fun _ => True) ∧
      ScopedScientism E (fun c => c = false) ∧ E.established false := by
  dsimp only
  have proofGround : ∀ O D : Unit → Prop, AccurateDenialImpossible O D := noAccurateDenial
  exact ⟨⟨true, proofGround, fun h => Bool.noConfusion h.1⟩,
    fun norm => Bool.noConfusion (norm true trivial proofGround).1,
    fun _ inScope _ => ⟨inScope, readLine⟩, readLine⟩

-- Only the capture direction for one proved content is needed.
theorem designatedTruthExcludesGlobalDenial {Agent Content : Type} (T : TruthSemantics Agent Content)
    (c : Content) (capture : NotEveryPropositionFails → T.trueAbs c) :
    SomeAbsoluteTruth T ∧ ¬ GlobalNoAbsoluteTruth T := by
  have hc := capture
    TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails.notEveryPropositionFails
  exact ⟨⟨c, hc⟩, fun h => h c hc⟩

-- No prior actual acceptance or warrant needed; the evidence is available.
theorem survivingBasisWitnessesReason (f : ReliabilityFrame) (R : f.Agent → f.Content → Prop)
    (a : f.Agent) (b : f.Basis) (p : f.Content)
    (hs : f.supports a b p) (hu : ¬ f.undercuts a b)
    (hCounts : SurvivingBasisGivesReason f R) :
    ThereAreEpistemicReasons R :=
  ⟨a, p, hCounts a b p hs hu⟩

-- Witness to the exact negation and, when in scope, failure of the norm.
theorem nonempiricalClaimDefeatsScopedNorm {Claim : Type} (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (c : Claim) (he : E.established c)
    (hn : ¬ E.empiricallyEstablished c) (hi : scope c) :
    SomeNonEmpiricalEstablished E ∧
      ¬ NoNonEmpiricalEstablished E ∧ ¬ ScopedScientism E scope := by
  have hw : SomeNonEmpiricalEstablished E := ⟨c, he, hn⟩
  exact ⟨hw, fun h => h hw, fun h => hn (h c hi he)⟩

-- The separate exclusive-origin reading; not the existing norm by fiat.
theorem nonobservationalBasisDefeatsExclusiveOrigin {Claim Basis : Type} (S : Claim → Basis → Prop)
    (O : Basis → Prop) (scope : Claim → Prop)
    (p : Claim) (b : Basis) (hi : scope p) (hs : S p b) (hn : ¬ O b) :
    ¬ (∀ p b, scope p → S p b → O b) := by
  intro h
  exact hn (h p b hi hs)

end TruthCore.Logic.RetorsionApplications
