module

public import TruthCore.Logic.EpistemicCredentialing
public import TruthCore.Results.Logic.EpistemicUnderminers.Solution
public import TruthCore.Results.Logic.EpistemicReasonBearer.Solution

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicCredentialing

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork
open TruthCore.Logic.EpistemicCredentialing
open TruthCore.Logic.EpistemicUnderminers
open TruthCore.Logic.EpistemicReasonBearer
open TruthCore.Logic.GlobalThesisBoundaries

/-- Induction on the supplied same-subject credential priority. -/
theorem noReasonsFromCredentials (f : Frame) (d : CredentialData f)
    (hPresentation : ConsiderationPresentation f)
    (hCredential : UniversalCredential f d)
    (hPrior : PriorCredentialReason f d)
    (hWF : CredentialWellFounded f d) :
    EpistemicNihilism f.Reason := by
  intro a p hp
  obtain ⟨r, hr⟩ := (hPresentation a p).mp hp
  have noActive : ∀ x : Instance f, ¬ Active f a x := by
    intro x
    induction (hWF a).apply x with
    | intro y _ ih =>
      intro hy
      obtain ⟨c, hc⟩ := hCredential a y hy
      obtain ⟨s, hs, hEdge⟩ := hPrior a y c hy hc
      exact (ih (s, c) hEdge) hs
  exact noActive (r, p) hr

/-- F6 forces a failure of C if the other credential commitments hold. -/
theorem universalCredentialFails (f : Frame) (d : CredentialData f)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hPrior : PriorCredentialReason f d)
    (hWF : CredentialWellFounded f d) :
    UniversalCredentialFails f d := by
  intro hCredential
  exact TruthCore.Results.Logic.EpistemicUnderminers.f6ExcludesNihilism f.Reason hThin
    (noReasonsFromCredentials f d hPresentation hCredential hPrior hWF)

/-- The complete incompatible bundle, without any philosophical premise. -/
theorem credentialBundleInconsistent (f : Frame) (d : CredentialData f) :
    CredentialBundleInconsistent f d := by
  rintro ⟨hThin, hPresentation, hCredential, hPrior, hWF⟩
  exact universalCredentialFails f d hThin hPresentation hPrior hWF hCredential

/-- Connect to warranted acceptance using the existing two calibrations. -/
theorem noWarrantedAcceptanceFromNihilism (f : ReliabilityFrame)
    (Reason : f.Agent → f.Content → Prop)
    (hNone : EpistemicNihilism Reason)
    (hNeeds : AcceptedWarrantNeedsBasis f)
    (hCounts : SurvivingBasisGivesReason f Reason) :
    NoJustifiedBeliefs f.accepts f.warranted := by
  intro hBelief
  exact TruthCore.Results.Logic.EpistemicUnderminers.f6ExcludesNihilism Reason
    (TruthCore.Results.Logic.EpistemicReasonBearer.reasonsFromWarrant f Reason
      hBelief hNeeds hCounts) hNone

private theorem emptyPrior (f : Frame) : PriorCredentialReason f (emptyData f) := by
  intro a x c _ hc
  exact False.elim hc.1

private theorem emptyWF (f : Frame) : CredentialWellFounded f (emptyData f) := by
  intro a
  exact ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩

private theorem goalThin : ThereAreEpistemicReasons goalRelative.Reason :=
  ⟨(), .even, rfl⟩

private theorem goalPresentation : ConsiderationPresentation goalRelative := by
  intro _ p
  constructor
  · intro hp
    exact ⟨.count, rfl, hp⟩
  · rintro ⟨_, _, hp⟩
    exact hp

private theorem emptyNoCredential : ¬ UniversalCredential goalRelative (emptyData goalRelative) := by
  intro h
  obtain ⟨c, hc⟩ := h () (.count, .even) ⟨rfl, rfl⟩
  exact hc.1

private theorem flatCredential : UniversalCredential goalRelative flatData := by
  intro a x _
  exact ⟨.even, rfl, trivial, trivial⟩

private theorem flatNoPrior : ¬ PriorCredentialReason goalRelative flatData := by
  intro h
  obtain ⟨s, _, hbad⟩ := h () (.count, .even) .even ⟨rfl, rfl⟩ ⟨rfl, trivial, trivial⟩
  exact hbad

private theorem flatWF : CredentialWellFounded goalRelative flatData := by
  intro a
  exact ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩

private theorem streamThin : ThereAreEpistemicReasons streamFrame.Reason :=
  ⟨(), 0, trivial⟩

private theorem streamPresentation : ConsiderationPresentation streamFrame := by
  intro _ _
  exact ⟨fun _ => ⟨(), trivial⟩, fun _ => trivial⟩

private theorem streamCredential : UniversalCredential streamFrame streamData := by
  intro _ x _
  exact ⟨x.2 + 1, rfl, trivial, trivial⟩

private theorem streamPrior : PriorCredentialReason streamFrame streamData := by
  intro a x c _ hc
  have he : c = x.2 + 1 := hc.1
  refine ⟨(), trivial, ?_⟩
  change x.2 < c
  exact he.symm ▸ Nat.lt_succ_self x.2

private theorem streamNotWF : ¬ CredentialWellFounded streamFrame streamData := by
  intro hw
  exact noReasonsFromCredentials streamFrame streamData streamPresentation streamCredential
    streamPrior hw () 0 trivial

private theorem unpresentedNoPresentation : ¬ ConsiderationPresentation unpresented := by
  intro h
  obtain ⟨_, hr⟩ := (h () .even).mp rfl
  exact hr

private theorem noReasonPresentation : ConsiderationPresentation noReasonFrame := by
  intro _ _
  exact ⟨fun h => False.elim h, fun ⟨_, h⟩ => h⟩

theorem controls : CredentialControls := by
  exact ⟨
    ⟨goalThin, goalPresentation, emptyNoCredential, emptyPrior goalRelative, emptyWF goalRelative⟩,
    ⟨goalThin, goalPresentation, flatCredential, flatNoPrior, flatWF⟩,
    ⟨streamThin, streamPresentation, streamCredential, streamPrior, streamNotWF,
      fun _ x h => (Nat.lt_irrefl x.2) h,
      fun _ _ _ _ hxy hyz => Nat.lt_trans hyz hxy⟩,
    ⟨⟨(), .even, rfl⟩, unpresentedNoPresentation,
      fun _ _ h => False.elim h, emptyPrior unpresented, emptyWF unpresented⟩,
    ⟨fun _ _ h => h, noReasonPresentation, fun _ _ h => False.elim h,
      emptyPrior noReasonFrame, emptyWF noReasonFrame⟩⟩

end TruthCore.Results.Logic.EpistemicCredentialing
