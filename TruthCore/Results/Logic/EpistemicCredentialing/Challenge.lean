import TruthCore.Logic.EpistemicCredentialing
import TruthCore.Results.Logic.EpistemicUnderminers.Solution
import TruthCore.Results.Logic.EpistemicReasonBearer.Solution

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
  sorry

/-- F6 forces a failure of C if the other credential commitments hold. -/
theorem universalCredentialFails (f : Frame) (d : CredentialData f)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hPrior : PriorCredentialReason f d)
    (hWF : CredentialWellFounded f d) :
    UniversalCredentialFails f d := by
  sorry

/-- The complete incompatible bundle, without any philosophical premise. -/
theorem credentialBundleInconsistent (f : Frame) (d : CredentialData f) :
    CredentialBundleInconsistent f d := by
  sorry

/-- Connect to warranted acceptance using the existing two calibrations. -/
theorem noWarrantedAcceptanceFromNihilism (f : ReliabilityFrame)
    (Reason : f.Agent → f.Content → Prop)
    (hNone : EpistemicNihilism Reason)
    (hNeeds : AcceptedWarrantNeedsBasis f)
    (hCounts : SurvivingBasisGivesReason f Reason) :
    NoJustifiedBeliefs f.accepts f.warranted := by
  sorry

theorem controls : CredentialControls := by
  sorry

end TruthCore.Results.Logic.EpistemicCredentialing
