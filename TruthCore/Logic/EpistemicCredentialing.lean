module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

/-!
Analyst comparison for #930/#932/#1007. The existing belief-specific
consideration presentation is retained. Actual reason attribution, a
separate justified credential about that reason, and a prior reason for
the credential are distinct. The prior relation is supplied; its
well-foundedness is an open condition, not part of the meaning of Reason.
No actual epistemic or metaphysical priority principle is established.
-/

@[expose] public section

namespace TruthCore.Logic.EpistemicCredentialing

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- One consideration and the content of its targeted belief. -/
abbrev Instance (f : Frame) := f.Consideration × f.Content

/-- Same-subject, belief-specific attributed reason in the existing frame. -/
def Active (f : Frame) (a : f.Agent) (x : Instance f) : Prop :=
  f.CountsAsReason a x.1 (f.believe x.2)

/-- Additional data only. Certifies relates a credential content to the
particular reason it purports to certify. It does not assert that the
credential is true, believed, warranted or adequate. Prior points from
an independently prior reason instance to the dependent instance, for
the same subject. Actual epistemic interpretation remains open. -/
structure CredentialData (f : Frame) where
  believes : f.Agent → f.Content → Prop
  warranted : f.Agent → f.Content → Prop
  certifies : f.Agent → f.Content → Instance f → Prop
  prior : f.Agent → Instance f → Instance f → Prop

def Credential (f : Frame) (d : CredentialData f) (a : f.Agent)
    (x : Instance f) (c : f.Content) : Prop :=
  d.certifies a c x ∧ d.believes a c ∧ d.warranted a c

/-- C: every attributed belief reason has a believed, warranted credential
for that very instance. No priority or further reason is included. -/
def UniversalCredential (f : Frame) (d : CredentialData f) : Prop :=
  ∀ a x, Active f a x → ∃ c, Credential f d a x c

/-- T: each such credential for an active reason has an active reason
for believing its content, prior to the certified instance. This is a
separate and stronger transfer claim than justified credentialing alone. -/
def PriorCredentialReason (f : Frame) (d : CredentialData f) : Prop :=
  ∀ a x c, Active f a x → Credential f d a x c →
    ∃ s, Active f a (s, c) ∧ d.prior a (s, c) x

/-- W: the supplied epistemic priority relation is well-founded for each
subject. No temporal or causal priority identification is made. -/
def CredentialWellFounded (f : Frame) (d : CredentialData f) : Prop :=
  ∀ a, WellFounded (d.prior a)

/-- Exact negation of C; not a claim about every reason being basic. -/
def UniversalCredentialFails (f : Frame) (d : CredentialData f) : Prop :=
  ¬ UniversalCredential f d

/-- The complete same-frame incompatibility, including the existing
presentation premise. No choice among the members is asserted. -/
def CredentialBundleInconsistent (f : Frame) (d : CredentialData f) : Prop :=
  ¬ (ThereAreEpistemicReasons f.Reason ∧ ConsiderationPresentation f ∧
    UniversalCredential f d ∧ PriorCredentialReason f d ∧ CredentialWellFounded f d)

/-- All credential claims false, with empty priority. -/
def emptyData (f : Frame) : CredentialData f where
  believes := fun _ _ => True
  warranted := fun _ _ => True
  certifies := fun _ _ _ => False
  prior := fun _ _ _ => False

/-- Credentials provided in the same goal-relative frame, but no priority. -/
def flatData : CredentialData goalRelative where
  believes := fun _ _ => True
  warranted := fun _ _ => True
  certifies := fun _ c _ => c = .even
  prior := fun _ _ _ => False

/-- A structural infinite-chain profile, not an account of actual
infinitist justification. The credential content of n is n+1. -/
def streamFrame : Frame where
  Agent := Unit
  Consideration := Unit
  Content := Nat
  Attitude := Nat
  Preference := Unit
  about := id
  believe := id
  beliefAbout := fun _ => rfl
  Reason := fun _ _ => True
  CountsAsReason := fun _ _ _ => True
  assessable := fun _ => True
  applies := fun _ _ _ => True
  favors := fun _ _ _ => True
  Holds := fun _ => True
  produces := fun _ _ _ => False
  rewards := fun _ _ _ => False
  force := fun _ _ _ _ => False
  actualPreference := fun _ => ()

def streamData : CredentialData streamFrame where
  believes := fun _ _ => True
  warranted := fun _ _ => True
  certifies := fun _ c x => c = Nat.succ x.2
  prior := fun _ y x => Nat.lt x.2 y.2

/-- Same carriers as the old frame with both reason extensions empty. -/
def noReasonFrame : Frame :=
  { goalRelative with
    Reason := fun _ _ => False
    CountsAsReason := fun _ _ _ => False }

/-- One-premise omissions for the displayed five-member bundle. C, T,
presentation and F6 omissions are finite. The W omission is an infinite
strict priority chain; it does not claim a finite acyclic serial graph.
The fields are stipulated interpretations, not actual warranted beliefs. -/
def CredentialControls : Prop :=
  (ThereAreEpistemicReasons goalRelative.Reason ∧ ConsiderationPresentation goalRelative ∧
    ¬ UniversalCredential goalRelative (emptyData goalRelative) ∧
    PriorCredentialReason goalRelative (emptyData goalRelative) ∧
    CredentialWellFounded goalRelative (emptyData goalRelative)) ∧
  (ThereAreEpistemicReasons goalRelative.Reason ∧ ConsiderationPresentation goalRelative ∧
    UniversalCredential goalRelative flatData ∧ ¬ PriorCredentialReason goalRelative flatData ∧
    CredentialWellFounded goalRelative flatData) ∧
  (ThereAreEpistemicReasons streamFrame.Reason ∧ ConsiderationPresentation streamFrame ∧
    UniversalCredential streamFrame streamData ∧ PriorCredentialReason streamFrame streamData ∧
    ¬ CredentialWellFounded streamFrame streamData ∧
    (∀ a x, ¬ streamData.prior a x x) ∧
    (∀ a x y z, streamData.prior a x y → streamData.prior a y z → streamData.prior a x z)) ∧
  (ThereAreEpistemicReasons unpresented.Reason ∧ ¬ ConsiderationPresentation unpresented ∧
    UniversalCredential unpresented (emptyData unpresented) ∧
    PriorCredentialReason unpresented (emptyData unpresented) ∧
    CredentialWellFounded unpresented (emptyData unpresented)) ∧
  (EpistemicNihilism noReasonFrame.Reason ∧ ConsiderationPresentation noReasonFrame ∧
    UniversalCredential noReasonFrame (emptyData noReasonFrame) ∧
    PriorCredentialReason noReasonFrame (emptyData noReasonFrame) ∧
    CredentialWellFounded noReasonFrame (emptyData noReasonFrame))

end TruthCore.Logic.EpistemicCredentialing
