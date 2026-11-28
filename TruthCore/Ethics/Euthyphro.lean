module

public import TruthCore.Metaethics.GoodnessFormEnd
public import TruthCore.Metaethics.GoodnessCorrectSupport
public import TruthCore.Logic.ObjectiveTruthDefinitionFork

/-!
# Euthyphro: a modal test of the fixed-assessor approval account

Analyst formulation; attribution deferred. The classic dilemma ("is it good
because approved, or approved because good?") is read as a *modal* test of the
named fixed-assessor approval proposal of `GoodnessFormEnd.DefinitionSpace`.
That space is extensional in one fixed profile, so the arbitrariness objection
(goodness would covary with the assessor's attitude while the natures stay
fixed) cannot be stated there. `ProfileFamily` adds the missing structure.

* Forms, ends and due standards are the base frame's in every profile: they are
  not indexed by profile. A profile fixes which perfections bearers actually
  have (`hasAt`), which aspects are good (`goodAt`) and which aspects the one
  assessor named by the space approves (`approvesAt`). Same natures means the
  same actual perfections under the shared forms, ends and standards.
* The base profile reproduces the frame's `Has` and `GoodIn` and the space's
  `approves`, pointwise.
* Which assessor is named (a human, an ideal observer, God) is an
  interpretation of the space, not a Lean parameter. The theorems apply to any
  assessor; human and divine instances differ only in whether the assessor's
  approvals can vary while natures are fixed (`ApprovalVariesWithNaturesFixed`).

Profiles are a selected range of formal interpretations. No claim is made that
they exhaust, or are, metaphysically possible worlds. Invariance and variation
are explicit premises, never built into the structure.

Reuse note. `SupervenienceProfiles.Strong` compares single cases across worlds
by a Bool-valued natural profile; with `hasAt` as that profile it is false for
the due-actuality account (actual knife mass and actual counterweight mass have
the same actuality value and different due status). The supervenience used here
is global over whole profiles with forms and ends held fixed, and is stated by
pointwise `Iff` to stay zero-axiom; Mathlib's `Function.FactorsThrough` would
need equality of Prop-valued functions.
-/

@[expose] public section

namespace TruthCore.Ethics.Euthyphro

open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
open TruthCore.Logic

/-- A family of evaluative profiles over one base frame and one named
definition space. Forms, ends and due standards are shared; actual perfections,
goodness and the named assessor's approvals are profile-relative. -/
structure ProfileFamily {f : Frame} (s : DefinitionSpace f) where
  Profile : Type
  base : Profile
  hasAt : Profile → f.Being → f.Perfection → Prop
  goodAt : Profile → f.Being → f.Perfection → Prop
  approvesAt : Profile → f.Being → f.Perfection → Prop
  baseHas : ∀ x p, hasAt base x p ↔ f.Has x p
  baseGood : ∀ x p, goodAt base x p ↔ f.GoodIn x p
  baseApproves : ∀ x p, approvesAt base x p ↔ s.approves x p

section
variable {f : Frame} {s : DefinitionSpace f}

/-- Two profiles agree on every bearer's actual perfections (forms, ends and
due standards are shared by construction). -/
def SameNatures (m : ProfileFamily s) (w v : m.Profile) : Prop :=
  ∀ x p, m.hasAt w x p ↔ m.hasAt v x p

def SameGoodness (m : ProfileFamily s) (w v : m.Profile) : Prop :=
  ∀ x p, m.goodAt w x p ↔ m.goodAt v x p

def SameApprovals (m : ProfileFamily s) (w v : m.Profile) : Prop :=
  ∀ x p, m.approvesAt w x p ↔ m.approvesAt v x p

/-- Strong invariance premise: goodness supervenes on the natural base across
the whole family. Any two profiles with the same natures agree on goodness. -/
def GoodnessSupervenes (m : ProfileFamily s) : Prop :=
  ∀ w v, SameNatures m w v → SameGoodness m w v

/-- Weak invariance premise: goodness at the base is unchanged in every profile
that keeps the base natures, whatever the assessor approves there. -/
def GoodnessInvariantUnderApprovalVariation (m : ProfileFamily s) : Prop :=
  ∀ v, SameNatures m m.base v → SameGoodness m m.base v

/-- The named assessor's approvals differ in some profile that keeps the base
natures (horn 1's "commanded cruelty" case). -/
def ApprovalVariesWithNaturesFixed (m : ProfileFamily s) : Prop :=
  ∃ v, SameNatures m m.base v ∧ ¬ SameApprovals m m.base v

/-- The assessor's approvals are fixed by the natures: every profile that keeps
the base natures keeps the base approvals. -/
def ApprovalsFixedByNatures (m : ProfileFamily s) : Prop :=
  ∀ v, SameNatures m m.base v → SameApprovals m m.base v

/-- In profile `w` approval and goodness coextend. -/
def ApprovalCorrectAt (m : ProfileFamily s) (w : m.Profile) : Prop :=
  ∀ x p, m.goodAt w x p ↔ m.approvesAt w x p

/-- Approval-as-ground, modally read: in every profile with the base natures,
goodness coextends with the assessor's approval. Includes the base. -/
def ApprovalGroundsAcrossNatureFixed (m : ProfileFamily s) : Prop :=
  ∀ v, SameNatures m m.base v → ApprovalCorrectAt m v

/-- Exact negation of the modal approval-as-ground reading. -/
def ApprovalDoesNotGround (m : ProfileFamily s) : Prop :=
  ¬ ApprovalGroundsAcrossNatureFixed m

/-- Rigidity bridge: if approval coextends with goodness at the base, it does so
in every profile with the base natures. This separates a defining or grounding
approval account from accidental coextension; it is an explicit open premise. -/
def ApprovalCorrectnessTransfers (m : ProfileFamily s) : Prop :=
  ApprovalCorrectAt m m.base → ApprovalGroundsAcrossNatureFixed m

/-- Rigidified actual-approval account: approval coextends with goodness at the
base, base goodness is kept in every nature-fixed profile, and the assessor's
approvals vary there. Goodness is what the assessor actually approves, not what
it would approve. It concedes invariance and denies the transfer bridge. -/
def RigidifiedApprovalAccount (m : ProfileFamily s) : Prop :=
  ApprovalCorrectAt m m.base ∧ GoodnessInvariantUnderApprovalVariation m ∧
    ApprovalVariesWithNaturesFixed m

/-- The divine-command theorist's price, stated as the equivalence it must
accept under approval-as-ground: goodness invariance holds exactly when the
assessor's approvals are fixed by the natures. -/
def GroundedInvarianceNeedsNatureFixedApproval (m : ProfileFamily s) : Prop :=
  GoodnessInvariantUnderApprovalVariation m ↔ ApprovalsFixedByNatures m

/-- The nature (due-actuality) account read robustly over the family: in every
profile goodness coextends with due actuality under the shared standards and
that profile's actual perfections. -/
def RobustDueAccount (m : ProfileFamily s) : Prop :=
  ∀ w x p, m.goodAt w x p ↔ (Due f x p ∧ m.hasAt w x p)

/-- Adapter to the existing attitude-profile truth frame: sentences are aspects
("x is good in p"), attitude profiles are the profiles keeping the base natures,
and the actual profile is the base. Weak invariance is exactly `Stable` truth of
every aspect over this frame (a conjunct of `Controls`). The `objective` field
is filled with base goodness and is not used. -/
def natureFixedTruthFrame (m : ProfileFamily s) : ObjectiveTruthDefinitionFork.Frame where
  Sentence := f.Being × f.Perfection
  AttitudeProfile := {v : m.Profile // SameNatures m m.base v}
  actual := ⟨m.base, fun _ _ => Iff.rfl⟩
  holds := fun v a => m.goodAt v.1 a.1 a.2
  objective := fun a => m.goodAt m.base a.1 a.2

end

/-- The named approval account has pointwise the extension of the named
due-actuality account (for instance, the assessor approves exactly the due
actualities). It says nothing about whether either account is correct. -/
def ApprovalCoincidesWithDue {f : Frame} (s : DefinitionSpace f) : Prop :=
  Coextensive s s.approvalAccount s.dueAccount

/-- Weak version of the extensional approval-failure premise: the named
approval account is incorrect, or it coextends with the due-actuality account.
It is what the correct-support elimination needs about approval. -/
def ApprovalFailsOrCoincidesWithDue {f : Frame} (s : DefinitionSpace f) : Prop :=
  ApprovalAccountFails s ∨ ApprovalCoincidesWithDue s

/-! ## Obligation layer (modified divine command theory)

Analyst formulation of a split view: goodness is fixed by natures, obligation by
command. Acts are a separate carrier; `goodAct` is the act-goodness the
commands must respect. No link from act-goodness to aspect goodness is assumed. -/

structure CommandLayer {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s) where
  Act : Type
  goodAct : m.Profile → Act → Prop
  commandsAt : m.Profile → Act → Prop
  obligatoryAt : m.Profile → Act → Prop

section
variable {f : Frame} {s : DefinitionSpace f} {m : ProfileFamily s}

/-- Obligation is constituted by command, and commands are constrained to good
acts, in every profile. -/
def ModifiedCommandTheory (c : CommandLayer m) : Prop :=
  (∀ w a, c.obligatoryAt w a ↔ c.commandsAt w a) ∧ (∀ w a, c.commandsAt w a → c.goodAct w a)

def ActGoodnessInvariant (c : CommandLayer m) : Prop :=
  ∀ v, SameNatures m m.base v → ∀ a, c.goodAct m.base a ↔ c.goodAct v a

def CommandVariesWithNaturesFixed (c : CommandLayer m) : Prop :=
  ∃ v, SameNatures m m.base v ∧ ¬ ∀ a, (c.commandsAt m.base a ↔ c.commandsAt v a)

def ObligationInvariant (c : CommandLayer m) : Prop :=
  ∀ v, SameNatures m m.base v → ∀ a, (c.obligatoryAt m.base a ↔ c.obligatoryAt v a)

end

/-! ## Finite interpretations on the existing knife/counterweight profile -/

/-- The supplied approval account with the assessor approving exactly the due
actualities (the theistic instance "God approves exactly the good"). Due,
feature and other proposals are those of `artifactSpace false`. -/
def exactSpace : DefinitionSpace (artifactWithGood false) where
  Candidate := Proposal
  denotes := fun d x p => match d with
    | .due => artifactGood x p
    | .feature => artifactHas x p
    | .approval => artifactGood x p
    | .other => x = .knife ∧ p = .mass
  admissible := fun d => d ≠ .other
  dueAccount := .due
  featureAccount := .feature
  approvalAccount := .approval
  featureCriterion := fun _ p => artifactHas .knife p
  approves := artifactGood
  dueMeaning := fun _ _ => Iff.rfl
  featureMeaning := fun _ _ => Iff.rfl
  approvalMeaning := fun _ _ => Iff.rfl

/-- Profile `true` gives the knife its edge; profile `false` is the base. -/
def edgedHas (w : Bool) (x : Bearer) (p : Perfection) : Prop :=
  artifactHas x p ∨ (w = true ∧ x = .knife ∧ p = .edge)

def edgedGood (w : Bool) (x : Bearer) (p : Perfection) : Prop :=
  artifactDue (artifactForm x) (artifactEnd (artifactForm x)) p ∧ edgedHas w x p

theorem edgedHas_base (x : Bearer) (p : Perfection) : edgedHas false x p ↔ artifactHas x p :=
  ⟨fun h => h.elim id (fun ⟨h, _⟩ => Bool.noConfusion h), Or.inl⟩

theorem edgedGood_base (x : Bearer) (p : Perfection) : edgedGood false x p ↔ artifactGood x p :=
  ⟨fun ⟨d, h⟩ => ⟨d, (edgedHas_base x p).1 h⟩, fun ⟨d, h⟩ => ⟨d, (edgedHas_base x p).2 h⟩⟩

/-- Divine-instance family: natures vary (the edged knife), goodness is due
actuality in every profile, and the assessor approves exactly the good. -/
def divineFamily : ProfileFamily exactSpace where
  Profile := Bool
  base := false
  hasAt := edgedHas
  goodAt := edgedGood
  approvesAt := edgedGood
  baseHas := edgedHas_base
  baseGood := edgedGood_base
  baseApproves := edgedGood_base

/-- Human-instance family: natures and goodness fixed; the base assessor (the
existing `artifactSpace false` approval) approves only counterweight goods, the
variant approves exactly the good. -/
def humanFamily : ProfileFamily (artifactSpace false) where
  Profile := Bool
  base := false
  hasAt := fun _ => artifactHas
  goodAt := fun _ => artifactGood
  approvesAt := fun w x p => match w with | true => artifactGood x p | false => (x = .counterweight ∧ artifactGood x p)
  baseHas := fun _ _ => Iff.rfl
  baseGood := fun _ _ => Iff.rfl
  baseApproves := fun _ _ => Iff.rfl

/-- Rigidified actual-approval model: the base assessor approves exactly the
good, the nature-fixed variant approves only counterweight goods, and goodness
keeps its base extension in both profiles. -/
def coincidentFamily : ProfileFamily exactSpace where
  Profile := Bool
  base := false
  hasAt := fun _ => artifactHas
  goodAt := fun _ => artifactGood
  approvesAt := fun w x p => match w with | true => (x = .counterweight ∧ artifactGood x p) | false => artifactGood x p
  baseHas := fun _ _ => Iff.rfl
  baseGood := fun _ _ => Iff.rfl
  baseApproves := fun _ _ => Iff.rfl

/-- Voluntarist family: goodness follows the assessor's approval, which varies
while natures stay fixed. -/
def voluntaristFamily : ProfileFamily exactSpace where
  Profile := Bool
  base := false
  hasAt := fun _ => artifactHas
  goodAt := fun w x p => match w with | true => (x = .counterweight ∧ artifactGood x p) | false => artifactGood x p
  approvesAt := fun w x p => match w with | true => (x = .counterweight ∧ artifactGood x p) | false => artifactGood x p
  baseHas := fun _ _ => Iff.rfl
  baseGood := fun _ _ => Iff.rfl
  baseApproves := fun _ _ => Iff.rfl

/-- Two acts: `keep` (keep a promise, good in every profile) and `rite` (a
ceremonial act, also good). Commands differ only on the ceremonial act. -/
inductive Deed | keep | rite deriving DecidableEq

/-- Modified command layer over the divine family's nature-fixed copy: the base
commands both acts, the variant only `keep`. -/
def adamsFamily : ProfileFamily exactSpace where
  Profile := Bool
  base := false
  hasAt := fun _ => artifactHas
  goodAt := fun _ => artifactGood
  approvesAt := fun _ => artifactGood
  baseHas := fun _ _ => Iff.rfl
  baseGood := fun _ _ => Iff.rfl
  baseApproves := fun _ _ => Iff.rfl

def adamsLayer : CommandLayer adamsFamily where
  Act := Deed
  goodAct := fun _ _ => True
  commandsAt := fun w a => match w with | true => a = .keep | false => True
  obligatoryAt := fun w a => match w with | true => a = .keep | false => True

/-- Formal controls for the modal approval test. General conjuncts: the robust
nature account entails supervenience; weak invariance is stable truth of every
aspect over the nature-fixed profiles; under approval as ground, invariance is
equivalent to approvals fixed by natures; the modified command theory with command
variation loses obligation invariance. Finite conjuncts: the divine joint model
(due account, supervenience, approval-as-ground, approvals fixed by natures, the
extensional approval account correct, the weak premise and the due thesis
true); the human instance (all Euthyphro premises, approval fails); omission of
the transfer bridge (the rigidified actual-approval model: invariance and
variation hold, approval does not ground, the base approval account is correct);
the rigidified account excludes the transfer bridge in general; omission of invariance
(voluntarist: variation and ground hold); and the modified command model
(goodness facts fixed, approval grounds, commands and obligations vary). These
are formal interpretations, not metaphysical possibility claims. -/
def Controls : Prop :=
  (∀ {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s),
      RobustDueAccount m → GoodnessSupervenes m) ∧
  (∀ {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s),
      GoodnessInvariantUnderApprovalVariation m ↔
        ∀ a, ObjectiveTruthDefinitionFork.Stable (natureFixedTruthFrame m) a) ∧
  (∀ {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s),
      ApprovalGroundsAcrossNatureFixed m → GroundedInvarianceNeedsNatureFixedApproval m) ∧
  (∀ {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s),
      RigidifiedApprovalAccount m → ¬ ApprovalCorrectnessTransfers m) ∧
  (∀ {f : Frame} {s : DefinitionSpace f} {m : ProfileFamily s} (c : CommandLayer m),
      ModifiedCommandTheory c → CommandVariesWithNaturesFixed c → ¬ ObligationInvariant c) ∧
  (RobustDueAccount divineFamily ∧ GoodnessSupervenes divineFamily ∧
    ApprovalGroundsAcrossNatureFixed divineFamily ∧ ApprovalsFixedByNatures divineFamily ∧
    ¬ ApprovalVariesWithNaturesFixed divineFamily ∧
    ¬ ApprovalAccountFails exactSpace ∧ ApprovalCoincidesWithDue exactSpace ∧
    ApprovalFailsOrCoincidesWithDue exactSpace ∧
    CorrectAccountSupport exactSpace ∧ CorrectAccountExists exactSpace ∧
    FeatureAccountFails exactSpace ∧ DueActualityThesis (artifactWithGood false)) ∧
  (GoodnessInvariantUnderApprovalVariation humanFamily ∧
    ApprovalVariesWithNaturesFixed humanFamily ∧ ApprovalCorrectnessTransfers humanFamily ∧
    ApprovalDoesNotGround humanFamily ∧ ApprovalAccountFails (artifactSpace false) ∧
    ¬ ApprovalCoincidesWithDue (artifactSpace false)) ∧
  (GoodnessInvariantUnderApprovalVariation coincidentFamily ∧
    ApprovalVariesWithNaturesFixed coincidentFamily ∧ ApprovalDoesNotGround coincidentFamily ∧
    ¬ ApprovalCorrectnessTransfers coincidentFamily ∧ ¬ ApprovalAccountFails exactSpace ∧
    RigidifiedApprovalAccount coincidentFamily) ∧
  (ApprovalVariesWithNaturesFixed voluntaristFamily ∧
    ApprovalGroundsAcrossNatureFixed voluntaristFamily ∧
    ¬ GoodnessInvariantUnderApprovalVariation voluntaristFamily) ∧
  (ModifiedCommandTheory adamsLayer ∧ ActGoodnessInvariant adamsLayer ∧
    GoodnessSupervenes adamsFamily ∧ ApprovalGroundsAcrossNatureFixed adamsFamily ∧
    CommandVariesWithNaturesFixed adamsLayer ∧ ¬ ObligationInvariant adamsLayer)

end TruthCore.Ethics.Euthyphro
