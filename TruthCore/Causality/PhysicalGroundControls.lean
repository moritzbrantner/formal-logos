module

public import Mathlib.Data.Fintype.Basic

/-! Bounded comparisons for a claim-specific response rule and for wisdom
compatibility and articulation. These tables stipulate their interpretations. -/

@[expose] public section
namespace TruthCore.Causality.PhysicalGroundControls

namespace ConsentResponse

inductive Consent where
  | absent | bystander | claimant
  deriving DecidableEq

def roster : List Consent := [.absent, .bystander, .claimant]

def duty (harm : Bool) (consent : Consent) : Bool := harm && consent != .claimant

def reasonRoute (cue : Bool) (report : Consent) (wantsProceed : Bool) : Bool × Bool :=
  let conclusion := duty cue report
  (conclusion, !conclusion && wantsProceed)

def bypass (cue : Bool) (report : Consent) (wantsProceed : Bool) : Bool :=
  wantsProceed && (!cue || report == .claimant)

def benefitOnly (cue wantsProceed : Bool) : Bool := wantsProceed && !cue

structure Case where
  harm : Bool
  consent : Consent
  cue : Bool
  report : Consent
  wantsProceed : Bool

def cases : List Case :=
  [false, true].flatMap fun harm => roster.flatMap fun consent =>
    [false, true].flatMap fun cue => roster.flatMap fun report =>
      [false, true].map fun wants => ⟨harm, consent, cue, report, wants⟩

def accurate (c : Case) : Bool := c.harm == c.cue && c.consent == c.report
def actualDuty (c : Case) : Bool := duty c.harm c.consent
def response (c : Case) : Bool × Bool := reasonRoute c.cue c.report c.wantsProceed

theorem census :
    cases.length = 72 ∧ (cases.filter accurate).length = 12 ∧
    (cases.filter fun c => actualDuty c != (response c).1).length = 32 ∧
    (cases.filter fun c => (response c).2 != benefitOnly c.cue c.wantsProceed).length = 6 ∧
    (∀ c ∈ cases, (response c).2 = bypass c.cue c.report c.wantsProceed) ∧
    (∀ c ∈ cases, accurate c = true →
      (response c).1 = actualDuty c ∧ !(actualDuty c && (response c).2)) := by
  decide +kernel

theorem selectedRows :
    reasonRoute true .claimant true = (false, true) ∧
    reasonRoute true .bystander true = (true, false) ∧
    reasonRoute true .bystander false = (true, false) ∧
    reasonRoute false .bystander true = (false, true) := by
  decide +kernel

end ConsentResponse

namespace Wisdom

abbrev Profile := Nat

def wisdom : Profile := 4
def profiles : List Profile := List.range 8
def subset (a b : Profile) : Bool := a &&& b == a
def wise (a : Profile) : Bool := a.testBit 2

def maximal (family : List Profile) (b : Profile) : Bool :=
  !(family.any fun t => t != b && subset b t)

def extendible (family : List Profile) (b : Profile) : Bool :=
  family.any fun t => subset (b ||| wisdom) t

def elsewhere (family : List Profile) : Bool := family.any wise

def families : List (List Profile) :=
  (List.range 255).map fun mask => profiles.filter (Nat.testBit (mask + 1))

def cases : List (List Profile × Profile) :=
  families.flatMap fun family => family.map (family, ·)

set_option maxRecDepth 4096 in
theorem census :
    cases.length = 1024 ∧
    (cases.filter fun (f, b) => maximal f b).length = 369 ∧
    (cases.filter fun (f, b) => !wise b && extendible f b).length = 376 ∧
    (cases.filter fun (f, b) =>
      !wise b && maximal f b && elsewhere f && !extendible f b).length = 80 ∧
    cases.all (fun (f, b) => !(maximal f b && extendible f b) || wise b) = true := by
  decide +kernel

abbrev Probe := Bool × Bool

def probes : List Probe := [(false, false), (true, false), (false, true), (true, true)]

def content (probe : Probe) (composition : Bool) : Bool :=
  if composition then !probe.2 else !probe.1

structure Apprehension where
  index : Bool
  truth : Bool
  subject : Unit
  object : Unit
  form : Unit
  operation : Unit
  realizer : Unit
  deriving DecidableEq

def actual : Probe := (false, false)
def constituents : List Unit := [()]
def aware : List Apprehension :=
  [false, true].map fun i => ⟨i, content actual i, (), (), (), (), ()⟩

theorem articulation :
    probes.map (fun p => (content p false, content p true)) =
      [(true, true), (false, true), (true, false), (false, false)] ∧
    (∃ p ∈ probes, content p false ≠ content p true) ∧
    aware.length = 2 ∧ (aware.map Apprehension.realizer).eraseDups.length = 1 ∧
    constituents.length = 1 ∧
    (∀ row ∈ aware, row.truth ∧ row.subject = row.object ∧ row.object = row.form ∧
      row.form = row.operation) := by
  decide +kernel

end Wisdom

end TruthCore.Causality.PhysicalGroundControls
