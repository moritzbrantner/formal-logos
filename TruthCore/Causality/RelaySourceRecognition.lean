module

public import TruthCore.Causality.EssentialPower
public import TruthCore.Logic.CorrectionCriterion

/-! The same present activity of a selected recipient can have an intrinsic
feed or a feed supplied by another ray. The intervention set probes the primary
successor links and can be extended to probe the entrance from the auxiliary
ray into the feed. -/

@[expose] public section
namespace TruthCore.Causality.RelaySourceRecognition

open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion)

/-- Primary zero is the recipient. The token placed at depth `d` is distinct
from the primary stage it feeds, including when `d = 0`. -/
inductive Stage where
  | primary (position : Nat)
  | feed
  | auxiliary (position : Nat)

/-- Only the feed token has intrinsic power in the sourced world. -/
def intrinsic (sourced : Bool) : Stage → Prop
  | .feed => sourced = true
  | .primary _ => False
  | .auxiliary _ => False

/-- The primary and auxiliary rays run from successors to predecessors.
The feed itself supplies primary stage `d`. Only the borrowed world has
an auxiliary entrance into the feed. A primary cut names one recipient
index. The entrance switch deletes only the auxiliary-to-feed link. -/
def link (d : Nat) (sourced entranceIntact : Bool) (cut : Option Nat) :
    Stage → Stage → Prop
  | .primary y, .primary x => y = x + 1 ∧ cut ≠ some x
  | .feed, .primary x => x = d
  | .auxiliary y, .auxiliary x => y = x + 1
  | .auxiliary y, .feed => y = 0 ∧ sourced = false ∧ entranceIntact = true
  | .primary _, .feed => False
  | .primary _, .auxiliary _ => False
  | .feed, .feed => False
  | .feed, .auxiliary _ => False
  | .auxiliary _, .primary _ => False

/-- The primary segment from position `n` up to the feed is unbroken. -/
def ReachesFeed (d : Nat) (cut : Option Nat) (n : Nat) : Prop :=
  n ≤ d ∧ ∀ i, n ≤ i → i < d → cut ≠ some i

/-- The source or entrance can keep the feed active. On the primary ray
the active stages are those at or below `d` with an intact route from it.
The auxiliary ray remains active in the borrowed world under every tested
intervention, including deletion of its link into the feed. -/
def active (d : Nat) (sourced entranceIntact : Bool) (cut : Option Nat) :
    Stage → Prop
  | .primary n => (sourced || entranceIntact) = true ∧ ReachesFeed d cut n
  | .feed => (sourced || entranceIntact) = true
  | .auxiliary _ => sourced = false

/-- The full record includes the uncut baseline and every single primary
cut, leaving the auxiliary entrance alone. -/
def primaryRecord (d : Nat) (sourced : Bool) (cut : Option Nat) : Prop :=
  active d sourced true cut (.primary 0)

/-- Actual transmission in an intervention requires both a retained edge
and an active supplier. -/
def transmits (d : Nat) (sourced entranceIntact : Bool) (cut : Option Nat)
    (supplier recipient : Stage) : Prop :=
  link d sourced entranceIntact cut supplier recipient ∧
    active d sourced entranceIntact cut supplier

/-- A profile obeys the local law if each active stage has either intrinsic
power or an active supplier through a retained link, and vice versa. -/
def LocalActivity (d : Nat) (sourced entranceIntact : Bool) (cut : Option Nat)
    (profile : Stage → Prop) : Prop :=
  ∀ x, profile x ↔ intrinsic sourced x ∨ ∃ y, link d sourced entranceIntact cut y x ∧ profile y

/-- The selected profiles obey the local law in both worlds and the full
source-free transmission rule in the borrowed world. Both worlds have actual delivery along the
primary path from the same specified feed. Their primary intervention records
agree while the feed's intrinsic status differs, precluding identification
from the record. The auxiliary-only cut distinguishes the selected responses.
With the primary incoming link at `d` also cut, every compatible response
at the recipient gives the feed's intrinsic status. -/
def PrimaryCutSourceComparison : Prop :=
  ∀ d,
    (∀ sourced entranceIntact cut,
      LocalActivity d sourced entranceIntact cut (active d sourced entranceIntact cut)) ∧
    (∀ entranceIntact cut,
      PowerTransmissionRule (link d false entranceIntact cut)
        (active d false entranceIntact cut)) ∧
    (∀ sourced,
      primaryRecord d sourced none ∧
      transmits d sourced true none .feed (.primary d) ∧
      FiniteCausalPath (transmits d sourced true none) (.primary 0) .feed) ∧
    (∀ sourced supplier, link d sourced true none supplier .feed ↔
      supplier = .auxiliary 0 ∧ sourced = false) ∧
    transmits d false true none (.auxiliary 0) .feed ∧
    intrinsic true .feed ∧ (∀ x, ¬ intrinsic false x) ∧
    FinitelyGroundedPower (transmits d true true none) (intrinsic true) (.primary 0) ∧
    ¬ FinitelyGroundedPower (transmits d false true none) (intrinsic false) (.primary 0) ∧
    primaryRecord d true = primaryRecord d false ∧
    (∀ sourced i, primaryRecord d sourced (some i) ↔ d ≤ i) ∧
    ¬ AdmitsCriterion (primaryRecord d) (fun sourced => intrinsic sourced .feed) ∧
    (∀ sourced, active d sourced false none (.primary 0) ↔ intrinsic sourced .feed) ∧
    (∀ sourced entranceIntact profile, LocalActivity d sourced entranceIntact (some d) profile →
      (profile (.primary 0) ↔ profile .feed)) ∧
    (∀ sourced profile, LocalActivity d sourced false (some d) profile →
      (profile (.primary 0) ↔ intrinsic sourced .feed))

end TruthCore.Causality.RelaySourceRecognition
