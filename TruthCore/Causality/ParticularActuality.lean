module

public import TruthCore.Causality.DerivativeJointPower
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Case.Catholicism.CausalPerfectionTransfer

/-! Analyst reconstruction at a fixed exercise context. An index `event x r`
locates the realization under test. Its membership in a type says nothing about
supply, subsistence, identity with an esse, or attribution of a causal edge.
The proposed use of #734 productive Supply for constitutive inputs, and the
adequacy of the admitted records for a real occurrence, are interpretation
premises. A cut changes the selected records, not the space of possible worlds. -/

@[expose] public section

namespace TruthCore.Causality.ParticularActuality

open TruthCore.Causality.JointGroups (Groups)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionsAreModesOfBeing)
open TruthCore.Case.Catholicism

variable {B R E G : Type}

/-- Remove specified productive alternatives, preserving the intrinsic basis
and every retained group's contributors, enablers and effect. -/
def restrict (h : Groups E G) (keep : G → Prop) : Groups E G :=
  { h with admitted := fun g => h.admitted g ∧ keep g }

/-- Sufficient local interface for a selected class of modes. Each has a
positive original realization, lacks an independent seed, and every admitted
last group for it includes the same bearer's esse as a contributor. Indirect
routes can support the weaker cut condition without satisfying this interface.
The selected class and ModeOfBeing interpretation remain explicit. -/
def ModeUsesBearer (h : Groups E G) (I : E → Prop) (event : B → R → E)
    (esse : R) (selected mode : B → R → Prop) : Prop :=
  ∀ x r, selected x r → mode x r →
    Supply h I (event x r) ∧ ¬ I (event x r) ∧
    ∀ g, h.admitted g → h.effect g = event x r → event x esse ∈ h.contributors g

/-- Each selected actual respect has positive original supply and loses supply
under every record restriction that deprives its bearer of esse supply. Which
restrictions do this, and which causal agent owns a withdrawn contribution,
are independent questions. No `CausesIn` edge is included. -/
def InheritsEsseCuts (h : Groups E G) (I : E → Prop) (event : B → R → E)
    (esse : R) (selected InAct : B → R → Prop) : Prop :=
  ∀ x r, selected x r → InAct x r →
    Supply h I (event x r) ∧ ∀ keep,
      ¬ Supply (restrict h keep) I (event x esse) → ¬ Supply (restrict h keep) I (event x r)

/-- A sufficient mediated interface. For each selected mode there is a region
containing its realization. An intrinsic member of the region must be the
bearer's esse. Each admitted group ending inside either yields the bearer's
esse or takes a contributor from inside. Different records can use different
intermediates. Supply induction then follows an actual branch to the bearer.
The conclusion about cut sensitivity alone does not recover this region. -/
def ModeThroughBearer (h : Groups E G) (I : E → Prop) (event : B → R → E)
    (esse : R) (selected mode : B → R → Prop) : Prop :=
  ∀ x r, selected x r → mode x r →
    Supply h I (event x r) ∧ ∃ region : Set E, event x r ∈ region ∧
      (∀ e ∈ region, I e → e = event x esse) ∧
      ∀ g, h.admitted g → h.effect g ∈ region →
        h.effect g = event x esse ∨ ∃ e ∈ h.contributors g, e ∈ region

/-- Exact test for the all-record-restrictions diagnostic in this model.
If a selected actual's bearer-esse is not intrinsic, delete every record
producing that same esse. Non-supply of the mode after this one deletion,
together with original supply, is equivalent to inheritance of every esse
cut. Independent deletion of records is a modeling assumption. -/
def SingleDeletionTest : Prop :=
  ∀ (B R E G : Type) (h : Groups E G) (I : E → Prop) (event : B → R → E)
    (esse : R) (selected InAct : B → R → Prop),
    (∀ x r, selected x r → InAct x r → ¬ I (event x esse)) →
    (InheritsEsseCuts h I event esse selected InAct ↔
      ∀ x r, selected x r → InAct x r →
        Supply h I (event x r) ∧
        ¬ Supply (restrict h (fun g => h.effect g ≠ event x esse)) I (event x r))

namespace Control

abbrev Event := TransferRole × Bool

def event (x : TransferRole) (r : Bool) : Event := (x, r)

def intrinsic (e : Event) : Prop := e = (.source, false)

/-- A giving record for each distinct bearer's esse and a realization record
for the skill of each role. The secondary producer's esse contributes to each
skill record. The switch changes the target bearer's esse from contributor to
enabler, leaving all record effects and combined memberships fixed. The sole
intrinsic seed is the source's esse. The records schematize contribution,
without identifying membership with effective causal responsibility. -/
def records (joint : Bool) : Groups Event Event where
  contributors := fun g e => if g.2 then
    e = (.producer, false) ∨ (joint = true ∧ e = (g.1, false))
    else e = (.source, false)
  enablers := fun g e => g.2 = true ∧ joint = false ∧ e = (g.1, false)
  effect := id
  admitted := fun g => g ≠ (.source, false)

def selected (_ : TransferRole) (r : Bool) : Prop := r = true

/-- Disable only this recipient's record at the named respect. The source
continues to supply the producer's esse in both comparisons. -/
def elsewhere (respect : Bool) (g : Event) : Prop := g ≠ (.recipient, respect)

/-- The two classifications are extensionally identical in this test.
All four bearers have both respects. The joint formulation inherits every
esse cut yet the existing secondary-only causal assignment fails universal
transfer. Withdrawal of the recipient's own esse record distinguishes joint
contribution from enabling. Withdrawal of its skill record spares its esse. -/
def Certificate : Prop :=
  SecondaryOnlyTransferSurvives ∧ PerfectionsAreModesOfBeing transferAct transferAct ∧
  ModeUsesBearer (records true) intrinsic event false selected transferAct ∧
  InheritsEsseCuts (records true) intrinsic event false selected transferAct ∧
  (∀ x r, Supply (records false) intrinsic (event x r)) ∧
  ¬ Supply (restrict (records true) (elsewhere false)) intrinsic (event .recipient false) ∧
  ¬ Supply (restrict (records true) (elsewhere false)) intrinsic (event .recipient true) ∧
  ¬ Supply (restrict (records false) (elsewhere false)) intrinsic (event .recipient false) ∧
  Supply (restrict (records false) (elsewhere false)) intrinsic (event .recipient true) ∧
  Supply (restrict (records true) (elsewhere true)) intrinsic (event .recipient false) ∧
  ¬ Supply (restrict (records true) (elsewhere true)) intrinsic (event .recipient true)

end Control
end TruthCore.Causality.ParticularActuality
