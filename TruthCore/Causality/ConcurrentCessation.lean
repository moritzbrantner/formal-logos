module

public import TruthCore.Causality.ConcurrentActualization
public import TruthCore.Causality.ProtectiveProcess
public import TruthCore.Causality.FrameAdapters

/-! A scoped test of the cessation argument at concurrent actualization.
The existing process dictionary supplies actual terminal occurrences and bearer
identity. The causal coverage law below is a hypothesis, not a definition of
real causation. Natural-number sampling does not cover dense-time limits or
first appearances. No productive interpretation is inferred from a loss table.
-/

@[expose] public section

namespace TruthCore.Causality.ConcurrentCessation
open TruthCore.Causality.ProtectiveProcess
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Modal.TemporalHistory

/-- The cessation instance of a causal principle: every sampled loss of an
existing bearer has a terminal process occurrence directed to that SAME bearer.
This OPEN coverage claim does not identify failure of giving with a process. -/
def CessationHasCause {B F : Type} (m : Model B F Nat) : Prop :=
  ∀ x n, m.existsAt n x → ¬ m.existsAt (n+1) x →
    ∃ p, Destroys m p n (n+1) x

/-- Restore the intended meaning of terminal destruction in the controls:
every declared destruction really loses a previously existing bearer. -/
def DestructionSound {B F : Type} (m : Model B F Nat) : Prop :=
  ∀ p n x, Destroys m p n (n+1) x →
    m.existsAt n x ∧ ¬ m.existsAt (n+1) x

def NoCessationCause {B F : Type} (m : Model B F Nat) (x : B) (n : Nat) : Prop :=
  ∀ p, ¬ Destroys m p n (n+1) x

/-- Weak giving, restricted to continuation over an immediately previous
sample. The giver may vary, be the recipient, or be unrelated to an originator.
No claim about births, time zero or dense-time limit points is included. -/
def ContinuedGiving {B F P : Type} (m : Model B F Nat)
    (G : BeingGiving Unit B Nat) (received : B → P → Prop) : Prop :=
  ∀ x n z, received x z → m.existsAt n x → m.existsAt (n+1) x →
    ∃ g, G.GivesAt () g x (n+1)

/-- The proposed no-giver/no-continuation premise. It concerns absence of ALL
givers, not withdrawal of one identified original cause. Its dependence content
is explicit; equivalence below is a diagnostic, not independent warrant. -/
def UngivenContinuationFails {B F P : Type} (m : Model B F Nat)
    (G : BeingGiving Unit B Nat) (received : B → P → Prop) : Prop :=
  ∀ x n z, received x z → m.existsAt n x →
    (¬ ∃ g, G.GivesAt () g x (n+1)) → ¬ m.existsAt (n+1) x

def Consequences : Prop := ∀ (B F P : Type) (m : Model B F Nat)
    (G : BeingGiving Unit B Nat) (received : B → P → Prop),
  (∀ x n, CessationHasCause m → m.existsAt n x →
    NoCessationCause m x n → ¬¬ m.existsAt (n+1) x) ∧
  (ContinuedGiving m G received ↔ UngivenContinuationFails m G received) ∧
  (CessationHasCause m → UngivenContinuationFails m G received →
    ∀ x n z, received x z → m.existsAt n x →
      (¬ ∃ g, G.GivesAt () g x (n+1)) → ∃ p, Destroys m p n (n+1) x)

/-- Apply the ACTUAL root-route premise at the same world, bearer and time.
The process existence dictionary must match temporal presence; the Unit giving
profile is only the restriction to the supplied world, not a world/time swap. -/
def ConsumerRestriction : Prop := ∀ (W B F P : Type) (h : History W B Nat)
    (G : BeingGiving W B Nat) (received : B → P → Prop) (v : W)
    (m : Model B F Nat),
  (∀ t x, m.existsAt t x ↔ h.IsAt v x t) →
  ConcurrentlyActualized h G received →
  ContinuedGiving m ⟨fun _ c x t => G.GivesAt v c x t⟩ received

namespace Control
open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control

/-- Reuse the existing inertia history. Its source true ceases at sample 2;
one represented process witnesses that real sampled loss, so causal coverage
is not tested solely on a loss-free population. False remains the recipient. -/
def inertialProcesses : Model Bool Unit Nat where
  threat := fun _ => ⟨false, true⟩
  occurs := fun _ s t => s = 1 ∧ t = 2
  terminal := fun _ t => t = 2
  existsAt := fun t x => inertia.IsAt () x t

/-- Reuse the existing sustained history, with no destructive processes. -/
def sustainedProcesses : Model Bool Unit Nat where
  threat := fun _ => ⟨false, true⟩
  occurs := fun _ _ _ => False
  terminal := fun _ _ => False
  existsAt := fun t x => sustained.IsAt () x t

def Controls : Prop :=
  (CessationHasCause inertialProcesses ∧ DestructionSound inertialProcesses ∧
    Destroys inertialProcesses () 1 2 true ∧
    falseReceived false () ∧ inertialProcesses.existsAt 1 false ∧
    inertialProcesses.existsAt 2 false ∧ NoCessationCause inertialProcesses false 1 ∧
    (¬ ∃ g, inertiaGiving.GivesAt () g false 2) ∧
    ¬ ContinuedGiving inertialProcesses inertiaGiving falseReceived ∧
    ¬ ConcurrentlyActualized inertia inertiaGiving falseReceived) ∧
  (CessationHasCause sustainedProcesses ∧ DestructionSound sustainedProcesses ∧
    ContinuedGiving sustainedProcesses sustainedGiving falseReceived ∧
    UngivenContinuationFails sustainedProcesses sustainedGiving falseReceived ∧
    ConcurrentlyActualized sustained sustainedGiving falseReceived)
end Control

/-- Conditional schema and populated controls about existing dictionaries.
Neither causal coverage nor a no-giving dependency is asserted of reality. -/
def Certificate : Prop := Consequences ∧ ConsumerRestriction ∧ Control.Controls


/-!
## C3 at one actual world: an originating cause can remain actual but inactive

This control strengthens the earlier one-world inertia assignment: a *single*
rigid bearer has the same temporal presence and world-existence interpretation,
both concrete relata exist at the selected actual world, and the effect is
modally contingent (both candidates are absent in the alternative world).
The source remains present after its originating action. The same actual
grounding profile can be tested with and without a ground edge.

The control is about typed models, not an attribution or proof that the
assignments are metaphysically possible. The positive persistence rule is
conditional on earlier existence; it says nothing about why the bearer was
actual at any time. In particular `ActualConcreteGround` does not identify
grounding with concurrent productive `GivesAt`.
-/

namespace C3ActualWorld

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.SustainingCausation.Control (trueCausesFalse)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

/-- The source is present throughout the actual history; the effect first
appears at time 1 and continues. Both are absent in the other possible world.
The `Ontic.ExistsAt` field agrees with presence at `now = 2` in *both* worlds. -/
def history : History Bool Bool Nat where
  ontic :=
    { frame := ⟨fun _ _ => True⟩
      ExistsAt := fun v _ => v = true
      Causes := fun _ _ _ => False }
  IsAt := fun v x t => v = true ∧ (x = true ∨ (x = false ∧ 1 ≤ t))
  now := 2

/-- Only an originating exercise occurs, at the effect's first moment. -/
def originGiving : BeingGiving Bool Bool Nat :=
  ⟨fun v c x t => v = true ∧ c = true ∧ x = false ∧ t = 1⟩

/-- Otherwise identical history, with giving extended to every effect moment. -/
def sustainedGiving : BeingGiving Bool Bool Nat :=
  ⟨fun v c x t => v = true ∧ c = true ∧ x = false ∧ 1 ≤ t⟩

/-- The same shared causal vocabulary for both giving profiles. The frame
fields this control does not use (`MovesIn`, `DependsForBeing`, `PriorSimply`)
are left empty. In particular `DependsForBeing := fun _ _ => False` does not
model q.44 dependence for being (`2068f91c`); it is an unused placeholder, and
no conjunct of `Certificate` reads it. -/
def frame (G : BeingGiving Bool Bool Nat) : CausalityFrame Bool Bool Nat Unit where
  history := history
  GivesAt := G.GivesAt
  CausesIn := trueCausesFalse
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := ()

def originFrame : CausalityFrame Bool Bool Nat Unit := frame originGiving
def sustainedFrame : CausalityFrame Bool Bool Nat Unit := frame sustainedGiving

/-- The source counts as an actual concrete ground in the reading world.
That assignment by itself says nothing about *present productive exercise*.
On the complete-history (ancestry) reading of `grounds w` that the `cb1cdea9`
record's note allows, an inertialist can accept this edge. On a
present-existential-grounding reading, this profile instead witnesses ground
without giving, which is not the inertialist's own position. -/
def withGround : Profile Bool Bool where
  ontic := history.ontic
  concrete := fun _ => True
  grounds := fun v c x => v = true ∧ c = true ∧ x = false

/-- A rival profile on the identical history, with the identical causes and
actual bearers but no selected actual-concrete grounding edge. -/
def withoutGround : Profile Bool Bool :=
  { withGround with grounds := fun _ _ _ => False }

/-- A positive one-step persistence constraint. Unlike a creation law, it
requires an already present bearer as antecedent and provides no existential
initial condition or present productive cause. -/
def StepPersistence (h : History Bool Bool Nat) : Prop :=
  ∀ v x n, h.IsAt v x n → h.IsAt v x (n+1)

/-- Joint finite-world and unbounded-time controls. The grounded inertial
interpretation satisfies the `cb1cdea9` *formal* cause-to-ground bridge while
failing C3; the ungrounded inertial interpretation defeats that bridge even
though the originating source is actual. Either assignment of the free
`grounds` primitive is compatible with origin-only giving, so applying the
root route to persistence needs an explicit ground-to-giving bridge.
Neither profile has a necessary actual bearer (both share `ontic`).
No C1/C2 premise or God-existence conclusion is established here. -/
def Certificate : Prop :=
  CoherentAtNow history ∧
  StepPersistence history ∧
  ActualConcrete withGround true true ∧
  ActualConcrete withGround true false ∧
  ContingentAt history.ontic true false ∧
  (∀ x, ActualConcrete withGround true x → ContingentAt history.ontic true x) ∧
  ¬ NecessaryConcreteAt withGround true ∧
  ¬ NecessaryConcreteAt withoutGround true ∧
  originFrame.CausesIn true false originFrame.esse ∧
  OriginatesBeing history originGiving true true false ∧
  GiverPresentWhenGiving history originGiving ∧
  (∀ v x t, ¬ originGiving.GivesAt v x x t) ∧
  EsseCauseIsActualConcreteGround withGround true originFrame.CausesIn originFrame.esse ∧
  ¬ ConcurrentlyActualized history originGiving falseReceived ∧
  ¬ CausingAnothersBeingIsSustaining history originGiving originFrame.CausesIn originFrame.esse ∧
  ¬ EsseCauseIsActualConcreteGround withoutGround true originFrame.CausesIn originFrame.esse ∧
  ConcurrentlyActualized history sustainedGiving falseReceived ∧
  CausingAnothersBeingIsSustaining history sustainedGiving sustainedFrame.CausesIn sustainedFrame.esse ∧
  GiverPresentWhenGiving history sustainedGiving

end C3ActualWorld


/-!
## ¬C3 withdrawal comparison (#1801)

Four structural alternative histories keep the same rigid originator. Three
share the effect's complete onset history through t=1, and two share its entire
presence history while differing in productive esse-giving at t=2.

The candidate law is the already defined `CessationHasCause`: every genuine
loss of an existing bearer has a positive represented destructive process.
There are NO such processes in these histories. This is the strongest
no-change reading's proposed causal coverage law, not an independently
established law of received esse. The candidate law can be true in worlds
with and without the effect and remains true under removal of a present giver.
The fourth history makes the effect disappear without a positive destructive
process; it must be excluded by the law, or the withdrawal must count as a
relevant loss-inducing condition. Merely labeling a history "admitted" would
not establish the law's metaphysical applicability.

See `docs/notes/law-actuality-743.md` and issue #1801. None of these
stipulated histories is certified as metaphysically accessible.
-/
namespace WithdrawalLaw

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.SustainingCausation.Control (trueCausesFalse)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)

/-- The effect receives esse at onset in three scenarios. `conserved`
continues giving, `inertial` does not, `absent` never has the effect, and
`vanished` loses it immediately after onset without a destructive process. -/
inductive Scenario where
  | conserved | inertial | absent | vanished
  deriving DecidableEq, Repr

/-- One rigid effect's actual temporal presence, not changing a state-value
bearer into a numerically different individual. -/
def effectAt : Scenario → Nat → Prop
  | .conserved, t => 1 ≤ t
  | .inertial, t => 1 ≤ t
  | .absent, _ => False
  | .vanished, t => t = 1

/-- The designated source (`true`) is present at every moment in every
scenario. The recipient (`false`) is present according to `effectAt`.
Existence at the selected time matches each world, including the vanished
world. An accessible world with no recipient is still populated by the source. -/
def history : History Scenario Bool Nat where
  ontic :=
    { frame := ⟨fun _ _ => True⟩
      ExistsAt := fun v x => x = true ∨ (x = false ∧ effectAt v 2)
      Causes := fun _ _ _ => False }
  IsAt := fun v x t => x = true ∨ (x = false ∧ effectAt v t)
  now := 2

/-- Exactly the same origin at t=1 in the three originating histories.
Only the `conserved` scenario has a strict giver after that; the cause remains
present even if the activity stops. Absence from `GivesAt` is NOT encoded as a
destructive occurrence. -/
def giving : BeingGiving Scenario Bool Nat :=
  ⟨fun v c x t => c = true ∧ x = false ∧
    ((t = 1 ∧ v ≠ .absent) ∨ (v = .conserved ∧ 1 ≤ t))⟩

/-- Same shared causality dictionary. Other causal roles are irrelevant and
unconstrained in this test; their empty assignments are not a q.44
`DependsForBeing` interpretation. -/
def frame : CausalityFrame Scenario Bool Nat Unit where
  history := history
  GivesAt := giving.GivesAt
  CausesIn := trueCausesFalse
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := fun _ _ => False
  esse := ()

/-- Causal coverage without a represented positive destruction. This `Model`
does not posit the absence of all metaphysically relevant loss conditions;
in particular withdrawal of a conserver is not itself a declared process. -/
def noDestruction (v : Scenario) : Model Bool Unit Nat where
  threat := fun _ => ⟨false, true⟩
  occurs := fun _ _ _ => False
  terminal := fun _ _ => False
  existsAt := fun t x => history.IsAt v x t

/-- Counter-reading: treat the very cessation of active conservation between
t=1 and t=2 as a loss-inducing occurrence for the same recipient. The originator
itself remains present. The `occurs` field is an analyst classification, NOT
an independently established positive destructive process; this is exactly
what the inertialist disputes. World and bearer presence are unchanged. -/
def withdrawalAsLoss : Model Bool Unit Nat where
  threat := fun _ => ⟨false, true⟩
  occurs := fun _ s t => s = 1 ∧ t = 2
  terminal := fun _ t => t = 2
  existsAt := fun t x => history.IsAt .vanished x t

/-- Candidate no-change governing principle for the same bearer and positive
destructive-process vocabulary. It is the existing `CessationHasCause`,
instantiated, not a newly defined explanation ontology. -/
def CoverageLaw (v : Scenario) : Prop :=
  CessationHasCause (noDestruction v)

/-- Same substantial beings and origin exercises at all sample times through
and including t=1. This excludes switching identities or onset data when
evaluating later withdrawal. -/
def SameOnset (v w : Scenario) : Prop :=
  (∀ x t, t ≤ 1 → (history.IsAt v x t ↔ history.IsAt w x t)) ∧
  (∀ c x t, t ≤ 1 → (giving.GivesAt v c x t ↔ giving.GivesAt w c x t))

/-- The exact selected-world instance of the already existing weak received-
esse concurrent actualization premise. Unlike `ConcurrentlyActualized`, it
does not quantify over all scenarios. -/
def ConcurrentAt (v : Scenario) : Prop :=
  ∀ x t z, falseReceived x z → history.IsAt v x t →
    ∃ c, frame.GivesAt v c x t

/-- A model comparison rather than a general metaphysical theory. The
`vanished` history has an actual source and an actual originated effect at
t=1 but cannot satisfy the no-positive-loss law with no destructive process.
Inertial persistence can, even with all present strict giving removed. -/
def Certificate : Prop :=
  CoherentAtNow history ∧
  TruthCore.German.Kant.CosmologicalInference.NecessaryAt history.ontic .inertial true ∧
  TruthCore.German.Kant.CosmologicalInference.ContingentAt history.ontic .inertial false ∧
  SameOnset .conserved .inertial ∧
  SameOnset .inertial .vanished ∧
  CoverageLaw .conserved ∧
  CoverageLaw .inertial ∧
  CoverageLaw .absent ∧
  ¬ CoverageLaw .vanished ∧
  OriginatesBeing history giving .inertial true false ∧
  GiverPresentWhenGiving history giving ∧
  ConcurrentAt .conserved ∧
  ¬ ConcurrentAt .inertial ∧
  history.IsAt .inertial false 1 ∧
  history.IsAt .inertial false 2 ∧
  history.IsAt .vanished false 1 ∧
  ¬ history.IsAt .vanished false 2 ∧
  (∀ g, ¬ frame.GivesAt .inertial g false 2) ∧
  frame.GivesAt .conserved true false 2 ∧
  NoCessationCause (noDestruction .inertial) false 1 ∧
  NoCessationCause (noDestruction .vanished) false 1 ∧
  (∀ t, ¬ history.IsAt .absent false t) ∧
  (∀ x t, (withdrawalAsLoss).existsAt t x ↔
    (noDestruction .vanished).existsAt t x) ∧
  Destroys withdrawalAsLoss () 1 2 false ∧
  CessationHasCause withdrawalAsLoss ∧
  ¬ NoCessationCause withdrawalAsLoss false 1

end WithdrawalLaw

end TruthCore.Causality.ConcurrentCessation
