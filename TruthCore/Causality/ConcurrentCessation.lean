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

end TruthCore.Causality.ConcurrentCessation
