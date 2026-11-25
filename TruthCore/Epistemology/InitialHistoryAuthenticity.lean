module

public import TruthCore.Explanation.HistorySelection

/-! # Initial conditions, complete trajectories and authentic records

Analyst formulation for the historical-reliability investigation of #1904 and
the existence-PSR comparison. `allowed` selects initial conditions; it is not a
metaphysical accessibility relation. One fixed, possibly time-dependent,
deterministic rule generates every trajectory. There are no later independent
inputs. The state carrier must include any memory the chosen law uses; a
one-coordinate readout need not be a complete state.

The new trajectory function is indexed by a time-dependent rule, unlike an
iterate of one endofunction. Existing `HistorySelection.SameEvidence` and
`EvidenceOnly` retain their informational meanings. No epistemic entitlement,
probability, adequate explanation or metaphysical admissibility is defined.
-/

@[expose] public section

namespace TruthCore.Epistemology.InitialHistoryAuthenticity

open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory

/-- The whole generated state history, including the supplied input at time
zero. Time zero is the start of this model, not a proof of a cosmic beginning. -/
def evolve (step : Nat → S → S) (initial : S) : Nat → S
  | 0 => initial
  | n + 1 => step n (evolve step initial n)

/-- The selected observation at one time. Equality of these values is the
chosen observational equivalence, not numerical identity of observed bearers. -/
def observed (step : Nat → S → S) (read : S → O) (n : Nat) (initial : S) : O :=
  read (evolve step initial n)

/-- Two admitted initial states give different values of the selected map.
This is extensional variation, not unexplained existence or a probability. -/
def Varies (allowed : I → Prop) (value : I → O) : Prop :=
  ∃ i j, allowed i ∧ allowed j ∧ value i ≠ value j

/-- Every admitted input giving a positive record makes that record's content
true. `positive o` means this record asserts the selected historical claim;
`content o i` is the primitive historical truth condition for that claim in
the history indexed by i. Its real historical interpretation remains OPEN. -/
def RecordsSound (allowed : I → Prop) (observe : I → O)
    (positive : O → Prop) (content : O → I → Prop) : Prop :=
  ∀ i, allowed i → positive (observe i) → content (observe i) i

/-- The exact candidate restriction: no input is admitted if its positive
observed record would have false historical content. This is a test on a
candidate restriction, not a reason to accept that restriction. -/
def SafeInitial (observe : I → O) (positive : O → Prop)
    (content : O → I → Prop) (i : I) : Prop :=
  positive (observe i) → content (observe i) i

/-- Each positive observation fiber, intersected with the admitted inputs,
is contained in the truth set of that particular record's historical content.
Empty fibers pass; actual applicability also needs an admitted input. -/
def PositiveFibersTrue (allowed : I → Prop) (observe : I → O)
    (positive : O → Prop) (content : O → I → Prop) : Prop :=
  ∀ o, positive o → ∀ i, allowed i → observe i = o → content o i

/-- Within a positive record's admitted observation fiber its authenticity
has one truth value. That value may be false: this is not soundness. -/
def PositiveUniform (allowed : I → Prop) (observe : I → O)
    (positive : O → Prop) (content : O → I → Prop) : Prop :=
  ∀ i j, allowed i → allowed j → positive (observe i) →
    observe i = observe j →
    (content (observe i) i ↔ content (observe j) j)

/-- Each inhabited positive observation fiber has an authentic member.
With uniformity this supplies truth, rather than only a common truth value.
It is an explicit premise, not an independently accessible audit procedure. -/
def PositiveWitnesses (allowed : I → Prop) (observe : I → O)
    (positive : O → Prop) (content : O → I → Prop) : Prop :=
  ∀ i, allowed i → positive (observe i) →
    ∃ j, allowed j ∧ observe j = observe i ∧ content (observe j) j

/-- The familiar evidence-only comparison, restricted to admitted inputs and
using all equality tests on the observation. The proposition tested is the
historical truth of this input's observed record, including nonpositive ones. -/
def AuthenticityEvidenceOnly (allowed : I → Prop) (observe : I → O)
    (content : O → I → Prop) : Prop :=
  EvidenceOnly (fun (i : { i // allowed i }) o => observe i.val = o)
    (fun _ => True) (fun i => content (observe i.val) i.val)

/-- Conditional historical identity: when the SAME bearer exists in two
supplied histories, its supplied origin value is the same. `origin` is a
primitive historical descriptor, not causation or an analysis of essence.
Existence is the existing Ontic field; no mandatory presence is inferred. -/
def EssentialOrigin (h : History I B T) (origin : I → B → H) : Prop :=
  ∀ i j b, h.ontic.ExistsAt i b → h.ontic.ExistsAt j b → origin i b = origin j b

/-- The designated record bearer exists in each admitted history. -/
def BearersPresent (h : History I B T) (allowed : I → Prop) (bearer : I → B) : Prop :=
  ∀ i, allowed i → h.ontic.ExistsAt i (bearer i)

/-- A strong identification bridge: equal observations of admitted histories
identify the numerically SAME bearer. Essential origin alone does not give it. -/
def IdentifiesBearer (allowed : I → Prop) (observe : I → O) (bearer : I → B) : Prop :=
  ∀ i j, allowed i → allowed j → observe i = observe j → bearer i = bearer j

/-- Reversible maps preserve admitted variation. Complete trajectories retain
time zero even for irreversible maps. No universal conservation of coarse
output variation, ignorance or absence of explanation is asserted. -/
def Dynamics : Prop :=
  (∀ (I O : Type) (allowed : I → Prop) (value : I → O),
    Set.InjOn value { i | allowed i } →
    (Varies allowed value ↔ Varies allowed (fun i => i))) ∧
  (∀ (S : Type) (step : Nat → S → S),
    (∀ n, Function.Injective (step n)) →
    ∀ n, Function.Injective (fun i => evolve step i n)) ∧
  (∀ (S : Type) (step : Nat → S → S), Function.Injective (evolve step)) ∧
  (∀ (S : Type) (step : Nat → S → S) (allowed : S → Prop),
    Varies allowed (evolve step) ↔ Varies allowed (fun i => i)) ∧
  (∀ (S O : Type) (step : Nat → S → S) (read : S → O) (n : Nat)
      (allowed : S → Prop),
    Set.InjOn (observed step read n) { i | allowed i } →
    (Varies allowed (observed step read n) ↔ Varies allowed (fun i => i)))

/-- Exact admissible-input condition, observation-fiber condition, and
truth-plus-uniformity factorization. The last clause reuses EvidenceOnly;
uniform classification is kept separate from positive-record truth. -/
def Authenticity : Prop :=
  (∀ (I O : Type) (allowed : I → Prop) (observe : I → O)
      (positive : O → Prop) (content : O → I → Prop),
    (RecordsSound allowed observe positive content ↔
      ∀ i, allowed i → SafeInitial observe positive content i) ∧
    (RecordsSound allowed observe positive content ↔
      PositiveFibersTrue allowed observe positive content) ∧
    (RecordsSound allowed observe positive content ↔
      PositiveUniform allowed observe positive content ∧
      PositiveWitnesses allowed observe positive content)) ∧
  (∀ (I O : Type) (allowed : I → Prop) (observe : I → O)
      (content : O → I → Prop),
    AuthenticityEvidenceOnly allowed observe content ↔
      PositiveUniform allowed observe (fun _ => True) content)

/-- Existing bearers plus essential historical identity and successful bearer
identification give uniform origins over observations. Actual record truth
still requires an authentic witness in each inhabited positive fiber. -/
def IdentityBridge : Prop :=
  ∀ (I B T H O : Type) (h : History I B T) (allowed : I → Prop)
      (observe : I → O) (positive : O → Prop) (bearer : I → B)
      (origin : I → B → H) (claim : O → H),
    EssentialOrigin h origin → BearersPresent h allowed bearer →
    IdentifiesBearer allowed observe bearer →
    (RecordsSound allowed observe positive (fun o i => origin i (bearer i) = claim o) ↔
      PositiveWitnesses allowed observe positive (fun o i => origin i (bearer i) = claim o))

/-! Concrete structural controls. All Boolean candidates are admitted where
`all` is used. Neither these assignments nor a hidden origin bit establishes
that a fabricated past is metaphysically admissible. -/

def all (_ : I) : Prop := True
def erase (_ : Nat) (_ : Bool) : Bool := false
def reverse (_ : Nat) (b : Bool) : Bool := !b
def record (i : Bool × Bool) : Bool := i.2
def positiveRecord (o : Bool) : Prop := o = true
def pastContent (o : Bool) (i : Bool × Bool) : Prop := i.1 = o
def accurateInputs (i : Bool × Bool) : Prop := i.1 = i.2
def falsePositiveInputs (i : Bool × Bool) : Prop := i.1 = false ∧ i.2 = true

/-- A retained historical coordinate is copied into the record. This is a
positive truth-tracking mechanism in the surrogate, conditional on genuine
access to that coordinate, and can correct an inaccurate initial record. -/
def copyPast (_ : Nat) (i : Bool × Bool) : Bool × Bool := (i.1, i.1)

/-- The rule stamps a positive record irrespective of the historical
coordinate. Same deterministic lawhood does not certify its record content. -/
def stampPositive (_ : Nat) (i : Bool × Bool) : Bool × Bool := (i.1, true)

/-- Fixed populated numerical roster in every alternative and at every time.
Empty ordinary causation is disclosed: this is a presence/identity control,
not a causal history or a complete metaphysical model. -/
def identityHistory : History (Bool × Bool) Bool Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False
  }
  IsAt := fun _ _ _ => True
  now := ()

/-- An explicitly stipulated essential marker of the numerical bearer.
It has no independent fossil, memory or natural-origin interpretation. -/
def originMarker (_ : Bool × Bool) (b : Bool) : Bool := b
def recordBearer (i : Bool × Bool) : Bool := i.1

/-- Coalescence, reversible change, lossy readout, non-singleton sound input
restriction, uniformly false fibers, identity without identification, and a
deterministic correcting channel. Every advertised claim is a conjunct here. -/
def Controls : Prop :=
  (Varies all (evolve erase) ∧
    (∀ n i, evolve erase i (n + 1) = false) ∧
    ¬ Varies all (fun i => evolve erase i 1)) ∧
  ((∀ n, Function.Injective (fun i => evolve reverse i n)) ∧
    Varies all (fun i => evolve reverse i 1) ∧
    ¬ Varies all (observed reverse (fun _ => ()) 1)) ∧
  (RecordsSound accurateInputs record positiveRecord pastContent ∧
    accurateInputs (false, false) ∧ accurateInputs (true, true) ∧
    (false, false) ≠ (true, true)) ∧
  (¬ RecordsSound all record positiveRecord pastContent ∧
    ¬ PositiveUniform all record positiveRecord pastContent ∧
    EssentialOrigin identityHistory originMarker ∧
    BearersPresent identityHistory all recordBearer ∧
    ¬ IdentifiesBearer all record recordBearer) ∧
  (falsePositiveInputs (false, true) ∧
    PositiveUniform falsePositiveInputs record positiveRecord pastContent ∧
    ¬ PositiveWitnesses falsePositiveInputs record positiveRecord pastContent ∧
    ¬ RecordsSound falsePositiveInputs record positiveRecord pastContent) ∧
  (RecordsSound all (observed copyPast record 1) positiveRecord pastContent ∧
    (false, false) ≠ (false, true) ∧
    evolve copyPast (false, false) 1 = evolve copyPast (false, true) 1) ∧
  ¬ RecordsSound all (observed stampPositive record 1) positiveRecord pastContent

end TruthCore.Epistemology.InitialHistoryAuthenticity
