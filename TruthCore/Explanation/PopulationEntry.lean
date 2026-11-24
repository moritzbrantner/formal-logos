module

public import TruthCore.Explanation.BruteContingencyParity
public import TruthCore.Modal.TemporalHistory
public import TruthCore.Modern.Hume.Induction
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

/-! Can an uncaused contingent founder be joined by another uncaused agent?
Analyst models for #1867/#1913. In each complete input `w`, bit `i` supplies
one persistent agent at time `i`, or none. No deaths, replacements, multiple
births at a date or further species are represented. The initial input selects
the founder. A new agent produces one distinguishable detector firing on the
next tick. Compare restrictions on the *entire* population with the same
mechanism, initial founder and complete actual history. Physical/metaphysical
admission of inputs, the cause assignment and the reason assignment are
interpretive commitments. -/

@[expose] public section
namespace TruthCore.Explanation.PopulationEntry

open TruthCore.Modern.Hume.Induction (Trace)
open TruthCore.Modal.TemporalHistory (History BeginsAt)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Explanation.ExistencePSR (Model Sound)
open TruthCore.Explanation.BruteContingencyParity (NoBruteContingentExistenceAt)

inductive Entity where
  | agent (birth : Nat)
  | firing (sourceBirth : Nat)
  deriving DecidableEq

/-- The presence interval for each candidate entity in a complete input. -/
def present (w : Trace) : Entity → Nat → Prop
  | .agent i, t => w i = true ∧ i ≤ t
  | .firing i, t => w i = true ∧ i + 1 = t

/-- A single detector reports whether any firing occurs at the given time.
The observation does not identify a source. -/
def readout (w : Trace) (t : Nat) : Prop := ∃ i, present w (.firing i) t

/-- Cardinality of the birth indices of the agents present at this time.
An index at most t is extant exactly when its input bit is on. -/
def population (w : Trace) (t : Nat) : Nat :=
  ((Finset.range (t+1)).filter (fun i => w i = true)).card

inductive Boundary where | conserved | capacityOne | unrestricted

/-- Both restrictions concern the total number of agents. A conserved total
in a model permitting deaths or compensating charges would be different. -/
def admits : Boundary → Trace → Prop
  | .conserved, w => ∀ t, population w (t+1) = population w t
  | .capacityOne, w => ∀ t, population w t ≤ 1
  | .unrestricted, _ => True

/-- Each possible agent is an external input. Within this modeled order the
sole productive relation is the entered agent producing its next-tick firing.
This is causation of the event's existence; reasons are assigned separately.
The accessibility component ranges between admissible complete inputs. -/
def history (boundary : Boundary) (now : Nat) : History Trace Entity Nat where
  now := now
  IsAt := present
  ontic := {
    frame := ⟨fun w v => admits boundary w ∧ admits boundary v⟩
    ExistsAt := fun w x => present w x now
    Causes := fun w x y => ∃ i, x = .agent i ∧ y = .firing i ∧ present w y now }

/-- In this #312 interpretation the entering agent supplies a circumstantial
reason for the event, and neither sort of token explains the agent's existence.
The latter stipulates the brute-source rival, independently of counting or
the metaphysical adequacy of such a reason assignment. -/
def reasonModel (boundary : Boundary) (now : Nat) : Model Trace Entity where
  ontic := (history boundary now).ontic
  explains := fun w r f => ∃ i, r = .circumstance (.agent i) ∧
    f = .fact (.firing i) ∧ present w (.firing i) now

/-- A single active bit; the founder history has that bit at zero. -/
def solitary (birth t : Nat) : Bool := decide (t = birth)

abbrev actual := solitary 0

/-- A literal common rival instance: the very same uncaused founder is
contingent on this frame, has no #312 existence reason, and produces its
represented firing. Thus at time one the local existence PSR fails here. -/
def FounderCase (b : Boundary) : Prop :=
  let h := history b 1
  let m := reasonModel b 1
  admits b actual ∧ ContingentAt h.ontic actual (.agent 0) ∧
  (∀ t, ¬ ∃ x, (history b t).ontic.Causes actual x (.agent 0)) ∧
  (¬ ∃ r, m.explains actual r (.fact (.agent 0))) ∧
  h.ontic.Causes actual (.agent 0) (.firing 0) ∧
  m.explains actual (.circumstance (.agent 0)) (.fact (.firing 0)) ∧
  ¬ NoBruteContingentExistenceAt m actual

/-- A new agent at k+1 alongside the original founder. All other input bits
are held fixed; the whole prior entity history agrees. At k+2 the new agent
is still present, produces its firing, has no incoming production edge and
no #312 existence reason. The target firing is absent in the base history. -/
def AdditionalEntry (b : Boundary) (k : Nat) : Prop :=
  let h := history b (k+2)
  let m := reasonModel b (k+2)
  ∃ v, h.ontic.frame.access actual v ∧
    (∀ i, i ≠ k+1 → v i = actual i) ∧
    (∀ x t, t ≤ k → (h.IsAt v x t ↔ h.IsAt actual x t)) ∧
    h.ontic.ExistsAt v (.agent 0) ∧ BeginsAt h v (.agent (k+1)) (k+1) ∧
    ContingentAt h.ontic v (.agent (k+1)) ∧
    (∀ t, ¬ ∃ x, (history b t).ontic.Causes v x (.agent (k+1))) ∧
    (¬ ∃ r, m.explains v r (.fact (.agent (k+1)))) ∧
    h.ontic.Causes v (.agent (k+1)) (.firing (k+1)) ∧
    readout v (k+2) ∧ ¬ readout actual (k+2)

/-- Conservation excludes entry even without the founder. Capacity alone
permits a solitary late entrant in the founder's absence, but in histories
with the founder it implies exactly the conserved histories. Unrestricted
inputs realize an additional effective agent at every proposed later tick. -/
def EntryComparison : Prop :=
  (∀ b t, Sound (reasonModel b t)) ∧ (∀ b, FounderCase b) ∧
  (∀ w, admits .conserved w ↔ ∀ t, w (t+1) = false) ∧
  (∀ w v, admits .conserved w → admits .conserved v → w 0 = v 0 → w = v) ∧
  (∀ w, w 0 = true → (admits .capacityOne w ↔ admits .conserved w)) ∧
  (∀ k, admits .capacityOne (solitary (k+1)) ∧
    ¬ (history .capacityOne 0).ontic.ExistsAt (solitary (k+1)) (.agent 0) ∧
    BeginsAt (history .capacityOne (k+1)) (solitary (k+1)) (.agent (k+1)) (k+1)) ∧
  (∀ k, ¬ AdditionalEntry .conserved k ∧
    ¬ AdditionalEntry .capacityOne k ∧ AdditionalEntry .unrestricted k)

end TruthCore.Explanation.PopulationEntry
