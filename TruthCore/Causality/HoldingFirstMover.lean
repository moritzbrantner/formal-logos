module

public import TruthCore.Causality.TotalHolding
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
# From the first holder to a holder held in no respect, and to the First Way (#2103)

Analyst formulations, attribution deferred. Note:
`docs/notes/caused-mover-cstar.md`, sections 9.4 and 10.5, which name three
missing pieces between the holding route and the absolute First-Way conclusion
`c1b68c21` (`FirstUnmovedMoverCannotBeLackingReading`): a total-holder repair
(section 10), a passage from the operative respect to every respect (2'), and a
MOTION_3 bridge (3).

**The passage (2').** The holding route ends at `5eb16c61`
(`UnlosableOperativeHolderCannotBeLacking`): there cannot be no holder of
another whose act in the respect by which it holds is one it could not lack. Two
open premises about the primitive, untimed `Lackability` carry that holder to
one that is held (MOTION_3) in no respect at all:

* `HeldActsAreLackable`: what another presently actualizes in a respect, the
  held thing could lack there;
* `LackableBeingLacksEveryAct`: what could lack being could lack each act it
  has.

With the existing `LackableActBringsLackableBeing` (`6e2176cd`), a holder held in
some respect could lack being and so could lack its operative act, which the
first holder cannot. No holding is mapped to or from timed giving, and neither
the esse instance `f834ee65` nor `PresentMomentHoldingReading` is used.

**The MOTION_3 bridge (3).** `FirstUnheldHolderCannotBeLacking` is the First-Way
reading with `MovedIn := HeldMotion` and moving read as holding another
(`firstUnheldHolder_iff_reading`). Reaching the First-Way statement in the
route's sense of motion (MOTION_1, eduction from potency to act, DISAMB-MOTION)
needs two open sense bridges, from MOTION_3 to MOTION_1:

* `HoldingAnotherIsMoving`: a holder of another moves it in some respect;
* `MovedIsHeld`: whatever is moved in some respect is held in some respect.

Applicability of every premise to reality remains OPEN. A countermodel shows that
a premise is needed in that interpretation, not that it is false.
-/

@[expose] public section

namespace TruthCore.Causality.HoldingFirstMover

open TruthCore.Causality.HoldingMotion
open TruthCore.Latin.Aquinas.SummaTheologiae (FirstUnmovedMoverCannotBeLackingReading)

variable {B R : Type}

/-- What is MOTION_3 held in a respect could lack its act in that respect. -/
def HeldActsAreLackable (InAct : B → R → Prop) (L : Lackability B R) (H : Holding B R) :
    Prop :=
  ∀ x r, HeldMotion InAct H x r → L.CanLack x r

/-- What could lack being could lack each act it has. -/
def LackableBeingLacksEveryAct (InAct : B → R → Prop) (L : Lackability B R) (esse : R) :
    Prop :=
  ∀ x r, L.CanLack x esse → InAct x r → L.CanLack x r

/-- MOTION_3 first holder: it is impossible that there be no holder of another
that is MOTION_3 held in no respect. -/
def FirstUnheldHolderCannotBeLacking (InAct : B → R → Prop) (H : Holding B R) : Prop :=
  ¬ ¬ ∃ f, (∃ x r, f ≠ x ∧ H.ActualizesNow f x r) ∧ ∀ r, ¬ HeldMotion InAct H f r

/-- Sense bridge MOTION_3 → MOTION_1, mover side: whatever presently actualizes
another in a respect moves it (`MovesIn`) in some respect. -/
def HoldingAnotherIsMoving (H : Holding B R) (MovesIn : B → B → R → Prop) : Prop :=
  ∀ f x r, f ≠ x → H.ActualizesNow f x r → ∃ s, MovesIn f x s

/-- Sense bridge MOTION_3 → MOTION_1, moved side: whatever is moved (`MovedIn`)
in some respect is MOTION_3 held in some respect. -/
def MovedIsHeld (InAct : B → R → Prop) (H : Holding B R) (MovedIn : B → R → Prop) : Prop :=
  ∀ f r, MovedIn f r → ∃ s, HeldMotion InAct H f s

/-- `HeldMotion` unfolded, for finite checks. -/
theorem heldMotion_iff {InAct : B → R → Prop} {H : Holding B R} {x : B} {r : R} :
    HeldMotion InAct H x r ↔ InAct x r ∧ ∃ z, z ≠ x ∧ H.ActualizesNow z x r :=
  ⟨fun ⟨z, h1, h2, h3⟩ => ⟨h1, z, h2, h3⟩, fun ⟨h1, z, h2, h3⟩ => ⟨z, h1, h2, h3⟩⟩

namespace Control

/-- Nonvacuity: `0` holds `1` in respect `0`; `1` could lack each act; nothing holds
`0`. Respects are `Fin 2`, `esse := 1`, everything is in act. -/
def soleHolder : Holding (Fin 2) (Fin 2) := ⟨fun z x r => z = 0 ∧ x = 1 ∧ r = 0⟩
def soleLack : Lackability (Fin 2) (Fin 2) := ⟨fun x _ => x = 1⟩

/-- Omitting `HeldActsAreLackable`: `0` holds `1` and `2` in respect `0`, `2` holds
`0` in `esse`; only `1` could lack anything. -/
def heldBack : Holding (Fin 3) (Fin 2) :=
  ⟨fun z x r => (z = 0 ∧ x ≠ 0 ∧ r = 0) ∨ (z = 2 ∧ x = 0 ∧ r = 1)⟩
def heldBackLack : Lackability (Fin 3) (Fin 2) := ⟨fun x _ => x = 1⟩

/-- Omitting `LackableBeingLacksEveryAct`: `0` holds `1` in both respects, `1`
holds `0` in `esse`; `0` could lack being but not its act in respect `0`, `1` could
lack each act. -/
def esseLoop : Holding (Fin 2) (Fin 2) :=
  ⟨fun z x r => (z = 0 ∧ x = 1) ∨ (z = 1 ∧ x = 0 ∧ r = 1)⟩
def esseLoopLack : Lackability (Fin 2) (Fin 2) := ⟨fun x r => (x = 0 ∧ r = 1) ∨ x = 1⟩

/-- All in act. -/
def allInAct {B : Type} : B → Fin 2 → Prop := fun _ _ => True

/-- Omission and nonvacuity controls, `esse := 1`, every being in act in every
respect.
(1) Sole holder: the unlosable-operative-holder conclusion, both lackability
premises, `LackableActBringsLackableBeing` and the MOTION_3 first-holder
conclusion hold. With moving read as holding and `MovedIn` as MOTION_3 holding,
both sense bridges and the First-Way reading hold.
(2) Held back: every premise of the passage except `HeldActsAreLackable` holds;
it and the first-holder conclusion fail.
(3) Esse loop: every premise of the passage except `LackableBeingLacksEveryAct`
holds; it and the first-holder conclusion fail.
(4) Sole holder, nothing moves: the first-holder conclusion and `MovedIsHeld`
hold, `HoldingAnotherIsMoving` and the First-Way reading fail.
(5) Sole holder, moving read as holding, everything moved in every respect:
the first-holder conclusion and `HoldingAnotherIsMoving` hold, `MovedIsHeld`
and the First-Way reading fail. -/
def Certificate : Prop :=
  (UnlosableOperativeHolderCannotBeLacking allInAct soleLack soleHolder ∧
    HeldActsAreLackable allInAct soleLack soleHolder ∧
    LackableActBringsLackableBeing allInAct soleLack 1 ∧
    LackableBeingLacksEveryAct allInAct soleLack 1 ∧
    FirstUnheldHolderCannotBeLacking allInAct soleHolder ∧
    HoldingAnotherIsMoving soleHolder (fun f x r => f ≠ x ∧ soleHolder.ActualizesNow f x r) ∧
    MovedIsHeld allInAct soleHolder (HeldMotion allInAct soleHolder) ∧
    FirstUnmovedMoverCannotBeLackingReading (HeldMotion allInAct soleHolder)
      (fun f x r => f ≠ x ∧ soleHolder.ActualizesNow f x r)) ∧
  (UnlosableOperativeHolderCannotBeLacking allInAct heldBackLack heldBack ∧
    LackableActBringsLackableBeing allInAct heldBackLack 1 ∧
    LackableBeingLacksEveryAct allInAct heldBackLack 1 ∧
    ¬ HeldActsAreLackable allInAct heldBackLack heldBack ∧
    ¬ FirstUnheldHolderCannotBeLacking allInAct heldBack) ∧
  (UnlosableOperativeHolderCannotBeLacking allInAct esseLoopLack esseLoop ∧
    HeldActsAreLackable allInAct esseLoopLack esseLoop ∧
    LackableActBringsLackableBeing allInAct esseLoopLack 1 ∧
    ¬ LackableBeingLacksEveryAct allInAct esseLoopLack 1 ∧
    ¬ FirstUnheldHolderCannotBeLacking allInAct esseLoop) ∧
  (MovedIsHeld allInAct soleHolder (fun _ _ => False) ∧
    ¬ HoldingAnotherIsMoving soleHolder (fun _ _ _ => False) ∧
    ¬ FirstUnmovedMoverCannotBeLackingReading (fun _ _ => False) (fun (_ _ : Fin 2) (_ : Fin 2) => False)) ∧
  (HoldingAnotherIsMoving soleHolder (fun f x r => f ≠ x ∧ soleHolder.ActualizesNow f x r) ∧
    ¬ MovedIsHeld allInAct soleHolder (fun _ _ => True) ∧
    ¬ FirstUnmovedMoverCannotBeLackingReading (fun (_ : Fin 2) (_ : Fin 2) => True)
      (fun f x r => f ≠ x ∧ soleHolder.ActualizesNow f x r))

end Control

end TruthCore.Causality.HoldingFirstMover
