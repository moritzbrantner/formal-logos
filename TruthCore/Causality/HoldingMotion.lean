module

public import TruthCore.Causality.ConcurrentActualization
public import TruthCore.Causality.MotionMoverFork
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

/-!
# Holding motion: an actualization reading of "being moved" (MOTION_3)

Analyst formulation, attribution deferred. It types the proposal that "being
moved is having a potential actualized, and that actualization comes from
being caused", read as *holding*: `x` is being moved in respect `r` when `x` is
in act in `r` and something other than `x` is presently actualizing `x` in `r`.
The known contemporary version is the existential reading of the First Way
(Feser); it is not attributed here. Aquinas's First Way takes motion strictly
(SCG I.13 [10], read in `docs/notes/caused-mover-cstar.md`), so this is a
sibling reformulation, not a reading of ST I q.2 a.3.

The sense is MOTION_3 of DISAMB-MOTION (`HeldMotion`). It is not MOTION_1
(`MotionMoverFork.BroadMotion`, reduction from potency to act now): under the
adopted POTENCY_1, what is held in `r` is in act in `r` and so not in potency to
it. `Control.Certificate` (parts 4 and 5) checks that a MOTION_1 premise of the
prima via (`MovedOnlyAsInPotencyReading`) fails for MOTION_3 whenever anything
is held, and that, where that premise holds of a MOTION_1 relation with one act
predicate shared by both senses, no being is moved in the same respect in both
senses. "Potential" in the proposal is read only as "actualized by another":
`HeldMotion` has no potency or lackability clause.

Primitives (explicitly identified):
* `Holding.ActualizesNow z x r`: `z` presently actualizes `x` in `r`. `x`'s
  present being in act in `r` is, now, from `z`'s present acting: the hand holds
  the stone aloft, the sun lights the air. It is not originating causation (the
  forge that heated the iron, no longer acting) and not the patient's reaction.
* `Lackability.CanLack x r`: `x` could be without its act in `r` (a contingent
  possession). The iron's heat and the stone's motion are such acts.

The derivation registered from this module runs one way: the respect-general
concurrent-actualization premise (`LackableActsAreHeld`) entails C\* in the
holding sense (`HeldMoverIsHeldInItsOperativeAct`); `Control.Certificate` part 3
shows that C\* in the holding sense entails neither that premise nor its esse
instance, and part 2 that the esse instance alone does not give C\*.

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.HoldingMotion

open TruthCore.Modal.TemporalHistory (History)
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualizedByAnother)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Primitive present actualization (holding): `ActualizesNow z x r` says that
`z` presently actualizes `x` in respect `r`, so that `x`'s present being in act
in `r` is from `z`'s present acting. -/
structure Holding (B R : Type) where
  ActualizesNow : B → B → R → Prop

/-- Primitive lackability: `CanLack x r` says that `x` could be without its act
in respect `r`. -/
structure Lackability (B R : Type) where
  CanLack : B → R → Prop

/-- MOTION_3, holding: `x` is being moved in `r` when it is in act in `r` and
something other than `x` is presently actualizing it in `r`. -/
inductive HeldMotion {B R : Type} (InAct : B → R → Prop) (H : Holding B R) (x : B) (r : R) :
    Prop
  | intro (z : B) : InAct x r → z ≠ x → H.ActualizesNow z x r → HeldMotion InAct H x r

/-- Whatever presently actualizes another in a respect is itself in act in that
respect (formally or virtually; `InAct` is abstract). The holding counterpart of
*movet autem aliquid secundum quod est actu*. -/
def ActualizerIsInAct {B R : Type} (InAct : B → R → Prop) (H : Holding B R) : Prop :=
  ∀ z x r, H.ActualizesNow z x r → InAct z r

/-- Respect-general concurrent actualization by another: whatever is in act in a
respect in which it could lack its act is presently actualized in that respect
by something other than itself. -/
def LackableActsAreHeld {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R) : Prop :=
  ∀ x r, InAct x r → L.CanLack x r → HeldMotion InAct H x r

/-- C\* in the holding sense: a mover that presently actualizes another in a
respect, and could lack its own act in that respect, is presently held in that
respect by something other than itself. -/
def HeldMoverIsHeldInItsOperativeAct {B R : Type} (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) : Prop :=
  ∀ y x r, y ≠ x → H.ActualizesNow y x r → L.CanLack y r → HeldMotion InAct H y r

/-- Concurrent actualization at esse, untimed: whatever is in act as to being
and could lack being is presently given being by something other than itself. -/
def LackableBeingIsHeld {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R) (esse : R) : Prop :=
  ∀ x, InAct x esse → L.CanLack x esse → HeldMotion InAct H x esse

/-- Accident-inclusive conservation: whatever presently gives another its being
presently actualizes it in every act it has that it could lack. -/
def GivingBeingHoldsLackableActs {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R) (esse : R) : Prop :=
  ∀ g x r, g ≠ x → H.ActualizesNow g x esse → InAct x r → L.CanLack x r →
    H.ActualizesNow g x r

/-- Whatever has an act it could lack is in act as to being and could lack
being. -/
def LackableActBringsLackableBeing {B R : Type} (InAct : B → R → Prop)
    (L : Lackability B R) (esse : R) : Prop :=
  ∀ x r, InAct x r → L.CanLack x r → InAct x esse ∧ L.CanLack x esse

/-- The present-moment reading of the timed concurrent-actualization vocabulary:
at moment `t` of history `v`, being in act as to being is being present, what
could lack being has received esse, and giving being is presently actualizing
in esse. -/
def PresentMomentHoldingReading {W B T P R : Type} (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop) (v : W) (t : T) (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R) : Prop :=
  (∀ x, InAct x esse → h.IsAt v x t) ∧ (∀ x, L.CanLack x esse → ∃ p, EsseReceivedIn x p) ∧
    (∀ z x, G.GivesAt v z x t → H.ActualizesNow z x esse)

/-- Something is presently held: some being is in act in a respect and presently
actualized in it by another. -/
def SomethingIsHeld {B R : Type} (InAct : B → R → Prop) (H : Holding B R) : Prop :=
  ∃ x r, HeldMotion InAct H x r

/-- Holding per se link: a holder of another that is itself held in the respect
by which it holds is a link `AsHeld` of a holding series. -/
def HeldInOperativeActIsPerSe {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (AsHeld : B → B → Prop) : Prop :=
  ∀ y x r, y ≠ x → H.ActualizesNow y x r → HeldMotion InAct H y r → AsHeld y x

/-- No infinite holding series: the holding per se relation is well founded. -/
def NoInfiniteHoldingSeries {B : Type} (AsHeld : B → B → Prop) : Prop :=
  ∀ x, Acc AsHeld x

/-- Relative first holder: it is impossible that there be no holder of another
that is not held in the respect by which it holds. -/
def UnheldOperativeHolderCannotBeLacking {B R : Type} (InAct : B → R → Prop)
    (H : Holding B R) : Prop :=
  ¬ ¬ ∃ f x r, f ≠ x ∧ H.ActualizesNow f x r ∧ ¬ HeldMotion InAct H f r

/-- A holder of another whose act in the respect by which it holds it could not
lack cannot be lacking. -/
def UnlosableOperativeHolderCannotBeLacking {B R : Type} (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) : Prop :=
  ¬ ¬ ∃ f x r, f ≠ x ∧ H.ActualizesNow f x r ∧ InAct f r ∧ ¬ L.CanLack f r

/-- Mutual holding: two distinct beings each presently actualize the other in
one respect in which both are in act (two cards leaning on each other, each
propped by the other). -/
def SomeTwoHoldEachOther {B R : Type} (InAct : B → R → Prop) (H : Holding B R) : Prop :=
  ∃ a b r, a ≠ b ∧ H.ActualizesNow a b r ∧ H.ActualizesNow b a r ∧ InAct a r ∧ InAct b r

/-- No two distinct beings presently hold each other in one respect in which
both are in act. -/
def NoTwoHoldEachOther {B R : Type} (InAct : B → R → Prop) (H : Holding B R) : Prop :=
  ¬ SomeTwoHoldEachOther InAct H

namespace Control

/-- Stick model: `0` holds `1` and `1` holds `2` in the moving respect `true`;
nothing holds anything in `esse` (`false`). -/
def stick : Holding (Fin 3) Bool :=
  ⟨fun z x r => r = true ∧ ((z = 0 ∧ x = 1) ∨ (z = 1 ∧ x = 2))⟩

/-- Everything but `0` could lack every act. -/
def notZero : Lackability (Fin 3) Bool := ⟨fun x _ => x ≠ 0⟩

/-- Iron model: `0` gives `1` (iron) and `2` (wood) being; the iron holds the
wood's heat (`true`); nothing holds the iron's heat. -/
def iron : Holding (Fin 3) Bool :=
  ⟨fun z x r => (z = 0 ∧ x ≠ 0 ∧ r = false) ∨ (z = 1 ∧ x = 2 ∧ r = true)⟩

/-- Holders held in another respect: `0` holds `1` and `2` in `true`, `2` holds
`0` in `false`. -/
def crossed : Holding (Fin 3) Bool :=
  ⟨fun z x r => (z = 0 ∧ x ≠ 0 ∧ r = true) ∨ (z = 2 ∧ x = 0 ∧ r = false)⟩

/-- In the crossed model, exactly the held acts could be lacked. -/
def crossedLack : Lackability (Fin 3) Bool :=
  ⟨fun x r => (x = 0 ∧ r = false) ∨ (x ≠ 0 ∧ r = true)⟩

/-- The crossed model is in act everywhere except `1` as to `false`. -/
def crossedInAct : Fin 3 → Bool → Prop := fun x r => ¬ (x = 1 ∧ r = false)

/-- Two cards: each holds the other in the one respect. -/
def cards : Holding Bool Unit := ⟨fun z x _ => z ≠ x⟩

/-- Directions, separations, sense-mixing and nonvacuity controls.
(1) Two cards hold each other: mutual holding, the actualizer premise, C\* in
the holding sense and respect-general concurrent actualization hold together.
(2) Iron: concurrent actualization at esse, the actualizer premise and
lackable-being hold; accident-inclusive conservation and C\* in the holding
sense fail (esse instance does not give C\*).
(3) Stick: C\* in the holding sense (non-vacuously) and the actualizer premise
hold; respect-general concurrent actualization and its esse instance fail
(C\* gives neither).
(4) For every interpretation, if anything is held, the MOTION_1 premise
"moved only as in potency" fails for MOTION_3 under the adopted POTENCY_1.
(5) For every interpretation satisfying that premise for a MOTION_1 relation,
nothing is moved in the same respect in both senses.
(6) Crossed: something is held, the holding per se premise, the holding
regress, the actualizer premise, C\* in the holding sense and respect-general
concurrent actualization hold, an unlosable operative holder exists, and the
absolute conclusion fails: every holder is held in some respect. -/
def Certificate : Prop :=
  (SomeTwoHoldEachOther (fun _ _ => True) cards ∧ ActualizerIsInAct (fun _ _ => True) cards ∧
    HeldMoverIsHeldInItsOperativeAct (fun _ _ => True) ⟨fun _ _ => True⟩ cards ∧
    LackableActsAreHeld (fun _ _ => True) ⟨fun _ _ => True⟩ cards) ∧
  (LackableBeingIsHeld (fun _ _ => True) notZero iron false ∧
    ActualizerIsInAct (fun _ _ => True) iron ∧
    LackableActBringsLackableBeing (fun _ _ => True) notZero false ∧
    ¬ GivingBeingHoldsLackableActs (fun _ _ => True) notZero iron false ∧
    ¬ HeldMoverIsHeldInItsOperativeAct (fun _ _ => True) notZero iron) ∧
  (HeldMoverIsHeldInItsOperativeAct (fun _ _ => True) notZero stick ∧
    (∃ y x r, y ≠ x ∧ stick.ActualizesNow y x r ∧ notZero.CanLack y r) ∧
    ActualizerIsInAct (fun _ _ => True) stick ∧
    ¬ LackableActsAreHeld (fun _ _ => True) notZero stick ∧
    ¬ LackableBeingIsHeld (fun _ _ => True) notZero stick false) ∧
  (∀ {B R : Type} (InAct CanBe : B → R → Prop) (H : Holding B R),
    SomethingIsHeld InAct H →
      ¬ MovedOnlyAsInPotencyReading (HeldMotion InAct H) (AdoptedPotency.InPotency InAct CanBe)) ∧
  (∀ {B R : Type} (InAct CanBe : B → R → Prop) (H : Holding B R) (moved : B → R → Prop),
    MovedOnlyAsInPotencyReading moved (AdoptedPotency.InPotency InAct CanBe) →
      ∀ x r, MotionMoverFork.BroadMotion moved x r → ¬ HeldMotion InAct H x r) ∧
  (SomethingIsHeld crossedInAct crossed ∧
    HeldInOperativeActIsPerSe crossedInAct crossed (fun _ _ => False) ∧
    NoInfiniteHoldingSeries (fun _ _ : Fin 3 => False) ∧
    ActualizerIsInAct crossedInAct crossed ∧
    HeldMoverIsHeldInItsOperativeAct crossedInAct crossedLack crossed ∧
    LackableActsAreHeld crossedInAct crossedLack crossed ∧
    (∃ f x r, f ≠ x ∧ crossed.ActualizesNow f x r ∧ crossedInAct f r ∧
      ¬ crossedLack.CanLack f r) ∧
    ¬ FirstUnmovedMoverCannotBeLackingReading (HeldMotion crossedInAct crossed)
      crossed.ActualizesNow)

end Control

end TruthCore.Causality.HoldingMotion
