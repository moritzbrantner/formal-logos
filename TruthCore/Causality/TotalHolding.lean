module

public import TruthCore.Causality.HoldingMotion

/-!
# Total holding: the repair of the holding per se link against mutual holding

Analyst formulation, attribution deferred. It continues `HoldingMotion`
(MOTION_3, `HeldMotion`). In `docs/notes/caused-mover-cstar.md`, section 9.2,
the holding per se link (`HeldInOperativeActIsPerSe`) and the holding regress
exclude mutual holding in one respect, and two cards leaning on each other are
an ordinary statics case of it, so that bundle is inconsistent.

The named repair restricts the per se link to a **total holder**
(`TotallyHolds`): `z` holds `x` in `r`, `z` is the only thing that holds `x` in
`r` (no other present actualizer of `x` in `r`), and `x` does not hold `z` in
`r` (no reciprocal present actualization). The link then
reads: a total holder that is itself totally held in the respect by which it
holds is a link of a total-holding series (`TotallyHeldTotalHolderIsPerSe`).

What this module states and the batch checks:
* the restricted link and its regress are consistent with two leaning cards
  (`Control.Certificate` part 1);
* with something totally held they give a relative first *total* holder that
  is not totally held in the act by which it holds
  (`TotalHolderNotTotallyHeldCannotBeLacking`), and not one that is unheld
  there (part 2); the bridge `HeldTotalHolderIsTotallyHeld` would close that
  gap;
* under the esse-side support bundle of C\* in the holding sense, a total
  holder of an act the held thing could lack presently actualizes it as to
  being (`TotalHolderOfLackableActGivesBeing`; the holding relation at esse,
  not the timed giving of the esse-root routes);
* unheldness in every respect does not give pure act even with the whole
  esse-side bundle (part 3); a potency clause is a sufficient extra premise
  (`PotencyBringsLackableBeing`, giving `UnheldInBeingIsPureAct`).

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.TotalHolding

open TruthCore.Causality.HoldingMotion
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Total holding: `z` totally holds `x` in respect `r` when `z` is other than
`x`, presently actualizes `x` in `r`, is the only being that presently actualizes
`x` in `r` (no other present actualizer of `x` in `r`), and `x` does not
presently actualize `z` in `r` (no reciprocal present actualization in `r`).
Defined from the primitive holding relation. -/
def TotallyHolds {B R : Type} (H : Holding B R) (z x : B) (r : R) : Prop :=
  z ≠ x ∧ H.ActualizesNow z x r ∧ (∀ w, H.ActualizesNow w x r → w = z) ∧
    ¬ H.ActualizesNow x z r

/-- Totally held: `x` is in act in `r` and some being totally holds it there. A
strengthening of MOTION_3 (`totallyHeld_held`), not a further sense of
motion. -/
def TotallyHeld {B R : Type} (InAct : B → R → Prop) (H : Holding B R) (x : B) (r : R) :
    Prop :=
  InAct x r ∧ ∃ z, TotallyHolds H z x r

/-- What is totally held is MOTION_3 held. -/
theorem totallyHeld_held {B R : Type} {InAct : B → R → Prop} {H : Holding B R} {x : B}
    {r : R} (h : TotallyHeld InAct H x r) : HeldMotion InAct H x r := by
  obtain ⟨hAct, z, hzx, hA, _, _⟩ := h
  exact ⟨z, hAct, hzx, hA⟩

/-- Something is totally held: some being is in act in a respect and totally
held there. -/
def SomethingIsTotallyHeld {B R : Type} (InAct : B → R → Prop) (H : Holding B R) : Prop :=
  ∃ x r, TotallyHeld InAct H x r

/-- Total-holding per se link: a total holder of another that is itself totally
held in the respect by which it holds is a link `AsTotallyHeld` of a
total-holding series. -/
def TotallyHeldTotalHolderIsPerSe {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (AsTotallyHeld : B → B → Prop) : Prop :=
  ∀ y x r, TotallyHolds H y x r → TotallyHeld InAct H y r → AsTotallyHeld y x

/-- No infinite total-holding series: the total-holding per se relation is well
founded. -/
def NoInfiniteTotalHoldingSeries {B : Type} (AsTotallyHeld : B → B → Prop) : Prop :=
  ∀ x, Acc AsTotallyHeld x

/-- Relative first total holder: it is impossible that there be no total holder
of another that is not totally held in the respect by which it holds. -/
def TotalHolderNotTotallyHeldCannotBeLacking {B R : Type} (InAct : B → R → Prop)
    (H : Holding B R) : Prop :=
  ¬ ¬ ∃ f x r, TotallyHolds H f x r ∧ ¬ TotallyHeld InAct H f r

/-- A total holder of another that is MOTION_3 held in the respect by which it
holds is totally held there. -/
def HeldTotalHolderIsTotallyHeld {B R : Type} (InAct : B → R → Prop) (H : Holding B R) :
    Prop :=
  ∀ f x r, TotallyHolds H f x r → HeldMotion InAct H f r → TotallyHeld InAct H f r

/-- First total holder unheld in its operative act: it is impossible that there
be no total holder of another that is not MOTION_3 held in the respect by which
it holds. -/
def UnheldTotalHolderCannotBeLacking {B R : Type} (InAct : B → R → Prop) (H : Holding B R) :
    Prop :=
  ¬ ¬ ∃ f x r, TotallyHolds H f x r ∧ ¬ HeldMotion InAct H f r

/-- A total holder of an act that the held thing could lack presently actualizes
the held thing as to being (the holding relation at `esse`). -/
def TotalHolderOfLackableActGivesBeing {B R : Type} (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R) : Prop :=
  ∀ z x r, TotallyHolds H z x r → InAct x r → L.CanLack x r → H.ActualizesNow z x esse

/-- Whatever is in potency (adopted POTENCY_1) in some respect is in act as to
being and could lack being. -/
def PotencyBringsLackableBeing {B R : Type} (InAct CanBe : B → R → Prop)
    (L : Lackability B R) (esse : R) : Prop :=
  ∀ x r, AdoptedPotency.InPotency InAct CanBe x r → InAct x esse ∧ L.CanLack x esse

/-- Whatever is not MOTION_3 held as to being is pure act: in potency (adopted
POTENCY_1) in no respect. The antecedent also holds of an item not in act as to
being. -/
def UnheldInBeingIsPureAct {B R : Type} (InAct CanBe : B → R → Prop) (H : Holding B R)
    (esse : R) : Prop :=
  ∀ f, ¬ HeldMotion InAct H f esse → PureAct (AdoptedPotency.InPotency InAct CanBe) f

/-- Every holder of another that is MOTION_3 held in no respect is pure act. Used
only in `Control.Certificate`. -/
def EveryUnheldHolderIsPureAct {B R : Type} (InAct CanBe : B → R → Prop) (H : Holding B R) :
    Prop :=
  ∀ f, (∃ x r, f ≠ x ∧ H.ActualizesNow f x r) → (∀ r, ¬ HeldMotion InAct H f r) →
    PureAct (AdoptedPotency.InPotency InAct CanBe) f

namespace Control

/-- Two cards on a floor, on the earth, with a stone on the floor: `0` and `1`
(cards) hold each other, the floor `2` holds both cards and the stone `4`, and
the earth `3` holds the floor. One respect. -/
def cardsOnFloor : Holding (Fin 5) Unit :=
  ⟨fun z x _ => (z = 0 ∧ x = 1) ∨ (z = 1 ∧ x = 0) ∨ (z = 2 ∧ x = 0) ∨ (z = 2 ∧ x = 1) ∨
    (z = 3 ∧ x = 2) ∨ (z = 2 ∧ x = 4)⟩

/-- The total-holding links of `cardsOnFloor`: the floor holds the stone as
itself totally held by the earth. -/
def cardsOnFloorLinks : Fin 5 → Fin 5 → Prop := fun y x => y = 2 ∧ x = 4

/-- Co-held holder: `1` totally holds `0`; `2` and `3` both hold `1` and hold
each other. One respect. -/
def coHeld : Holding (Fin 4) Unit :=
  ⟨fun z x _ => (z = 1 ∧ x = 0) ∨ (z = 2 ∧ x = 1) ∨ (z = 3 ∧ x = 1) ∨ (z = 2 ∧ x = 3) ∨
    (z = 3 ∧ x = 2)⟩

/-- Unlosably held giver with an unrealized capacity: `0` holds `1` as to being
(`0`) and in respect `1`; nothing holds `0`. Respect `2` is one in which nothing
is in act. -/
def giver : Holding (Fin 2) (Fin 3) := ⟨fun z x r => z = 0 ∧ x = 1 ∧ r ≠ 2⟩

/-- Everything is in act in respects `0` and `1`, nothing in respect `2`. -/
def giverInAct : Fin 2 → Fin 3 → Prop := fun _ r => r ≠ 2

/-- Only `0` can be in respect `2`. -/
def giverCanBe : Fin 2 → Fin 3 → Prop := fun x r => x = 0 ∧ r = 2

/-- The variant in which only `1` can be in respect `2`. -/
def heldCanBe : Fin 2 → Fin 3 → Prop := fun x r => x = 1 ∧ r = 2

/-- Only `1` could lack its acts (in respects `0` and `1`). -/
def giverLack : Lackability (Fin 2) (Fin 3) := ⟨fun x r => x = 1 ∧ r ≠ 2⟩

/-- Consistency, gap and separation controls.
(1) Cards on a floor: two cards hold each other, something is totally held, the
total-holding per se link holds with a well-founded link relation, and a total
holder unheld in its operative act exists (the earth); every holding per se
link of the unrestricted kind fails to be well founded.
(2) Co-held holder: something is totally held, the total-holding per se link
and its regress hold, the actualizer premise, respect-general concurrent
actualization and C\* in the holding sense hold, two beings hold each other,
and no total holder is unheld in its operative act; the bridge
`HeldTotalHolderIsTotallyHeld` fails, and no holder has an operative act it
could not lack.
(3) Giver: the esse instance of concurrent actualization, accident-inclusive
conservation, the lackable-being bridge, the actualizer premise, respect-general
concurrent actualization and C\* in the holding sense hold; `0` totally holds
`1` in an act `1` could lack; `0` holds another and is held in no respect; yet
`0` is in potency in respect `2`, so the potency bridge and
`EveryUnheldHolderIsPureAct` fail.
(4) Held potency: with only `1` able to be in respect `2`, the potency bridge
and the esse instance hold with something in potency. -/
def Certificate : Prop :=
  (SomeTwoHoldEachOther (fun _ _ => True) cardsOnFloor ∧
    SomethingIsTotallyHeld (fun _ _ => True) cardsOnFloor ∧
    TotallyHeldTotalHolderIsPerSe (fun _ _ => True) cardsOnFloor cardsOnFloorLinks ∧
    NoInfiniteTotalHoldingSeries cardsOnFloorLinks ∧
    (∃ f x r, TotallyHolds cardsOnFloor f x r ∧ ¬ HeldMotion (fun _ _ => True) cardsOnFloor f r) ∧
    ∀ AsHeld : Fin 5 → Fin 5 → Prop,
      HeldInOperativeActIsPerSe (fun _ _ => True) cardsOnFloor AsHeld →
        ¬ NoInfiniteHoldingSeries AsHeld) ∧
  (SomethingIsTotallyHeld (fun _ _ => True) coHeld ∧
    TotallyHeldTotalHolderIsPerSe (fun _ _ => True) coHeld (fun _ _ => False) ∧
    NoInfiniteTotalHoldingSeries (fun _ _ : Fin 4 => False) ∧
    ActualizerIsInAct (fun _ _ => True) coHeld ∧
    LackableActsAreHeld (fun _ _ => True) ⟨fun _ _ => True⟩ coHeld ∧
    HeldMoverIsHeldInItsOperativeAct (fun _ _ => True) ⟨fun _ _ => True⟩ coHeld ∧
    SomeTwoHoldEachOther (fun _ _ => True) coHeld ∧
    ¬ UnheldTotalHolderCannotBeLacking (fun _ _ => True) coHeld ∧
    ¬ HeldTotalHolderIsTotallyHeld (fun _ _ => True) coHeld ∧
    ¬ UnlosableOperativeHolderCannotBeLacking (fun _ _ => True) ⟨fun _ _ => True⟩ coHeld) ∧
  (LackableBeingIsHeld giverInAct giverLack giver 0 ∧
    GivingBeingHoldsLackableActs giverInAct giverLack giver 0 ∧
    LackableActBringsLackableBeing giverInAct giverLack 0 ∧
    ActualizerIsInAct giverInAct giver ∧
    LackableActsAreHeld giverInAct giverLack giver ∧
    HeldMoverIsHeldInItsOperativeAct giverInAct giverLack giver ∧
    (∃ z x r, TotallyHolds giver z x r ∧ giverInAct x r ∧ giverLack.CanLack x r) ∧
    (∃ x r, (0 : Fin 2) ≠ x ∧ giver.ActualizesNow 0 x r) ∧
    (∀ r, ¬ HeldMotion giverInAct giver 0 r) ∧
    AdoptedPotency.InPotency giverInAct giverCanBe 0 2 ∧
    ¬ PotencyBringsLackableBeing giverInAct giverCanBe giverLack 0 ∧
    ¬ EveryUnheldHolderIsPureAct giverInAct giverCanBe giver) ∧
  (PotencyBringsLackableBeing giverInAct heldCanBe giverLack 0 ∧
    LackableBeingIsHeld giverInAct giverLack giver 0 ∧
    AdoptedPotency.InPotency giverInAct heldCanBe 1 2)

end Control

end TruthCore.Causality.TotalHolding
