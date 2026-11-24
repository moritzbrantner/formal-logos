module

public import TruthCore.Causality.HolderRootIdentification

/-!
# Deriving NAR from the root's withholding and a grounding-to-giving bridge (#1926 phase 3)

Analyst formulations, attribution deferred (logic first). #1944
(`TruthCore.Causality.HolderRootIdentification`) identifies the holder of the
power for the actual contingents' joint absence with the actual root, using
one open premise, NAR (`NecessaryActualConcretaAreRoots`, `43651417`): every
NECESSARY_2 actual concretum has no actual concrete `G`-ground. That note's
gap 1 asks whether NAR can be derived from

* **(a)** the root withholds, at some accessible world where it exists, its
  giving of being to each actual concretum it grounds
  (`ActualRootsWithholdEachGrounded`), and
* **(b)** the explicit `G`-to-giving bridge: an actual concrete `G`-ground of
  `x` gives `x` being at `w` and at every accessible world where `x` exists
  (`ActualGroundsGiveWhereverGroundedExists`).

and whether (a) itself follows from one power, an invariant set-up and
simplicity through a *uniform mode of giving* (#1897 gap 6).

**Relations kept distinct (rigor contract 5 of #1926; #1626).** `G` stays a
parameter of the profile `groundProfile F concrete G`. Giving is the frame's
`GivesAt`, through #1897's `GivesTo`. The only premise that joins them is
(b), stated as an open bridge. The new primitive `EndRequires` (what a
being's own end, its good, cannot be had without) is a parameter, related to
giving only by the open premise `RationalFixedGivingIsRequired`.

**Modes of giving toward one effect.** `FixedTowardAt` (NECESSITATE_5: giving
`x` being at `w` and at every accessible world where the giver exists) and
`TwoWayTowardAt` (giving `x` being at `w` and withholding it at an accessible
world where the giver exists) are per-effect refinements of #1897's
`FixedGiver` and `TwoWayGiverAt` (law 1). `UniformGivingModeAt` says that a
giver that is two-way toward one effect is two-way toward each effect it
gives.

Every model is a finite structural surrogate on #1897's frames; it witnesses
only its formal interpretation, never metaphysical possibility. See
`docs/notes/nar-derivation.md`.
-/

@[expose] public section

namespace TruthCore.Causality.NarDerivation

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.PrussPowerPremises (GivesTo TwoWayGiverAt GivenExists)
open TruthCore.Causality.WillVersusChance (AgencyFrame OnePower)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

variable {W B T R S P : Type}

/-! ## Modes of giving toward one effect -/

/-- NECESSITATE_5, FIXED TOWARD ONE EFFECT from `w`: `y` gives `x` being at
`w` (`GivesTo`, DEF `62dfa893`) and at every world accessible from `w` where
`y` exists. The per-effect, accessible-world form of #1897's `FixedGiver`
(NECESSITATE_2, which fixes *all* of a giver's effects across *all* worlds
where it exists). Example: on Avicenna's account, the First's giving being to
the first intelligence. Non-example: a craftsman's building of one house. -/
def FixedTowardAt (F : CausalityFrame W B T R) (w : W) (y x : B) : Prop :=
  GivesTo F w y x ∧
    ∀ v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y → GivesTo F v y x

/-- TWO-WAY TOWARD ONE EFFECT at `w`: `y` exists at `w`, gives `x` being at
`w`, and at some world accessible from `w` where `y` exists does not give `x`
being. The per-effect form of #1897's `TwoWayGiverAt` (law 1: a two-way giver
is exactly a being two-way toward some effect). It says nothing about what
decides the difference (choice, chance or an external condition). -/
def TwoWayTowardAt (F : CausalityFrame W B T R) (w : W) (y x : B) : Prop :=
  F.history.ontic.ExistsAt w y ∧ GivesTo F w y x ∧
    ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v y ∧ ¬ GivesTo F v y x

/-- UNIFORM MODE OF GIVING at `w`: if `y` is two-way toward some effect at
`w`, it is two-way toward every being it gives at `w`. A giver fixed toward
one effect and two-way toward another (a *mixed-mode* giver) violates it; a
giver fixed toward all its effects satisfies it vacuously. -/
def UniformGivingModeAt (F : CausalityFrame W B T R) (w : W) (y : B) : Prop :=
  (∃ x, TwoWayTowardAt F w y x) → ∀ x, GivesTo F w y x → TwoWayTowardAt F w y x

/-! ## Premises (all OPEN) -/

/-- OPEN bridge (b), from `G`-grounding to giving (rigor contract 5): whatever
is an actual concrete `G`-ground of `x` at `w` gives `x` being at `w` if `x`
exists there, and at every world accessible from `w` where `x` exists.

Two components, both carried here: (b1) the *local* bridge, that a
`G`-ground gives its grounded being being (grounding read as productive
dependence for being, the sustaining CAUSE_OF_BEING sense of `88a8fba7`); and
(b2) *rigidity of the actual ground's giving*: the being that grounds `x` at
`w` gives `x` being wherever `x` exists (necessity of origin, conservation by
the same source). Classical theism and Avicenna's emanation both accept it:
God conserves each creature wherever it exists; the First gives the first
intelligence being in every world. Its rival is a non-productive reading of
`G` (grounding as metaphysical dependence without giving, e.g. a set on its
members), under which (b1) fails. -/
def ActualGroundsGiveWhereverGroundedExists (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ y x, ActualConcreteGround (groundProfile F concrete G) w y x →
    (F.history.ontic.ExistsAt w x → GivesTo F w y x) ∧
    ∀ v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v x → GivesTo F v y x

/-- OPEN premise (a), the root withholds each grounded being somewhere: for
every actual root `n` of `G` at `w` and every actual concretum `x` that `n`
grounds at `w`, there is a world accessible from `w` where `n` exists and does
not give `x` being. #1897's two-way profile extended from the giving of the
actual contingents to every being the root grounds, including any
putatively necessary one; close to the theist-internal free-creation premise
(ST I q.19 a.3, navigation). Under (b), factive giving, a common root and
necessary roots and excluded middle it is equivalent to NAR (`Model.Laws` 3): it relocates NAR into
the giving register; it is not additional evidence for it. -/
def ActualRootsWithholdEachGrounded (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ n x, ActualRoot (groundProfile F concrete G) w n →
    ActualConcrete (groundProfile F concrete G) w x →
    ActualConcreteGround (groundProfile F concrete G) w n x →
    ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v n ∧ ¬ GivesTo F v n x

/-- OPEN: every actual root of `G` at `w` is NECESSARY_2 at `w` (exists at every
accessible world). Universal over actual roots; with a common root it is the
necessity of that one root. Its warrant is that of the necessary-root routes
(e.g. the necessary-root trilemma of `NecessaryRootFork`), not assessed here. -/
def ActualRootsNecessary (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ n, ActualRoot (groundProfile F concrete G) w n → NecessaryAt F.history.ontic w n

/-- OPEN (uniformity at the root): every actual root of `G` at `w` gives in a
uniform mode (`UniformGivingModeAt`). Not entailed by one power, an invariant
set-up and willed (rational) exercise (`Model.MixedModeRoot`). -/
def ActualRootsGiveUniformly (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ n, ActualRoot (groundProfile F concrete G) w n → UniformGivingModeAt F w n

/-- OPEN (power-level simplicity at the root): every actual root of `G` at `w`
has one power (#1941 `OnePower`; ST I q.19 a.4 ad 4, navigation). The root
counterpart of #1941's holder premise `9856239a`. -/
def ActualRootsOnePower (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (concrete : B → Prop) (G : W → B → B → Prop) (w : W) : Prop :=
  ∀ n, ActualRoot (groundProfile F concrete G) w n → OnePower A n

/-- OPEN (WN, a rational power is fixed only toward what its end requires): if
`y` gives `x` being at `w` by exercising a rational power and is fixed toward
`x` from `w` (NECESSITATE_5), then `x` is required by `y`'s own end
(`EndRequires y x`). The structure of ST I q.19 a.3 co. (navigation, not
attributed): the will has a necessary relation to its end and to what the end
cannot be had without, but not to other things. Rivals: the necessary
diffusion of the good (Neoplatonic emanation; Avicenna's First, whose
consenting will is necessitated toward its effects), and the moral necessity
of choosing the best (Leibniz; Rowe's argument that a perfectly good creator
is not free). Both hold that a perfect will is fixed toward effects that its
own good does not require. -/
def RationalFixedGivingIsRequired (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
    (EndRequires : B → B → Prop) (w : W) : Prop :=
  ∀ y p x, A.PowerOf y p → A.Rational p → A.Exercises w y x p → FixedTowardAt F w y x →
    EndRequires y x

/-- OPEN (SS, self-sufficiency of the root's end): no being other than an
actual root of `G` at `w` is required by that root's end. The aseity of the
root's good: "His goodness can be without other things, ... no perfection can
accrue to Him from them" (ST I q.19 a.3 co., navigation). Avicenna's First is
self-sufficient in the same sense; the emanationist rival denies WN, not SS. -/
def ActualRootsEndRequiresNoOther (F : CausalityFrame W B T R) (concrete : B → Prop)
    (G : W → B → B → Prop) (EndRequires : B → B → Prop) (w : W) : Prop :=
  ∀ n x, ActualRoot (groundProfile F concrete G) w n → x ≠ n → ¬ EndRequires n x

/-! ## Laws and models -/

namespace Model

open TruthCore.Causality.HolderRootIdentification (NecessaryActualConcretaAreRoots
  ActualAbsenceHoldersExistAt ActualAbsenceHoldersAreActualRoots)
open TruthCore.Causality.HolderRootIdentification.Model (gdEx gGroundsOthers gdWithholdG dPower)
open TruthCore.Modal.PrussPowerPremises.Model (Bg Bg.forall_iff Bg.exists_iff gFrame theistG
  allC uni gcEx gcAlways givesCHere)
open TruthCore.Causality.WillVersusChance (SetupInvariantAt WilledTwoWayAt
  OnePowerIntellectualGivingWilled)
open TruthCore.Causality.WillVersusChance.Model (onlyG nobody simpleRational twoPowerChancer)
open TruthCore.Causality.RootPositiveIntellectWill (IntellectualGodCommonRootAt)
open TruthCore.Modal.ModalGrounding (SomeContingentConcreteAt ActualAbsenceInitiatorPresent
  ActualAbsencePowerHoldersConcrete)
open TruthCore.Modal.PrussPowerPremises (ActualAbsenceHoldersGiveEach)

/-- General laws.

1. **Two-way givers.** `y` is a two-way giver at `w` (#1897) exactly when it is
   two-way toward some effect.
2. **The root is two-way toward the contingents.** With (b), factive giving, a
   common root, necessary roots and some concrete contingent being at `w`,
   every actual root is two-way toward some concrete contingent being. Derived
   without #1897's holder premises: what (a) adds is only the extension to
   every grounded being.
3. **Relocation.** With (b), factive giving, a common root, necessary roots and
   excluded middle, NAR holds exactly when (a) does. So (a) is NAR in the
   giving register: given these premises it adds no evidence for NAR.
4. **Simplicity at the level of exercise forces uniform *fixity*.** If `y`
   exercises toward each effect at every accessible world where it exists
   whatever it exercises toward it at `w`, every exercise is a giving, and
   every giving at `w` exercises a power, then `y` is two-way toward nothing.
   The agency-overlay counterpart of #555 `SimplicityCollapse.rigid_core`
   (one act carried by the being, strict efficacy): such simplicity makes the
   mode uniform only by collapse, which law 2 excludes at the root.
5. **The will route under reflexive access.** If `w` is accessible from
   itself, (a) follows from excluded middle, the common GOD_4 root with
   intellect (`0c27f65a`), #1941's willed giving of a one-power intellectual
   being (`5c1aba17`), roots with one power, WN and SS, without (b). -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (y : B),
    TwoWayGiverAt F w y ↔ ∃ x, TwoWayTowardAt F w y x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop)
      (G : W → B → B → Prop) (w : W),
    ActualGroundsGiveWhereverGroundedExists F concrete G w → GivenExists F →
    ActualCommonRootAt (groundProfile F concrete G) w → ActualRootsNecessary F concrete G w →
    SomeContingentConcreteAt F concrete w →
    ∀ n, ActualRoot (groundProfile F concrete G) w n →
      ∃ c, concrete c ∧ ContingentAt F.history.ontic w c ∧ TwoWayTowardAt F w n c) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (concrete : B → Prop)
      (G : W → B → B → Prop) (w : W),
    TruthCore.Logic.ExcludedMiddle →
    ActualGroundsGiveWhereverGroundedExists F concrete G w → GivenExists F →
    ActualCommonRootAt (groundProfile F concrete G) w → ActualRootsNecessary F concrete G w →
    (NecessaryActualConcretaAreRoots (groundProfile F concrete G) w ↔
      ActualRootsWithholdEachGrounded F concrete G w)) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P) (w : W) (y : B),
    (∀ v x p, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v y →
      A.Exercises w y x p → A.Exercises v y x p) →
    (∀ v x p, A.Exercises v y x p → GivesTo F v y x) →
    (∀ x, GivesTo F w y x → ∃ p, A.PowerOf y p ∧ A.Exercises w y x p) →
    ∀ x, ¬ TwoWayTowardAt F w y x) ∧
  (∀ (W B T R S P : Type) (F : CausalityFrame W B T R) (A : AgencyFrame W B S P)
      (concrete IsGod HasIntellect : B → Prop) (G : W → B → B → Prop)
      (EndRequires : B → B → Prop) (w : W),
    F.history.ontic.frame.access w w → TruthCore.Logic.ExcludedMiddle →
    IntellectualGodCommonRootAt (groundProfile F concrete G) w IsGod HasIntellect →
    OnePowerIntellectualGivingWilled F A HasIntellect → ActualRootsOnePower F A concrete G w →
    RationalFixedGivingIsRequired F A EndRequires w →
    ActualRootsEndRequiresNoOther F concrete G EndRequires w →
    ActualRootsWithholdEachGrounded F concrete G w)

/-! ### Frames on #1897's three candidates (`Bg`: `g`, `c`, `d`; actual world `false`) -/

/-- The mixed-mode giving: `g` gives `d` being at both worlds; `g` and `d` give
`c` being at `false` only. -/
def mixedGives (v : Bool) (y x : Bg) : Prop :=
  (y = .g ∧ x = .d) ∨ ((y = .g ∨ y = .d) ∧ x = .c ∧ v = false)

/-- Necessary `g` and `d`, contingent `c`, with the mixed-mode giving. -/
def mixedG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx mixedGives

/-- `g` and `d` each have one constant state and one rational power, exercised
in all of their giving; no external conditions. -/
def rationalGD : AgencyFrame Bool Bg Unit Unit where
  StateAt := fun _ y _ => y ≠ .c
  ConditionOf := fun _ _ _ => False
  PowerOf := fun y _ => y ≠ .c
  Rational := fun _ => True
  Exercises := fun _ y _ _ => y ≠ .c

/-- As `rationalGD` with the powers non-rational: natural emanation. -/
def naturalGD : AgencyFrame Bool Bg Unit Unit := rationalGD.reclassify fun _ => False

/-- Nothing is required by anything's end. -/
def noRequirement (_ _ : Bg) : Prop := False

/-- `g`'s end requires `d`. -/
def gRequiresD (y x : Bg) : Prop := y = .g ∧ x = .d

/-- `g` and `d` ground each other, at every world. -/
def mutualGD (_ : Bool) (y x : Bg) : Prop := (y = .g ∧ x = .d) ∨ (y = .d ∧ x = .g)

/-- `g` and `d` give each other being at every world; nothing gives `c`. -/
def mutualG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx mutualGD

/-- `g` gives `d` being at both worlds, and nothing else. -/
def gGivesD (_ : Bool) (y x : Bg) : Prop := y = .g ∧ x = .d

/-- `g` gives `d` being fixedly and gives `c` nothing. -/
def fixedDG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx gGivesD

/-- `g` gives every other being being at both worlds, also where `c` is absent. -/
def gGivesOthers (_ : Bool) (y x : Bg) : Prop := y = .g ∧ x ≠ .g

/-- Non-factive giving: `g` gives `c` being at `true`, where `c` is absent. -/
def nonFactiveMixedG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx gGivesOthers

/-- Everything exists at `false` only. -/
def onlyFalseEx (v : Bool) (_ : Bg) : Prop := v = false

/-- `g` gives every other being being at `false` only. -/
def gGivesOthersHere (v : Bool) (y x : Bg) : Prop := y = .g ∧ x ≠ .g ∧ v = false

/-- A contingent root: `g`, `c`, `d` exist at `false` only; `g` gives `c` and
`d` being there. -/
def contingentRootG : CausalityFrame Bool Bg Unit Bool := gFrame uni onlyFalseEx gGivesOthersHere

/-- `g` and `d` at both worlds; `c` nowhere. -/
def noCEx (_ : Bool) (x : Bg) : Prop := x ≠ .c

/-- No contingent being: `g` and `d` at both worlds, `g` gives `d` being. -/
def noContingentG : CausalityFrame Bool Bg Unit Bool := gFrame uni noCEx gGivesD

/-- The chain `d → g → c` at every world. -/
def chainGrounds (_ : Bool) (y x : Bg) : Prop := (y = .d ∧ x = .g) ∨ (y = .g ∧ x = .c)

/-- `d` gives `g` being at both worlds; `g` gives `c` being at `false` only. -/
def chainGives (v : Bool) (y x : Bg) : Prop :=
  (y = .d ∧ x = .g) ∨ (y = .g ∧ x = .c ∧ v = false)

/-- A mediated creator: the root `d` gives the necessary `g` being, which gives
the contingent `c` being. -/
def chainG : CausalityFrame Bool Bg Unit Bool := gFrame uni gdEx chainGives

/-- Access from every world to `true` only (not reflexive at `false`). -/
def toTrue (_ v : Bool) : Prop := v = true

/-- `g` gives `c` being at `true` only. -/
def givesCThere (v : Bool) (y x : Bg) : Prop := y = .g ∧ x = .c ∧ v = true

/-- `g` and `c` at both worlds; from `false` only `true` is accessible; `g`
gives `c` being at `true` only. -/
def toTrueG : CausalityFrame Bool Bg Unit Bool := gFrame toTrue gcAlways givesCThere

/-- **Theist nonvacuity** (`theistG`, `g` grounds every other being,
`simpleRational`, intellect and GOD_4 at `g`, nothing required; actual world
`false`): every premise and conclusion of arguments N1–N3 holds. -/
def TheistNonvacuity : Prop :=
  TruthCore.Logic.ExcludedMiddle ∧
  ActualCommonRootAt (groundProfile theistG allC gGroundsOthers) false ∧
  ActualGroundsGiveWhereverGroundedExists theistG allC gGroundsOthers false ∧
  GivenExists theistG ∧
  ActualRootsNecessary theistG allC gGroundsOthers false ∧
  SomeContingentConcreteAt theistG allC false ∧
  ActualRootsGiveUniformly theistG allC gGroundsOthers false ∧
  IntellectualGodCommonRootAt (groundProfile theistG allC gGroundsOthers) false onlyG onlyG ∧
  OnePowerIntellectualGivingWilled theistG simpleRational onlyG ∧
  ActualRootsOnePower theistG simpleRational allC gGroundsOthers false ∧
  RationalFixedGivingIsRequired theistG simpleRational noRequirement false ∧
  ActualRootsEndRequiresNoOther theistG allC gGroundsOthers noRequirement false ∧
  ActualRootsWithholdEachGrounded theistG allC gGroundsOthers false ∧
  NecessaryActualConcretaAreRoots (groundProfile theistG allC gGroundsOthers) false

/-- **The mixed-mode root** (`mixedG`, `g` grounds every other being,
`rationalGD`, intellect and GOD_4 at `g`; the holder is `d`): the
necessary-through-another rival of #1944 that *respects* (b). The root `g`
gives the necessary `d` being at both worlds (fixed toward `d`) and the
contingent `c` being at the actual world only (two-way toward `c`), by one
rational power under an invariant set-up, so its giving is willed two-way
giving (#1941). (b), factive giving, the common root, necessary roots, some
contingent, the common GOD_4 root with intellect, #1941's willed giving of a
one-power intellectual being, one power at the root, an invariant set-up and
the holder premises P2′, P3′, holders at `w` and the creator reading all
hold; uniformity, (a), NAR and the holder conclusion of #1944's argument 1
fail. With nothing required, WN fails and SS holds; with `g`'s end requiring
`d`, WN holds and SS fails. So one power, an invariant set-up and willed
exercise do not force a uniform mode of giving. -/
def MixedModeRoot : Prop :=
  ActualGroundsGiveWhereverGroundedExists mixedG allC gGroundsOthers false ∧
  GivenExists mixedG ∧
  ActualCommonRootAt (groundProfile mixedG allC gGroundsOthers) false ∧
  ActualRootsNecessary mixedG allC gGroundsOthers false ∧
  SomeContingentConcreteAt mixedG allC false ∧
  IntellectualGodCommonRootAt (groundProfile mixedG allC gGroundsOthers) false onlyG onlyG ∧
  OnePowerIntellectualGivingWilled mixedG rationalGD onlyG ∧
  ActualRootsOnePower mixedG rationalGD allC gGroundsOthers false ∧
  SetupInvariantAt mixedG rationalGD false .g ∧
  WilledTwoWayAt mixedG rationalGD false .g ∧
  ActualAbsenceInitiatorPresent mixedG dPower allC false ∧
  ActualAbsencePowerHoldersConcrete mixedG dPower allC false ∧
  ActualAbsenceHoldersExistAt mixedG dPower allC false ∧
  ActualAbsenceHoldersGiveEach mixedG dPower allC false ∧
  FixedTowardAt mixedG false .g .d ∧ TwoWayTowardAt mixedG false .g .c ∧
  ¬ UniformGivingModeAt mixedG false .g ∧
  ¬ ActualRootsGiveUniformly mixedG allC gGroundsOthers false ∧
  ¬ ActualRootsWithholdEachGrounded mixedG allC gGroundsOthers false ∧
  ¬ NecessaryActualConcretaAreRoots (groundProfile mixedG allC gGroundsOthers) false ∧
  ¬ ActualAbsenceHoldersAreActualRoots mixedG dPower allC gGroundsOthers false ∧
  ¬ RationalFixedGivingIsRequired mixedG rationalGD noRequirement false ∧
  ActualRootsEndRequiresNoOther mixedG allC gGroundsOthers noRequirement false ∧
  RationalFixedGivingIsRequired mixedG rationalGD gRequiresD false ∧
  ¬ ActualRootsEndRequiresNoOther mixedG allC gGroundsOthers gRequiresD false

/-- **Omission models of argument N1** (NAR from (a), (b) and a common root;
`g` grounds every other being unless stated):

1. without (b) (`gdWithholdG` of #1944): `g` grounds the necessary `d` and
   gives nothing; (a) and the common GOD_4 root with intellect hold, NAR fails;
2. without (a): `MixedModeRoot`;
3. without the common root (`mutualG`, `g` and `d` ground and give each other):
   (a) holds vacuously at the only root `c`, (b) holds, the common root and
   `0c27f65a` fail, NAR fails. -/
def OmissionsN1 : Prop :=
  (ActualCommonRootAt (groundProfile gdWithholdG allC gGroundsOthers) false ∧
    IntellectualGodCommonRootAt (groundProfile gdWithholdG allC gGroundsOthers) false onlyG onlyG ∧
    ActualRootsWithholdEachGrounded gdWithholdG allC gGroundsOthers false ∧
    ¬ ActualGroundsGiveWhereverGroundedExists gdWithholdG allC gGroundsOthers false ∧
    ¬ NecessaryActualConcretaAreRoots (groundProfile gdWithholdG allC gGroundsOthers) false) ∧
  (ActualGroundsGiveWhereverGroundedExists mutualG allC mutualGD false ∧
    ActualRootsWithholdEachGrounded mutualG allC mutualGD false ∧
    ¬ ActualCommonRootAt (groundProfile mutualG allC mutualGD) false ∧
    ¬ IntellectualGodCommonRootAt (groundProfile mutualG allC mutualGD) false onlyG onlyG ∧
    ¬ NecessaryActualConcretaAreRoots (groundProfile mutualG allC mutualGD) false)

/-- **Omission models of argument N2** ((a) from uniformity; `g` grounds every
other being unless stated). Without uniformity: `MixedModeRoot`. In each model
below uniformity holds vacuously (the root is two-way toward nothing) and (a)
fails:

1. without (b) (`fixedDG`): `g` gives only `d`, fixedly, and not `c`;
2. without factive giving (`nonFactiveMixedG`): `g` gives `c` being also where
   `c` is absent;
3. without necessary roots (`contingentRootG`): everything exists at `false`
   only;
4. without some contingent concretum (`noContingentG`);
5. without the common root (`chainG`, the chain `d → g → c`): the root `d`
   gives the necessary `g` being fixedly and gives the contingent `c` nothing;
   a mediated creator. -/
def OmissionsN2 : Prop :=
  (GivenExists fixedDG ∧ ActualCommonRootAt (groundProfile fixedDG allC gGroundsOthers) false ∧
    ActualRootsNecessary fixedDG allC gGroundsOthers false ∧
    SomeContingentConcreteAt fixedDG allC false ∧
    ActualRootsGiveUniformly fixedDG allC gGroundsOthers false ∧
    ¬ ActualGroundsGiveWhereverGroundedExists fixedDG allC gGroundsOthers false ∧
    ¬ ActualRootsWithholdEachGrounded fixedDG allC gGroundsOthers false) ∧
  (ActualGroundsGiveWhereverGroundedExists nonFactiveMixedG allC gGroundsOthers false ∧
    ActualCommonRootAt (groundProfile nonFactiveMixedG allC gGroundsOthers) false ∧
    ActualRootsNecessary nonFactiveMixedG allC gGroundsOthers false ∧
    SomeContingentConcreteAt nonFactiveMixedG allC false ∧
    ActualRootsGiveUniformly nonFactiveMixedG allC gGroundsOthers false ∧
    ¬ GivenExists nonFactiveMixedG ∧
    ¬ ActualRootsWithholdEachGrounded nonFactiveMixedG allC gGroundsOthers false) ∧
  (ActualGroundsGiveWhereverGroundedExists contingentRootG allC gGroundsOthers false ∧
    GivenExists contingentRootG ∧
    ActualCommonRootAt (groundProfile contingentRootG allC gGroundsOthers) false ∧
    SomeContingentConcreteAt contingentRootG allC false ∧
    ActualRootsGiveUniformly contingentRootG allC gGroundsOthers false ∧
    ¬ ActualRootsNecessary contingentRootG allC gGroundsOthers false ∧
    ¬ ActualRootsWithholdEachGrounded contingentRootG allC gGroundsOthers false) ∧
  (ActualGroundsGiveWhereverGroundedExists noContingentG allC gGroundsOthers false ∧
    GivenExists noContingentG ∧
    ActualCommonRootAt (groundProfile noContingentG allC gGroundsOthers) false ∧
    ActualRootsNecessary noContingentG allC gGroundsOthers false ∧
    ActualRootsGiveUniformly noContingentG allC gGroundsOthers false ∧
    ¬ SomeContingentConcreteAt noContingentG allC false ∧
    ¬ ActualRootsWithholdEachGrounded noContingentG allC gGroundsOthers false) ∧
  (ActualGroundsGiveWhereverGroundedExists chainG allC chainGrounds false ∧
    GivenExists chainG ∧
    ¬ IntellectualGodCommonRootAt (groundProfile chainG allC chainGrounds) false onlyG onlyG ∧
    ActualRootsNecessary chainG allC chainGrounds false ∧
    SomeContingentConcreteAt chainG allC false ∧
    ActualRootsGiveUniformly chainG allC chainGrounds false ∧
    ¬ ActualCommonRootAt (groundProfile chainG allC chainGrounds) false ∧
    ¬ ActualRootsWithholdEachGrounded chainG allC chainGrounds false ∧
    ¬ NecessaryActualConcretaAreRoots (groundProfile chainG allC chainGrounds) false)

/-- **Omission models of argument N3** ((a) from the will route; `g` grounds
every other being). Without WN, and without SS: `MixedModeRoot`. In each model
below (a) fails:

1. without #1941's willed giving `5c1aba17` (`mixedG`, `naturalGD`: `g` has
   intellect and one power, but its power is non-rational; natural emanation
   by an intellectual source);
2. without one power at the root (`mixedG`, #1941's `twoPowerChancer`: `g`
   gives by a non-rational second power);
3. without the common GOD_4 root with intellect `0c27f65a` (`mixedG`,
   `naturalGD`, intellect for nobody): an emanating root without intellect;
4. without (b) (`toTrueG`, access from `false` to `true` only): `g` does not
   give `c` being at `false`, where `c` exists, and gives it at the only
   accessible world. Law 5 shows that with reflexive access (b) is idle in
   N3, so this omission needs a non-reflexive frame. -/
def OmissionsN3 : Prop :=
  (IntellectualGodCommonRootAt (groundProfile mixedG allC gGroundsOthers) false onlyG onlyG ∧
    ActualRootsOnePower mixedG naturalGD allC gGroundsOthers false ∧
    ActualGroundsGiveWhereverGroundedExists mixedG allC gGroundsOthers false ∧
    RationalFixedGivingIsRequired mixedG naturalGD noRequirement false ∧
    ActualRootsEndRequiresNoOther mixedG allC gGroundsOthers noRequirement false ∧
    ¬ OnePowerIntellectualGivingWilled mixedG naturalGD onlyG ∧
    ¬ ActualRootsWithholdEachGrounded mixedG allC gGroundsOthers false) ∧
  (IntellectualGodCommonRootAt (groundProfile mixedG allC gGroundsOthers) false onlyG onlyG ∧
    OnePowerIntellectualGivingWilled mixedG twoPowerChancer onlyG ∧
    ActualGroundsGiveWhereverGroundedExists mixedG allC gGroundsOthers false ∧
    RationalFixedGivingIsRequired mixedG twoPowerChancer noRequirement false ∧
    ActualRootsEndRequiresNoOther mixedG allC gGroundsOthers noRequirement false ∧
    ¬ ActualRootsOnePower mixedG twoPowerChancer allC gGroundsOthers false ∧
    ¬ ActualRootsWithholdEachGrounded mixedG allC gGroundsOthers false) ∧
  (OnePowerIntellectualGivingWilled mixedG naturalGD nobody ∧
    ActualRootsOnePower mixedG naturalGD allC gGroundsOthers false ∧
    ActualGroundsGiveWhereverGroundedExists mixedG allC gGroundsOthers false ∧
    RationalFixedGivingIsRequired mixedG naturalGD noRequirement false ∧
    ActualRootsEndRequiresNoOther mixedG allC gGroundsOthers noRequirement false ∧
    ¬ IntellectualGodCommonRootAt (groundProfile mixedG allC gGroundsOthers) false onlyG nobody ∧
    ¬ ActualRootsWithholdEachGrounded mixedG allC gGroundsOthers false) ∧
  (IntellectualGodCommonRootAt (groundProfile toTrueG allC gGroundsOthers) false onlyG onlyG ∧
    OnePowerIntellectualGivingWilled toTrueG simpleRational onlyG ∧
    ActualRootsOnePower toTrueG simpleRational allC gGroundsOthers false ∧
    RationalFixedGivingIsRequired toTrueG simpleRational noRequirement false ∧
    ActualRootsEndRequiresNoOther toTrueG allC gGroundsOthers noRequirement false ∧
    ¬ ActualGroundsGiveWhereverGroundedExists toTrueG allC gGroundsOthers false ∧
    ¬ ActualRootsWithholdEachGrounded toTrueG allC gGroundsOthers false)

/-- The certificate: laws and models. -/
def Controls : Prop :=
  Laws ∧ TheistNonvacuity ∧ MixedModeRoot ∧ OmissionsN1 ∧ OmissionsN2 ∧ OmissionsN3

end Model

end TruthCore.Causality.NarDerivation
