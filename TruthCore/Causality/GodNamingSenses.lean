module

public import TruthCore.Causality.NecessarySenseFork
public import TruthCore.Modal.RigidDesignation

/-!
# Two senses of naming "God" inside a modal context

Analyst formulation, attribution deferred (owner direction on the modal
library, 2026-11-07, and "Logic first", 2026-11-05). This is not a reading of
Kripke's *Naming and Necessity* or of Aquinas; it formalizes the distinction
between a description and a name whose reference a description fixes, and
connects the existing rigid-designation library
(`TruthCore.Modal.RigidDesignation`) to the necessary-being node of the
root route (`NecessaryRootBoxK`).

The naming premises of stage one (`GodNamesTheUniqueMaximeEns`,
`GodNamesTheFullyDescribedPrinciple`, `MaximeEnsIsGod`) are not modal: their
`God` predicate and their description (maximal in being, cause of the being of
all others, ...) are evaluated in one model, with no worlds. The necessary-being
node `NecessaryRootBoxK` puts that God inside a box: some actual root `n` is
GOD_4 (`σ.IsGod n`, a world-invariant predicate) and `n` exists at every
accessible world. Inside a modal context, "God exists necessarily" has two
readings, depending on how the name works at other worlds:

* NAMING_1, descriptive (`DescriptiveName`): at each world `v`, "God" designates
  whatever uniquely satisfies the God-description *at `v`* among what exists at
  `v`. The name is the description; it need not designate the same bearer at
  different worlds.
* NAMING_2, reference-fixed (`ReferenceFixedName`): the description, evaluated at
  the reference world `w₀`, fixes the bearer once; at each world `v` the name
  designates that same bearer when it exists at `v`, whether or not it satisfies
  the description at `v`. Such a name is rigid (`RigidAt`,
  `referenceFixed_rigid`).

A third reading, a name whose *sense* is the description, coincides with
NAMING_1 when the description is evaluated at each world (narrow scope) and with
NAMING_2 when it is evaluated at the reference world (wide scope, "the actual
D"). It has no distinct world-intension, so it is not a separate Lean sense here;
the difference it marks (what is knowable a priori from the name) is not a
modal-semantic difference (attempt record).

The God-description at other worlds is a primitive parameter `GodAt : W → B →
Prop`: `GodAt v x` means that `x` satisfies, at world `v`, the conditions the
name's descriptive content requires (GOD_4's content as it would hold at `v`).
Nothing relates `GodAt` at other worlds to `σ.IsGod`; the two bridges
`NoOtherPossibleGod` and `GodhoodEssentialToGod` state such relations as open
premises.
-/

@[expose] public section

namespace TruthCore.Causality.GodNamingSenses

open TruthCore.Modal.RigidDesignation (Name RigidAt CoRef)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Isabelle.AFP.GoedelGod (Box)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessarySenseFork (RootFacts NecessaryRootBoxK)
open TruthCore.Case.Catholicism (Signature)

variable {W B : Type}

/-- A world-indexed description: `D v x` says that `x` satisfies the
description at world `v`. -/
abbrev Description (W B : Type) := W → B → Prop

/-- `x` is the unique existing satisfier of `D` at `v`: it satisfies `D` at `v`,
exists at `v`, and every satisfier of `D` that exists at `v` is `x` (actualist
uniqueness: candidates absent from `v` do not compete). Shared helper of both
naming senses; it is not itself a sense. -/
def UniqueExistentAt (o : Ontic W B) (D : Description W B) (v : W) (x : B) : Prop :=
  D v x ∧ o.ExistsAt v x ∧ ∀ y, D v y → o.ExistsAt v y → y = x

/-- NAMING_1, descriptive: at each world `v` the name designates the unique
existing satisfier of `D` at `v`. -/
def DescriptiveName (o : Ontic W B) (D : Description W B) : Name W B :=
  fun v x => UniqueExistentAt o D v x

/-- NAMING_2, reference-fixed: the description at the reference world `w₀`
picks the bearer; at each world `v` the name designates that bearer exactly when
it exists at `v`. -/
def ReferenceFixedName (o : Ontic W B) (D : Description W B) (w₀ : W) : Name W B :=
  fun v x => UniqueExistentAt o D w₀ x ∧ o.ExistsAt v x

/-! ## The route's necessary-being node under each naming sense -/

/-- Rigid-name reading of the necessary-being node: some actual root `n` has
the route's root facts (actual root, GOD_4, the one GOD_4, the classical
attributes), and at every world accessible from `w` the name "God",
reference-fixed at `w` by being GOD_4, designates something (strict
co-designation of the name with itself). -/
def NecessaryRootRigidName (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  ∃ n, RootFacts σ m w n ∧
    Box m.ontic.frame
      (CoRef (ReferenceFixedName m.ontic (fun _ => σ.IsGod) w)
        (ReferenceFixedName m.ontic (fun _ => σ.IsGod) w)) w

/-- Descriptive reading of the necessary-being node: some actual root `n` has the
route's root facts, and at every world accessible from `w` the descriptive name
"God" designates something: something existing there uniquely satisfies the
God-description `GodAt` there. It does not say that the satisfier is `n`. -/
def NecessaryRootDescriptiveName (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being) : Prop :=
  ∃ n, RootFacts σ m w n ∧
    Box m.ontic.frame (CoRef (DescriptiveName m.ontic GodAt) (DescriptiveName m.ontic GodAt)) w

/-- Open bridge: nothing could be God (satisfy the God-description at a world
accessible from `w` while existing there) without actually being GOD_4. The
God-description is not satisfiable, at an accessible world, by a being other
than the actual God. -/
def NoOtherPossibleGod (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being) : Prop :=
  ∀ v, m.ontic.frame.access w v → ∀ y, GodAt v y → m.ontic.ExistsAt v y → σ.IsGod y

/-- Open bridge: being God is essential to what is actually GOD_4: whatever is
GOD_4 satisfies the God-description at every world accessible from `w` at which
it exists. -/
def GodhoodEssentialToGod (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being) : Prop :=
  ∀ g, σ.IsGod g → ∀ v, m.ontic.frame.access w v → m.ontic.ExistsAt v g → GodAt v g

/-! ## Laws and controls (premise-free) -/

namespace Control

/-- Universal two-world frame; being `b` exists exactly at world `b`. -/
def swapOntic : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun v b => v = b
  Causes := fun _ _ _ => False

/-- Universal two-world frame; both beings exist at both worlds. -/
def fullOntic : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

/-- A two-being signature: `false` is GOD_4 and has the classical attributes.
The historical and creedal fields are unused placeholders. -/
def boolSignature : Signature where
  Being := Bool
  IsGod := fun b => b = false
  HasClassicalAttributes := fun b => b = false
  RevealsRecognizably := fun _ => False
  jesus := true
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- Profile over `swapOntic`: each being exists only at its own world, every
being is concrete, nothing grounds anything. -/
def swapProfile : Profile Bool boolSignature.Being where
  ontic := swapOntic
  concrete := fun _ => True  -- category-constant: intended (all-concrete two-being inventory: the models test naming and modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- Profile over `fullOntic`. -/
def fullProfile : Profile Bool boolSignature.Being where
  ontic := fullOntic
  concrete := fun _ => True  -- category-constant: intended (all-concrete two-being inventory: the models test naming and modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- Migrating God-description: at world `v` the being `v` satisfies it. -/
def migratingGodAt : Description Bool Bool := fun v b => b = v

/-- Lapsing God-description: only at world `false`, and only by `false`. -/
def lapsingGodAt : Description Bool Bool := fun v b => v = false ∧ b = false

/-- Stable God-description: `false` satisfies it at both worlds. -/
def stableGodAt : Description Bool Bool := fun _ b => b = false

/-- Generic laws of the two naming senses, for every `Ontic` model:
1. a reference-fixed name is rigid (`RigidAt`) at every origin for the unique
   existing satisfier at its reference world;
2. at the reference world the two senses designate the same bearers, so a
   one-world (non-modal) naming premise cannot tell them apart;
3. Kripkean necessity of identity for reference-fixed names: if two
   reference-fixed names designate the same bearer `x` at `w₀`, they
   co-designate at every world accessible from `w₀` at which `x` exists, and
   they co-designate at every accessible world iff `x` exists at every
   accessible world (`NecessaryAt`): necessity of identity, not necessary
   existence. -/
def Laws : Prop :=
  ∀ (W B : Type) (o : Ontic W B) (D D' : Description W B) (w₀ : W) (x : B),
    (UniqueExistentAt o D w₀ x → ∀ w, RigidAt o (ReferenceFixedName o D w₀) w x) ∧
    (∀ y, DescriptiveName o D w₀ y ↔ ReferenceFixedName o D w₀ w₀ y) ∧
    (UniqueExistentAt o D w₀ x → UniqueExistentAt o D' w₀ x →
      (∀ v, o.frame.access w₀ v → o.ExistsAt v x →
        CoRef (ReferenceFixedName o D w₀) (ReferenceFixedName o D' w₀) v) ∧
      (Box o.frame (CoRef (ReferenceFixedName o D w₀) (ReferenceFixedName o D' w₀)) w₀ ↔
        NecessaryAt o w₀ x))

/-- The rigid-name reading is exactly the route's de re box node: for every
signature, profile and origin, `NecessaryRootRigidName` iff `NecessaryRootBoxK`
(for any `CN`, which the box node does not use). -/
def RigidIffBoxK : Prop :=
  ∀ (W : Type) (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop),
    NecessaryRootRigidName σ m w ↔ NecessaryRootBoxK σ m w CN

/-- Separating controls on explicit two-world models (reference world `false`):
1. migrating description (`swapProfile`, `migratingGodAt`): the descriptive
   node holds, the box node fails, and `NoOtherPossibleGod` fails (the
   descriptive reading's "God exists necessarily" does not give a necessarily
   existing actual God without that bridge);
2. lapsing description (`fullProfile`, `lapsingGodAt`): the box node and
   `NoOtherPossibleGod` hold, the descriptive node fails, and
   `GodhoodEssentialToGod` fails (the actual God's necessary existence does not
   give the descriptive reading without that bridge);
3. naming senses separate: in the migrating model, at world `true`, the
   descriptive name designates `true` and the reference-fixed name designates
   nothing;
4. identity: in `fullOntic`, the descriptive names for `stableGodAt` and
   `migratingGodAt` co-designate `false` at `false`, that bearer exists at
   `true`, and they do not co-designate at `true` (each designates a different
   being there); the names reference-fixed at `false` by the same two
   descriptions do co-designate at `true`. -/
def Separation : Prop :=
  (NecessaryRootDescriptiveName boolSignature swapProfile false migratingGodAt ∧
    ¬ NecessaryRootBoxK boolSignature swapProfile false (fun _ _ => False) ∧
    ¬ NoOtherPossibleGod boolSignature swapProfile false migratingGodAt) ∧
  (NecessaryRootBoxK boolSignature fullProfile false (fun _ _ => False) ∧
    NoOtherPossibleGod boolSignature fullProfile false lapsingGodAt ∧
    ¬ NecessaryRootDescriptiveName boolSignature fullProfile false lapsingGodAt ∧
    ¬ GodhoodEssentialToGod boolSignature fullProfile false lapsingGodAt) ∧
  (DescriptiveName swapOntic migratingGodAt true true ∧
    ∀ y, ¬ ReferenceFixedName swapOntic migratingGodAt false true y) ∧
  (CoRef (DescriptiveName fullOntic stableGodAt) (DescriptiveName fullOntic migratingGodAt) false ∧
    fullOntic.ExistsAt true false ∧
    ¬ CoRef (DescriptiveName fullOntic stableGodAt) (DescriptiveName fullOntic migratingGodAt) true ∧
    CoRef (ReferenceFixedName fullOntic stableGodAt false)
      (ReferenceFixedName fullOntic migratingGodAt false) true)

/-- Nonvacuity: in `fullProfile` with a stable God-description (`false` at both
worlds), the rigid node, the descriptive node and both bridges hold together. -/
def Nonvacuity : Prop :=
  NecessaryRootRigidName boolSignature fullProfile false ∧
  NecessaryRootDescriptiveName boolSignature fullProfile false stableGodAt ∧
  NoOtherPossibleGod boolSignature fullProfile false stableGodAt ∧
  GodhoodEssentialToGod boolSignature fullProfile false stableGodAt

/-- The premise-free certificate of this module. -/
def Checks : Prop := Laws ∧ RigidIffBoxK ∧ Separation ∧ Nonvacuity

end Control

end TruthCore.Causality.GodNamingSenses
