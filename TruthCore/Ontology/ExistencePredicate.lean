module

public import Mathlib.Data.Set.Insert
public import TruthCore.Case.Catholicism.Root
public import TruthCore.Case.Catholicism.StageOneQuartaVia

/-!
# Existence as a predicate: definitional truth and nuclear characterization

Analyst formulations; historical attribution is deferred. Author names are
navigation, not verified source claims.

**1. The definitional argument** (owner-specified analyst formulation):
P1 "I define the existing omnibenevolent God"; P2 "whatever is defined is true";
C "the omnibenevolent God exists". A `DefinitionalFrame` has describable objects,
an existence predicate `Existent` that marks which of them are beings (the beings
over which the root's `GodExists` quantifies), and a primitive `Defined` saying
which descriptions have been introduced by a definitional act. P2 has a weak
version (`DefinitionsAreTrue`: every *defined* description is satisfied) and an
unrestricted version (`UnrestrictedCharacterization`: every description is
satisfied). `DefinitionalTruthRetorsion` is the guard: the unrestricted version
fails, and the weak version fails as soon as the contrary description "the
existing being that is the only God and is *not* omnibenevolent" is defined by
the same kind of act, although each of the two descriptions is satisfiable on
its own. An inconsistent background supports no conclusion, so the argument
gives no warrant: existence cannot be put into a description and taken out
again as a fact.

**2. Nuclear characterization** (a reconstruction in the style of Parsons 1980
of Meinong's *Gegenstandstheorie*; not the naive P2 and not attributed to
Meinong): objects have nuclear (constitutive) properties; for every set of
nuclear properties exactly one object has exactly those nuclear properties.
Extranuclear existence (`ParsonsFrame.ExistsExtranuclear`, EXISTENCE_4) is not a
nuclear property, so it cannot be put into a characterizing set; only the
watered-down nuclear "existent" (`NuclearExistent`, EXISTENCE_5) can.
`NuclearCharacterizationControl` shows that the restricted principle delivers
an object with the nuclear properties god, omnibenevolent and existent, while a
model of the principle has no extranuclear-existent god. Read as a definitional
frame whose admissible definitions are the nuclear descriptions, the model
satisfies the weak P2 but not P1, and the root-style existence claim fails. Read
with "in act at esse" taken nuclearly, the model also satisfies the naming
premise `GodNamesTheUniqueMaximeEns` and has a maximum in being, still with no
extranuclear-existent god: the naming premise carries no existential import of
its own.
-/

@[expose] public section

namespace TruthCore.Ontology.ExistencePredicate

open TruthCore.Case.Catholicism (GodExists GodNamesTheUniqueMaximeEns)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)

/-! ## 1. The definitional argument and its retorsion -/

/-- A frame for reasoning from definitions. `Object` is everything a description
can be about. `Existent x` says that `x` is among the beings (the domain the
root's existence claims quantify over). `Defined D` is primitive: the description
`D` has been introduced by a definitional act (stipulated). Nothing relates
`Defined` to satisfaction or to existence; that relation is what P2 asserts. -/
structure DefinitionalFrame where
  Object : Type
  Existent : Object → Prop
  Defined : (Object → Prop) → Prop

/-- The beings of a definitional frame: the objects that exist. The root's
`GodExists` is read over this domain. -/
abbrev Beings (F : DefinitionalFrame) : Type := {x : F.Object // F.Existent x}

/-- The description P1 introduces: an existing object that is God and is
omnibenevolent. `IsGod` and `OB` are arbitrary predicates of objects; the
argument's validity and its retorsion do not depend on their content. -/
def existingOmnibenevolentGod (F : DefinitionalFrame) (IsGod OB : F.Object → Prop) :
    F.Object → Prop :=
  fun x => F.Existent x ∧ IsGod x ∧ OB x

/-- P1: the description "existing, God, omnibenevolent" has been defined. -/
def DefinesExistingOmnibenevolentGod (F : DefinitionalFrame) (IsGod OB : F.Object → Prop) :
    Prop :=
  F.Defined (existingOmnibenevolentGod F IsGod OB)

/-- P2, weak version: whatever is defined is true, i.e. every description that
has been defined is satisfied by some object. -/
def DefinitionsAreTrue (F : DefinitionalFrame) : Prop :=
  ∀ D, F.Defined D → ∃ x, D x

/-- P2, unrestricted version (the unrestricted characterization principle):
every description of objects whatever is satisfied by some object. It does not
mention `Defined`: any description could be stipulated. -/
def UnrestrictedCharacterization (F : DefinitionalFrame) : Prop :=
  ∀ D : F.Object → Prop, ∃ x, D x

/-- The description "the existing being that is the only God and has `Q`". -/
def existingSoleGodWith (F : DefinitionalFrame) (IsGod Q : F.Object → Prop) :
    F.Object → Prop :=
  fun x => F.Existent x ∧ IsGod x ∧ (∀ y, IsGod y → y = x) ∧ Q x

/-- The retorsion guard on P2. (a) The unrestricted principle is false in every
definitional frame. (b) In every frame, if "the existing being that is the only
God and is omnibenevolent" and "the existing being that is the only God and is
not omnibenevolent" have both been defined, whatever-is-defined-is-true fails.
(c) Each of the two descriptions is satisfied in some frame (not in the same
frame, by (b)), so the clash is not the self-contradiction of a single
description. -/
def DefinitionalTruthRetorsion : Prop :=
  (∀ F : DefinitionalFrame, ¬ UnrestrictedCharacterization F) ∧
  (∀ (F : DefinitionalFrame) (IsGod OB : F.Object → Prop),
    F.Defined (existingSoleGodWith F IsGod OB) →
    F.Defined (existingSoleGodWith F IsGod (fun x => ¬ OB x)) →
    ¬ DefinitionsAreTrue F) ∧
  (∃ (F : DefinitionalFrame) (IsGod OB : F.Object → Prop) (x : F.Object),
    existingSoleGodWith F IsGod OB x) ∧
  (∃ (F : DefinitionalFrame) (IsGod OB : F.Object → Prop) (x : F.Object),
    existingSoleGodWith F IsGod (fun y => ¬ OB y) x)

/-! ## 2. Nuclear characterization (Parsons-style reconstruction) -/

/-- A frame for a nuclear-property object theory, in the style of Parsons 1980.
`Nuclear` are the nuclear (constitutive) properties, such as being golden or
being a mountain; `HasNuclear x p` says that object `x` has nuclear property
`p`. `ExistsExtranuclear x` (EXISTENCE_4) is existence as an extranuclear
property: not a member of `Nuclear`, so no characterizing set contains it.
`existentNuclear` is the watered-down nuclear "existent" (EXISTENCE_5): a nuclear
property that can be part of a characterization. No relation between the two
existences is assumed. -/
structure ParsonsFrame where
  Object : Type
  Nuclear : Type
  HasNuclear : Object → Nuclear → Prop
  ExistsExtranuclear : Object → Prop
  existentNuclear : Nuclear

/-- EXISTENCE_5: having the watered-down nuclear property "existent". -/
def NuclearExistent (F : ParsonsFrame) (x : F.Object) : Prop :=
  F.HasNuclear x F.existentNuclear

/-- The set of nuclear properties of an object. -/
def nuclearSet (F : ParsonsFrame) (x : F.Object) : Set F.Nuclear :=
  {p | F.HasNuclear x p}

/-- The characterization principle restricted to nuclear properties: for every
set of nuclear properties there is exactly one object whose nuclear properties
are exactly that set. -/
def NuclearCharacterization (F : ParsonsFrame) : Prop :=
  ∀ S : Set F.Nuclear, ∃! x, nuclearSet F x = S

/-- A nuclear description: "has (at least) the nuclear properties in `S`". These
are the descriptions the restricted principle admits as characterizations. -/
def nuclearDescription (F : ParsonsFrame) (S : Set F.Nuclear) : F.Object → Prop :=
  fun x => S ⊆ nuclearSet F x

/-- The definitional frame of a nuclear-property theory: its existence predicate
is extranuclear existence, and its admissible definitions are exactly the
nuclear descriptions. -/
def nuclearDefinitionalFrame (F : ParsonsFrame) : DefinitionalFrame where
  Object := F.Object
  Existent := F.ExistsExtranuclear
  Defined := fun D => ∃ S, D = nuclearDescription F S

/-- What nuclear characterization delivers for the definitional argument, and
what it blocks.

(a) In every frame satisfying the principle, for any nuclear properties `g`
(god) and `o` (omnibenevolent) some object has `g`, `o` and nuclear existence
(EXISTENCE_5).

(b) Some frame satisfies the principle, has extranuclear-existent objects, and
for some `g`, `o`: a nuclear-existent object with `g` and `o` exists as an object,
no object with `g` exists extranuclearly (EXISTENCE_4), the weak P2 holds of its
nuclear definitional frame, P1 fails there (the existing-God description is not
a nuclear description), and the root-style claim that some being is a god
fails.

(c) In the same frame, reading "in act at esse" as nuclear existence, the
naming premise `GodNamesTheUniqueMaximeEns` holds for the god predicate, some
object is the unique maximum in being and causes all in that genus, and some
object is a god, while no extranuclear-existent object is a god. -/
def NuclearCharacterizationControl : Prop :=
  (∀ F : ParsonsFrame, NuclearCharacterization F →
    ∀ g o : F.Nuclear, ∃ x, F.HasNuclear x g ∧ F.HasNuclear x o ∧ NuclearExistent F x) ∧
  (∃ F : ParsonsFrame, NuclearCharacterization F ∧ (∃ x, F.ExistsExtranuclear x) ∧
    ∃ g o : F.Nuclear,
      (∃ x, F.HasNuclear x g ∧ F.HasNuclear x o ∧ NuclearExistent F x) ∧
      (¬ ∃ x, F.ExistsExtranuclear x ∧ F.HasNuclear x g) ∧
      DefinitionsAreTrue (nuclearDefinitionalFrame F) ∧
      ¬ DefinesExistingOmnibenevolentGod (nuclearDefinitionalFrame F)
          (fun x => F.HasNuclear x g) (fun x => F.HasNuclear x o) ∧
      ¬ GodExists (fun b : Beings (nuclearDefinitionalFrame F) => F.HasNuclear b.1 g) ∧
      (∃ (MoreIn : Unit → F.Object → F.Object → Prop)
          (CausesIn : F.Object → F.Object → Unit → Prop),
        GodNamesTheUniqueMaximeEns (fun x (_ : Unit) => NuclearExistent F x) MoreIn CausesIn ()
          (fun x => F.HasNuclear x g) ∧
        (∃ m, IsMaximumIn (fun x (_ : Unit) => NuclearExistent F x) MoreIn () m ∧
          CausesAllInGenus (fun x (_ : Unit) => NuclearExistent F x) CausesIn () m ∧
          ∀ m', IsMaximumIn (fun x (_ : Unit) => NuclearExistent F x) MoreIn () m' → m' = m) ∧
        GodExists (fun x => F.HasNuclear x g) ∧
        ¬ ∃ x, F.ExistsExtranuclear x ∧ F.HasNuclear x g))

end TruthCore.Ontology.ExistencePredicate
