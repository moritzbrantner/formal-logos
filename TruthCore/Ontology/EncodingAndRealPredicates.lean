module

public import Mathlib.Data.Set.Insert
public import TruthCore.Ontology.ExistencePredicate
public import TruthCore.German.Kant.CosmologicalInference

/-!
# Existence as a predicate, part 2: encoding, real predicates, Meditation V

Analyst formulations; historical attribution is deferred. Author names (Zalta,
Kant, Descartes) are navigation, not verified source claims. Part 1 is
`TruthCore.Ontology.ExistencePredicate`.

**1. Encoding and exemplification** (a non-modal reconstruction in the style of
Zalta's abstract object theory). Objects *exemplify* properties (the ordinary
mode of having a property) and may *encode* them (the mode in which abstract
objects are characterized). `ZaltaFrame.concrete` plays E!. EXISTENCE_6 is
exemplifying E! (`ExemplifiesExistence`); EXISTENCE_7 is encoding E!
(`EncodesExistence`). Abstract objects are those that do not exemplify E!
(Zalta's A! is ¬◇E!; this reconstruction drops the modality). Object
comprehension: for every set of properties some abstract object encodes exactly
those properties, and only one. Ordinary objects (those exemplifying E!) encode
nothing. `EncodingControl` shows that comprehension gives the characterized god
EXISTENCE_7 but never EXISTENCE_6, that a model satisfies comprehension with
existents but no exemplifying-existent god, and tests the naming premise
`GodNamesTheUniqueMaximeEns` under encoded and exemplified readings of "God" and
of "in act at esse": the exemplified reading of being excludes the encoded
reading of God (the unique maximum would have to encode god while encoding
nothing), and the encoded reading of both delivers a god that does not exemplify
existence. This blocks the definitional argument; it does not show that object
theory blocks ontological arguments (an Anselmian argument with a greatness
premise is valid inside object theory, Oppenheimer and Zalta 1991, navigation). As in part 1, the route's existential import sits in the
maximum-existence premise `InAct m esse` together with the carrier.

**2. Kant: existence is not a real predicate.** Reusing the reality profiles of
`TruthCore.German.Kant.CosmologicalInference`, `ExistenceFeature m p w f` says
that the profile feature `f` is coextensive with existence at `w` (EXISTENCE_8).
This is an extensional surrogate of "existence is a real predicate": it is
satisfiable by accidental coextension and does not say that any concept contains
existence. `ExistenceIsRealPredicate` says some feature is; its exact negation
`ExistenceNotRealPredicate` is an analyst strengthening of Kant's thesis, since it
also denies accidental coextension. `RealPredicateControl`: EXISTENCE_8 suffices
for every most-real candidate to exist (a); some model of the strengthened thesis
with `NecessaryIsMostReal` and `MostRealUnique` has a most-real candidate and no
existing most-real candidate, and no necessary being (b), so those premises do
not yield existence. EXISTENCE_8 is sufficient, not shown necessary.

**3. Meditation V** (analyst formulation of Descartes' ontological argument,
attribution deferred): some candidate is supremely perfect (most real for the
profile) and is God; existence is a perfection (a real predicate); so some
existing being is God. Sibling of the definitional argument of part 1: its
second premise is the extensional real-predicate surrogate EXISTENCE_8, whose
warrant Kant's thesis targets and which the nuclear (part 1) and encoding readings
do not supply.
-/

@[expose] public section

namespace TruthCore.Ontology.EncodingAndRealPredicates

open TruthCore.Case.Catholicism (GodExists GodNamesTheUniqueMaximeEns)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)
open TruthCore.German.Kant.CosmologicalInference

/-! ## 1. Encoding and exemplification -/

/-- A frame for a non-modal encoding/exemplification object theory. `Exemplifies x
p`: x has p in the ordinary way. `Encodes x p`: x is characterized by p, the mode
in which abstract objects have their defining properties. `concrete` is the
existence property E!. No relation between the two modes is assumed. -/
structure ZaltaFrame where
  Object : Type
  Property : Type
  Exemplifies : Object → Property → Prop
  Encodes : Object → Property → Prop
  concrete : Property

/-- EXISTENCE_6: exemplifying the existence property E!. -/
def ExemplifiesExistence (F : ZaltaFrame) (x : F.Object) : Prop :=
  F.Exemplifies x F.concrete

/-- EXISTENCE_7: encoding the existence property E!. -/
def EncodesExistence (F : ZaltaFrame) (x : F.Object) : Prop :=
  F.Encodes x F.concrete

/-- Abstract objects: those that do not exemplify E! (non-modal surrogate of ¬◇E!). -/
def IsAbstract (F : ZaltaFrame) (x : F.Object) : Prop := ¬ ExemplifiesExistence F x

/-- Object comprehension: for every set of properties exactly one abstract object
encodes exactly those properties. -/
def ObjectComprehension (F : ZaltaFrame) : Prop :=
  ∀ S : Set F.Property, ∃ x, IsAbstract F x ∧ (∀ p, F.Encodes x p ↔ p ∈ S) ∧
    ∀ y, IsAbstract F y → (∀ p, F.Encodes y p ↔ p ∈ S) → y = x

/-- Ordinary objects (those exemplifying E!) encode no property. -/
def OrdinaryEncodeNothing (F : ZaltaFrame) : Prop :=
  ∀ x, ExemplifiesExistence F x → ∀ p, ¬ F.Encodes x p

/-- The encoding control.

(a) In every frame with object comprehension, for any properties `g`, `o` some
object encodes `g`, `o` and E! (EXISTENCE_7) and does not exemplify E!
(EXISTENCE_6).

(b) In every frame where ordinary objects encode nothing, if the naming premise's
form holds with "in act at esse" read as EXISTENCE_6 and "God" read as encoding
`g`, then no object is the unique maximum in being that causes all in the genus.

(c) Some frame has object comprehension, ordinary objects encoding nothing, an
object exemplifying E!, and properties `g`, `o` such that: some object encodes
`g`, `o` and E!; no object exemplifies both E! and `g`; no being (object
exemplifying E!) exemplifies `g`; and, with "in act at esse" read as EXISTENCE_7
and "God" as encoding `g`, for some "more in being" and causal relation the
naming premise's form holds, some object is the unique maximum in being causing
all in the genus, and some object encodes `g`. -/
def EncodingControl : Prop :=
  (∀ F : ZaltaFrame, ObjectComprehension F → ∀ g o : F.Property,
    ∃ x, F.Encodes x g ∧ F.Encodes x o ∧ EncodesExistence F x ∧ ¬ ExemplifiesExistence F x) ∧
  (∀ (F : ZaltaFrame), OrdinaryEncodeNothing F → ∀ (g : F.Property)
      (MoreIn : Unit → F.Object → F.Object → Prop) (CausesIn : F.Object → F.Object → Unit → Prop),
    GodNamesTheUniqueMaximeEns (fun x (_ : Unit) => ExemplifiesExistence F x) MoreIn CausesIn ()
      (fun x => F.Encodes x g) →
    ¬ ∃ m, IsMaximumIn (fun x (_ : Unit) => ExemplifiesExistence F x) MoreIn () m ∧
      CausesAllInGenus (fun x (_ : Unit) => ExemplifiesExistence F x) CausesIn () m ∧
      ∀ m', IsMaximumIn (fun x (_ : Unit) => ExemplifiesExistence F x) MoreIn () m' → m' = m) ∧
  (∃ F : ZaltaFrame, ObjectComprehension F ∧ OrdinaryEncodeNothing F ∧
    (∃ x, ExemplifiesExistence F x) ∧ ∃ g o : F.Property,
      (∃ x, F.Encodes x g ∧ F.Encodes x o ∧ EncodesExistence F x) ∧
      (¬ ∃ x, ExemplifiesExistence F x ∧ F.Exemplifies x g) ∧
      ¬ GodExists (fun b : {x : F.Object // ExemplifiesExistence F x} => F.Exemplifies b.1 g) ∧
      ∃ (MoreIn : Unit → F.Object → F.Object → Prop)
          (CausesIn : F.Object → F.Object → Unit → Prop),
        GodNamesTheUniqueMaximeEns (fun x (_ : Unit) => EncodesExistence F x) MoreIn CausesIn ()
          (fun x => F.Encodes x g) ∧
        (∃ m, IsMaximumIn (fun x (_ : Unit) => EncodesExistence F x) MoreIn () m ∧
          CausesAllInGenus (fun x (_ : Unit) => EncodesExistence F x) CausesIn () m ∧
          ∀ m', IsMaximumIn (fun x (_ : Unit) => EncodesExistence F x) MoreIn () m' → m' = m) ∧
        GodExists (fun x => F.Encodes x g))

/-! ## 2. Kant: existence is not a real predicate -/

variable {W E : Type}

/-- EXISTENCE_8: the feature `f` of the reality profile is had by exactly the
candidates existing at `w`. An extensional surrogate of "existence is a real
predicate", satisfiable by accidental coextension. -/
def ExistenceFeature (m : Ontic W E) (p : RealityProfile E) (w : W) (f : p.Feature) : Prop :=
  ∀ x, p.Has x f ↔ m.ExistsAt w x

/-- Some feature of the profile is EXISTENCE_8 at `w` (the extensional
real-predicate surrogate). -/
def ExistenceIsRealPredicate (m : Ontic W E) (p : RealityProfile E) (w : W) : Prop :=
  ∃ f, ExistenceFeature m p w f

/-- Strengthened Kantian thesis, analyst formulation: no feature of the profile
is coextensive with existence at `w`. The exact negation of
`ExistenceIsRealPredicate`; it also denies accidental coextension, which Kant's
intensional thesis does not. -/
def ExistenceNotRealPredicate (m : Ontic W E) (p : RealityProfile E) (w : W) : Prop :=
  ¬ ExistenceIsRealPredicate m p w

/-- The real-predicate control.

(a) EXISTENCE_8 suffices: for every ontic model, profile and world, if some
feature is coextensive with existence there, every most-real candidate exists
there.

(b) Some model, profile and world satisfy the strengthened Kantian thesis, the
identification premise `NecessaryIsMostReal` and `MostRealUnique`, and have a
most-real candidate, while no most-real candidate exists there and no necessary
being exists: those premises do not yield existence. -/
def RealPredicateControl : Prop :=
  (∀ (W E : Type) (m : Ontic W E) (p : RealityProfile E) (w : W),
    ExistenceIsRealPredicate m p w → ∀ x, MostReal p x → m.ExistsAt w x) ∧
  (∃ (m : Ontic Unit Unit) (p : RealityProfile Unit),
    ExistenceNotRealPredicate m p () ∧ NecessaryIsMostReal m p () ∧ MostRealUnique p ∧
    (∃ x, MostReal p x) ∧ (¬ ∃ x, MostReal p x ∧ m.ExistsAt () x) ∧ ¬ NecessaryBeing m ())

/-! ## 3. Meditation V -/

/-- First premise of the Meditation V argument: some candidate is supremely
perfect (has every positive reality of the profile) and is God. Candidates need
not exist. -/
def SupremelyPerfectGodCandidate (p : RealityProfile E) (IsGod : E → Prop) : Prop :=
  ∃ x, MostReal p x ∧ IsGod x

end TruthCore.Ontology.EncodingAndRealPredicates
