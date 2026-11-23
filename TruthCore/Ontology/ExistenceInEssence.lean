module

public import TruthCore.Modal.ModalGrounding

/-!
# Does existence belong to an essence when essence is identical with esse? (#1887)

Analyst formulations, attribution deferred (logic first). The texts read for
this slice are listed in `docs/notes/existence-in-essence-identity.md` with URL,
section and date; nothing here is a source claim.

The phrase "existence belongs to the essence of `x`" has several senses
(EXISTENCE_IN_ESSENCE, `docs/notes/existence-in-essence-identity.md` §1). Each
is a distinct declaration below; no relation between them is assumed, and the
laws in `Model.Laws` state which bridges connect them.

* (a) *conceptual containment* (`ConceptContainsExistence`): existence is a
  determination contained in a concept of `x`. Concepts are values of their
  own type `ConceptRelation`, distinct from the essence relation; which concept
  is meant (one formed from `x`'s effects, or one adequate to `x`'s nature) is
  fixed by the premises that hold of it, in particular concept adequacy
  (`ConceptAdequateToEssence`).
* (b) *essential truth* (`EssentialExistence`): it lies in the nature of `x`
  that `x` exists, with the Finean primitive `Essential` of
  `TruthCore.Modal.ModalGrounding` (ESSENCE_5). Its consequential variant is
  `NatureEntailsExistence`: some essential truth of `x` entails `x`'s
  existence.
* (c) *act identity* (`EsseIsEssence`): `x`'s represented esse is its
  represented essence (the q.3 a.4 maps, ESSENCE_3). Not a predicate or a
  determination inside a quiddity: an identity of principles, with no world
  index.
* (d) the existing NECESSARY_EXISTENCE_BY_OWN_NATURE_3
  (`EssenceReasonSeparation.OwnEssentialExistence`) is a further sense, on a
  different profile type; no bridge to it is encoded here.

**Points as represented space, access as real possibility.** The frame's
points are the represented space; accessibility is real possibility (an
analyst analogue of Kant's distinction between the logical possibility of a
concept and the real possibility of a thing, not his notion of real
possibility, which concerns objective reality from principles of possible
experience). Existence-conditional essences and entailment of existence
quantify over all points; necessity and contingency over accessible ones.
Kant's thesis in sense (a) (`ExistenceNotConceptual`) therefore yields a
*representable* absence; a represented-to-accessible bridge is needed for a
*real* one, and identifying the two spaces suffices (`Model.Laws`, law 5).

**Act versus fact.** `Exercised v p` (`EsseExercisedAt`) is a stated
primitive: the principle `p` is in act at point `v`; for an esse principle,
that act of being is exercised there. It is world-indexed, unlike the q.3 a.4
`InAct x esse`. The passage from the act of being to the existence fact
`ExistsAt` is the explicit premise `EsseExercisedWhereExists`. Given that
link, the bridge `EsseEssenceIsEssentialExistence` (statement `565ccd6c`) is
equivalent to `IdentityPutsExerciseInNature` (laws 15 and the argument
`exerciseInNatureGivesEssentialExistence`).

Models are finite typed interpretations on the `ModalGrounding.Model` frames:
structural satisfiability of the stated formal readings, never certificates
of metaphysical possibility.
-/

@[expose] public section

namespace TruthCore.Ontology.ExistenceInEssence

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Modal.ModalGrounding (EssentialTruth EntailsExistence EssenceGroundsNecessity
  EsseEssenceIsEssentialExistence ExistenceConditionalEssences EssentialExclusionAccount
  FoundationalExistenceUnrequiredByOthers FoundationalBeingsContingentAt)

variable {W B T R P : Type}

/-! ## Primitive parameters -/

/-- A concept relation: its own type, so that a concept is never silently an
essence relation. `contains x φ` says that the world-proposition `φ` is a
determination contained in this concept of `x`. A model supplies the field;
nothing relates it to `Essential` except explicit premises. -/
structure ConceptRelation (W B : Type) where
  contains : B → (W → Prop) → Prop

/-- The conceptual-content relation, a stated primitive: `ConceptContent C x φ`
says that the world-proposition `φ` is a determination contained in the
concept `C` of `x` (a wrapper over the field `C.contains`). Examples: "is a
coin" and "is worth a hundred thalers" are contained in the concept of a
hundred thalers; "is the first cause of whatever else exists" is contained in
a concept of the first mover formed from its effects. Non-examples: what lies
in a thing's nature but is unknown to the thinker whose concept it is; what is
true of the thing only by accident. Distinct from essential truth (ESSENCE_5):
related only by the explicit bridge `ConceptAdequateToEssence`. Structural
properties assumed: none. -/
def ConceptContent (C : ConceptRelation W B) (x : B) (φ : W → Prop) : Prop :=
  C.contains x φ

/-- The act of being as exercised at a point, a stated primitive:
`EsseExercisedAt Exercised v p` says that the principle `p` is in act at `v`;
for an esse principle, that act of being is exercised there (a parameter
wrapper over `Exercised`). Examples: Socrates' act of being is exercised at a
world where Socrates lives. Non-examples: the truth of the proposition "`x`
exists" (the composition of a proposition, ST I q.3 a.4 ad 2's second sense of
"to be"); the q.3 a.4 `InAct x esse`, which has no world index. Related to
world-relative existence only by the explicit premise
`EsseExercisedWhereExists`. Structural properties assumed: none. -/
def EsseExercisedAt (Exercised : W → P → Prop) (v : W) (p : P) : Prop :=
  Exercised v p

/-! ## Senses of "existence belongs to the essence of `x`" -/

/-- EXISTENCE_IN_ESSENCE_1 (conceptual containment): the proposition that `x`
exists is a determination contained in the concept `C` of `x`. The target of
Kant's thesis and the ontological argument's step. -/
def ConceptContainsExistence (F : CausalityFrame W B T R) (C : ConceptRelation W B)
    (x : B) : Prop :=
  ConceptContent C x (fun v => F.history.ontic.ExistsAt v x)

/-- EXISTENCE_IN_ESSENCE_2 (essential truth, constitutive): it lies in the
nature of `x` that `x` exists (Fine's `□ₓ E!x`, unconditionally: the
proposition true exactly where `x` exists). -/
def EssentialExistence (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop)
    (x : B) : Prop :=
  EssentialTruth Essential x (fun v => F.history.ontic.ExistsAt v x)

/-- EXISTENCE_IN_ESSENCE_3 (act identity): `x`'s represented esse is its
represented essence (the q.3 a.4 maps). An identity of principles with no
world index; it says nothing about other points. -/
def EsseIsEssence (essenceOf esseOf : B → P) (x : B) : Prop :=
  esseOf x = essenceOf x

/-- EXISTENCE_IN_ESSENCE_5 (essential truth, consequential): some essential
truth of `x` entails `x`'s existence over every point. Weaker than
`EssentialExistence` (`Model.Laws`, law 8). -/
def NatureEntailsExistence (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop)
    (x : B) : Prop :=
  ∃ φ, EssentialTruth Essential x φ ∧ EntailsExistence F φ x

/-! ## Theses and bridges -/

/-- OPEN (Kant's thesis, conceptual form; analyst formulation): no
determination contained in the concept `C` of any thing entails that thing's
existence over the represented points. "Whatever be the content of our
conception of an object, it is necessary to go beyond it, if we wish to
predicate existence of the object" (Kant, *Critique of Pure Reason*,
Meiklejohn translation, Transcendental Dialectic, Book II, ch. III, sect. IV;
read, see the note). Stronger than "existence is not a real predicate": it
also excludes any content that entails existence, such as an unconditional
"`x` is omnipotent" read as true only where `x` exists. It implies that no
concept contains existence (law 1). It is about concepts, not natures: it
reaches essential truths only through concept adequacy (laws 2–3). -/
def ExistenceNotConceptual (F : CausalityFrame W B T R) (C : ConceptRelation W B) : Prop :=
  ∀ x φ, ConceptContent C x φ → ¬ EntailsExistence F φ x

/-- OPEN (conceptual necessity is conditional; analyst formulation of Kant's
triangle paragraph, "the absolute necessity of a judgement is only a
conditioned necessity of a thing"): every determination contained in the
concept `C` of `x` holds at every point where `x` is absent, that is, a
concept yields only "if `x` is posited, then …". The conceptual counterpart
of existence-conditional essences (laws 13–14). Used only in `Model.Laws`
and the models. -/
def ConceptualNecessityConditional (F : CausalityFrame W B T R)
    (C : ConceptRelation W B) : Prop :=
  ∀ x φ, ConceptContent C x φ → ∀ v, ¬ F.history.ontic.ExistsAt v x → φ v

/-- OPEN (concept adequacy): whatever lies in a being's nature is contained in
the concept `C` of it. False of a concept formed only from a being's effects,
whenever the being's nature has content not given by those effects (the
reading of ST I q.2 a.1 recorded in the note); true by construction of a
concept adequate to the nature (the "ratio" in itself). -/
def ConceptAdequateToEssence (C : ConceptRelation W B)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ (x : B) (φ : W → Prop), EssentialTruth Essential x φ → ConceptContent C x φ

/-- OPEN (act identity puts existence in the concept): whatever has its esse
identical with its essence has its existence contained in the concept `C` of
it. For a concept adequate to the nature this is the step of ST I q.2 a.1
from "God is His own existence" to "the predicate is the same as the subject"
(read; analyst reading, see the note). -/
def IdentityInConcept (F : CausalityFrame W B T R) (C : ConceptRelation W B)
    (essenceOf esseOf : B → P) : Prop :=
  ∀ x, EsseIsEssence essenceOf esseOf x → ConceptContainsExistence F C x

/-- OPEN (the act–fact link): every being's act of being is exercised at
exactly the points where the being exists. The explicit passage from esse as
act (`EsseExercisedAt`) to existence as the world-relative fact (`ExistsAt`). -/
def EsseExercisedWhereExists (F : CausalityFrame W B T R) (Exercised : W → P → Prop)
    (esseOf : B → P) : Prop :=
  ∀ v x, EsseExercisedAt Exercised v (esseOf x) ↔ F.history.ontic.ExistsAt v x

/-- OPEN (exercise in the nature): whatever has its esse identical with its
essence has, in its nature, that its esse is exercised: unconditionally, the
proposition true exactly where that act is exercised. With the act–fact link
it is equivalent to `EsseEssenceIsEssentialExistence` (law 15 and the
factorization argument); existence-conditional essences, the link and it
cannot all hold of an identity being whose absence is representable (law 6). -/
def IdentityPutsExerciseInNature (Exercised : W → P → Prop)
    (Essential : B → (W → Prop) → Prop) (essenceOf esseOf : B → P) : Prop :=
  ∀ x, EsseIsEssence essenceOf esseOf x →
    EssentialTruth Essential x (fun v => EsseExercisedAt Exercised v (esseOf x))

/-- Serious-actualist essence at `x`: every essential truth of `x` entails
`x`'s existence (each is an unconditional predication of `x`, which can hold
only where `x` exists). Used only in `Model.Laws`. -/
def SeriousActualistEssenceAt (F : CausalityFrame W B T R)
    (Essential : B → (W → Prop) → Prop) (x : B) : Prop :=
  ∀ φ, EssentialTruth Essential x φ → EntailsExistence F φ x

/-- No other being's essential truth entails `x`'s existence (the one-being
form of `FoundationalExistenceUnrequiredByOthers`). Used only in
`Model.Laws`. -/
def UnrequiredByOthersAt (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop)
    (x : B) : Prop :=
  ∀ y φ, y ≠ x → EssentialTruth Essential y φ → ¬ EntailsExistence F φ x

/-! ## Laws and finite models -/

namespace Model

open TruthCore.Modal.ModalGrounding (FoundationalAt FoundationalBeingsContingentAt)
open TruthCore.Modal.ModalGrounding.Model (frameOn univ bothHere bothContingent lockedF
  fEssentialExistence noEssence otherRequiresF FoundationalF Pt ptEx gCausesC gPriorC)
open TruthCore.Causality.FirstMoverNecessity.Model (noCause noPrior receivedNone esseTrue
  essenceByBeing noneHolds xContingent)
open TruthCore.Causality.ContingencyGrounding.Model (heatFail noPower)

/-- General laws.
1. Kant's thesis excludes conceptual containment of existence (sense (a)) for
   every being and concept.
2. Kant's thesis with concept adequacy excludes, for every being, that any
   essential truth entails its existence (sense (b), consequential form): the
   modal effect of existence-conditional essences, with no representability
   premise.
3. Kant's thesis, concept adequacy and unconditional essentialism's reading of
   esse = essence (`565ccd6c`) exclude every esse–essence identity.
4. Kant's thesis with the act-identity-to-concept bridge excludes every
   esse–essence identity.
5. Kant's thesis yields only representable absence; identifying the
   represented space with real possibility (access from `w` to every point)
   is one sufficient bridge to real absence: under it, a being existing at
   `w` with a nonempty concept is contingent at `w`. (That some bridge is
   needed is shown by `kantAquinasModel`; weaker bridges also suffice.)
6. Existence-conditional essences, the act–fact link and exercise in the
   nature are jointly inconsistent with an esse–essence identity whose
   absence is representable. Which member to reject is not settled by the
   law.
7. Under the act–fact link, for every identity being `x` and every point `v`
   at which `x` exists, `x`'s essence principle is exercised at `v`; so the
   world-proposition "if `x` exists, its essence is exercised" is true at
   every point. `Essential` does not occur: the law says nothing about what
   lies in any nature.
8. Constitutive essential existence implies the consequential form.
9. Essence grounds necessity: an essential truth entailing a being's
   existence makes it necessary.
10. Essence grounds necessity: a contingent being has no essential truth
    entailing its existence.
11. Within the essentialist framework (excluded middle, essence grounds
    necessity, the essentialist account of possibility, no other being's
    nature requiring `x`), for an `x` existing at `w`: some essential truth of
    `x` entails its existence if and only if `x` is necessary at `w`.
12. Serious-actualist essences: essence grounds necessity, every essential
    truth of `x` an unconditional predication of `x`, and `x` having some
    essential truth make `x` necessary.
13. Conditional conceptual necessity with concept adequacy gives
    existence-conditional essences.
14. Conditional conceptual necessity gives Kant's thesis at every being whose
    absence is representable.
15. Under the act–fact link the unconditional bridge `565ccd6c` gives
    exercise in the nature (the converse of the factorization argument). -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B),
    ExistenceNotConceptual F C → ∀ x, ¬ ConceptContainsExistence F C x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B)
    (Essential : B → (W → Prop) → Prop),
    ExistenceNotConceptual F C → ConceptAdequateToEssence C Essential →
    ∀ x, ¬ NatureEntailsExistence F Essential x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B)
    (Essential : B → (W → Prop) → Prop) (essenceOf esseOf : B → P),
    ExistenceNotConceptual F C → ConceptAdequateToEssence C Essential →
    EsseEssenceIsEssentialExistence F essenceOf esseOf Essential →
    ∀ x, ¬ EsseIsEssence essenceOf esseOf x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B)
    (essenceOf esseOf : B → P),
    ExistenceNotConceptual F C → IdentityInConcept F C essenceOf esseOf →
    ∀ x, ¬ EsseIsEssence essenceOf esseOf x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B) (w : W),
    ExistenceNotConceptual F C → (∀ v, F.history.ontic.frame.access w v) →
    ∀ x φ, F.history.ontic.ExistsAt w x → ConceptContent C x φ →
      ContingentAt F.history.ontic w x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop)
    (Exercised : W → P → Prop) (essenceOf esseOf : B → P),
    ExistenceConditionalEssences F Essential → EsseExercisedWhereExists F Exercised esseOf →
    IdentityPutsExerciseInNature Exercised Essential essenceOf esseOf →
    ∀ x, EsseIsEssence essenceOf esseOf x → (∃ v, ¬ F.history.ontic.ExistsAt v x) → False) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (Exercised : W → P → Prop)
    (essenceOf esseOf : B → P),
    EsseExercisedWhereExists F Exercised esseOf →
    ∀ x, EsseIsEssence essenceOf esseOf x →
      ∀ v, F.history.ontic.ExistsAt v x → EsseExercisedAt Exercised v (essenceOf x)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop) (x : B),
    EssentialExistence F Essential x → NatureEntailsExistence F Essential x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (Essential : B → (W → Prop) → Prop)
    (x : B),
    EssenceGroundsNecessity F w Essential → NatureEntailsExistence F Essential x →
    NecessaryAt F.history.ontic w x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (Essential : B → (W → Prop) → Prop)
    (x : B),
    EssenceGroundsNecessity F w Essential → ContingentAt F.history.ontic w x →
    ¬ NatureEntailsExistence F Essential x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (Essential : B → (W → Prop) → Prop)
    (x : B),
    TruthCore.Logic.ExcludedMiddle → EssenceGroundsNecessity F w Essential →
    EssentialExclusionAccount F w Essential → UnrequiredByOthersAt F Essential x →
    F.history.ontic.ExistsAt w x →
    (NatureEntailsExistence F Essential x ↔ NecessaryAt F.history.ontic w x)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (Essential : B → (W → Prop) → Prop)
    (x : B),
    EssenceGroundsNecessity F w Essential → SeriousActualistEssenceAt F Essential x →
    (∃ φ, EssentialTruth Essential x φ) → NecessaryAt F.history.ontic w x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B)
    (Essential : B → (W → Prop) → Prop),
    ConceptualNecessityConditional F C → ConceptAdequateToEssence C Essential →
    ExistenceConditionalEssences F Essential) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (C : ConceptRelation W B) (x : B),
    ConceptualNecessityConditional F C → (∃ v, ¬ F.history.ontic.ExistsAt v x) →
    ∀ φ, ConceptContent C x φ → ¬ EntailsExistence F φ x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (Essential : B → (W → Prop) → Prop)
    (Exercised : W → P → Prop) (essenceOf esseOf : B → P),
    EsseExercisedWhereExists F Exercised esseOf →
    EsseEssenceIsEssentialExistence F essenceOf esseOf Essential →
    IdentityPutsExerciseInNature Exercised Essential essenceOf esseOf)

/-! ### Model ingredients

Beings are `Bool`: `true` is the identity candidate, `false` a second being.
Principles are `Pr`: `true`'s esse is its essence (`godEsse`); `false` has an
esse (`creatureEsse`) distinct from its essence (`creatureEssence`), so the
act–fact link does not force the two beings to co-exist. -/

/-- Three principles: the identity being's esse = essence, and the second
being's esse and essence. -/
inductive Pr where
  | godEsse
  | creatureEsse
  | creatureEssence
  deriving DecidableEq

/-- Represented esse: distinct for the two beings. -/
def esseOfB : Bool → Pr
  | true => .godEsse
  | false => .creatureEsse

/-- Represented essence: equal to esse only for `true`. -/
def essenceOfB : Bool → Pr
  | true => .godEsse
  | false => .creatureEssence

/-- No principle receives anything. -/
def receivedNoneP (_ : Bool) (_ : Pr) : Prop := False

/-- Each principle is in act exactly where its owner exists. -/
def exercisedBy {W : Type} (F : CausalityFrame W Bool Unit Bool) (v : W) : Pr → Prop
  | .godEsse => F.history.ontic.ExistsAt v true
  | .creatureEsse => F.history.ontic.ExistsAt v false
  | .creatureEssence => F.history.ontic.ExistsAt v false

/-- Every principle is in act at every point. -/
def exercisedEverywhere (_ : Bool) (_ : Pr) : Prop := True

/-- The foundational profile of `true` with the three principles. -/
abbrev FoundationalPr {W : Type} (F : CausalityFrame W Bool Unit Bool) (w : W) : Prop :=
  FoundationalAt F w essenceOfB esseOfB receivedNoneP noneHolds heatFail noPower true

/-- Real possibility from any point: points `a` and `b`. -/
def kaAccess (_ v : Pt) : Prop := v = .a ∨ v = .b

/-- Represented points `a`, `b`, `c`. The reading point `a` really accesses
`a` and `b`, not `c`. `true` exists at `a` and `b`; `false` only at `a`;
nothing at `c`. `true` causes `false`'s esse and is simply prior to it. -/
def kantFrame : CausalityFrame Pt Bool Unit Bool := frameOn kaAccess ptEx gCausesC gPriorC

/-- Universal access; `true` everywhere, `false` only at point `true`. -/
def requiredFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ xContingent noCause noPrior

/-- A concept of `true` formed from its effects: "if `false` exists, `true`
exists" (the cause of the other being). -/
def effectConcept {W : Type} (F : CausalityFrame W Bool Unit Bool) : ConceptRelation W Bool :=
  ⟨fun x φ => x = true ∧
    φ = fun v => F.history.ontic.ExistsAt v false → F.history.ontic.ExistsAt v true⟩

/-- The concept adequate to a nature: its contents are exactly the essential
truths. A construction from the essence relation, not an identification of
the types. -/
def adequateConcept {W : Type} (Essential : Bool → (W → Prop) → Prop) : ConceptRelation W Bool :=
  ⟨Essential⟩

/-- The empty concept. -/
def emptyConcept {W : Type} : ConceptRelation W Bool := ⟨fun _ _ => False⟩

/-- `true`'s nature includes only the conditional exercise of its esse ("if
`true` exists, its act of being is exercised"). -/
def conditionalExercise (F : CausalityFrame Bool Bool Unit Bool) (x : Bool)
    (φ : Bool → Prop) : Prop :=
  x = true ∧ φ = fun v => F.history.ontic.ExistsAt v true → exercisedBy F v .godEsse

/-- `true`'s nature includes the exercise of its esse under the decoupled
interpretation `exercisedEverywhere`. -/
def everywhereExercise (x : Bool) (φ : Bool → Prop) : Prop :=
  x = true ∧ φ = fun v => exercisedEverywhere v .godEsse

/-- **kantAquinas** (frame `kantFrame`, reading point `a`). `true` is
foundational with esse equal to essence; `false` has distinct esse and
essence, is caused by `true` in its esse and is contingent (absent at the
accessible point `b`). The act–fact link holds with distinct principles.
Exercise in the nature, the unconditional bridge `565ccd6c`, essence grounds
necessity, constitutive essential existence and necessity of `true` hold;
`true`'s absence is representable (point `c`) though not really possible.
With the concept formed from effects, Kant's thesis and conditional
conceptual necessity hold, no concept contains `true`'s existence, and
neither concept adequacy nor the identity-to-concept bridge holds. With the
concept adequate to the nature, adequacy and the identity-to-concept bridge
hold and Kant's thesis and conditional conceptual necessity fail. What it
shows about `true` is compatible with a Thomist reading of ST I q.2 a.1 (not
self-evident to us, self-evident in itself) with Kant's thesis restricted to
concepts from effects; it is not a model of Thomism as a whole. -/
def KantAquinasModel : Prop :=
  FoundationalPr kantFrame .a ∧
  ¬ EsseIsEssence essenceOfB esseOfB false ∧
  kantFrame.CausesIn true false kantFrame.esse ∧
  ContingentAt kantFrame.history.ontic .a false ∧
  ExistenceNotConceptual kantFrame (effectConcept kantFrame) ∧
  ConceptualNecessityConditional kantFrame (effectConcept kantFrame) ∧
  ¬ ConceptContainsExistence kantFrame (effectConcept kantFrame) true ∧
  ¬ ConceptAdequateToEssence (effectConcept kantFrame) (fEssentialExistence kantFrame) ∧
  ¬ IdentityInConcept kantFrame (effectConcept kantFrame) essenceOfB esseOfB ∧
  EsseIsEssence essenceOfB esseOfB true ∧
  EsseExercisedWhereExists kantFrame (exercisedBy kantFrame) esseOfB ∧
  IdentityPutsExerciseInNature (exercisedBy kantFrame) (fEssentialExistence kantFrame)
    essenceOfB esseOfB ∧
  EsseEssenceIsEssentialExistence kantFrame essenceOfB esseOfB (fEssentialExistence kantFrame) ∧
  EssenceGroundsNecessity kantFrame .a (fEssentialExistence kantFrame) ∧
  EssentialExistence kantFrame (fEssentialExistence kantFrame) true ∧
  NecessaryAt kantFrame.history.ontic .a true ∧
  (∃ v, ¬ kantFrame.history.ontic.ExistsAt v true) ∧
  ¬ ExistenceNotConceptual kantFrame (adequateConcept (fEssentialExistence kantFrame)) ∧
  ¬ ConceptualNecessityConditional kantFrame (adequateConcept (fEssentialExistence kantFrame)) ∧
  ConceptAdequateToEssence (adequateConcept (fEssentialExistence kantFrame))
    (fEssentialExistence kantFrame) ∧
  IdentityInConcept kantFrame (adequateConcept (fEssentialExistence kantFrame)) essenceOfB
    esseOfB

/-- **conditionalIdentity** (frame `bothContingent`, reading point `true`):
`true` is foundational with esse equal to essence and the act–fact link holds
with distinct principles, but its nature includes the exercise of its esse
only conditionally. Existence-conditional essences, essence grounds
necessity, the essentialist account of possibility, unrequired-by-others,
Kant's thesis and conditional conceptual necessity for the concept adequate
to the nature and concept adequacy hold; exercise in the nature, the
unconditional bridge and the identity-to-concept bridge fail; no essential
truth entails `true`'s existence; `true` is contingent and every foundational
being is contingent. Admissible on a Fine/Lowe existence-conditional
essentialism with Kant's thesis extended to adequate concepts. -/
def ConditionalIdentityModel : Prop :=
  FoundationalPr bothContingent true ∧
  EsseIsEssence essenceOfB esseOfB true ∧
  EsseExercisedWhereExists bothContingent (exercisedBy bothContingent) esseOfB ∧
  ExistenceConditionalEssences bothContingent (conditionalExercise bothContingent) ∧
  ¬ IdentityPutsExerciseInNature (exercisedBy bothContingent)
    (conditionalExercise bothContingent) essenceOfB esseOfB ∧
  ¬ EsseEssenceIsEssentialExistence bothContingent essenceOfB esseOfB
    (conditionalExercise bothContingent) ∧
  EssenceGroundsNecessity bothContingent true (conditionalExercise bothContingent) ∧
  EssentialExclusionAccount bothContingent true (conditionalExercise bothContingent) ∧
  FoundationalExistenceUnrequiredByOthers bothContingent true essenceOfB esseOfB
    receivedNoneP noneHolds heatFail noPower (conditionalExercise bothContingent) ∧
  ExistenceNotConceptual bothContingent (adequateConcept (conditionalExercise bothContingent)) ∧
  ConceptualNecessityConditional bothContingent
    (adequateConcept (conditionalExercise bothContingent)) ∧
  ConceptAdequateToEssence (adequateConcept (conditionalExercise bothContingent))
    (conditionalExercise bothContingent) ∧
  ¬ IdentityInConcept bothContingent (adequateConcept (conditionalExercise bothContingent))
    essenceOfB esseOfB ∧
  ¬ NatureEntailsExistence bothContingent (conditionalExercise bothContingent) true ∧
  ContingentAt bothContingent.history.ontic true true ∧
  FoundationalBeingsContingentAt bothContingent true essenceOfB esseOfB receivedNoneP
    noneHolds heatFail noPower

/-- Omission models of the Kant-adequacy argument (Kant's thesis, concept
adequacy, the essentialist account, unrequired-by-others ⊢ every foundational
being is contingent), each with `true` foundational at `true` and the verdict
failing. They do not use the act–fact link, so the shared esse principle of
`esseTrue` plays no role:
1. Kant's thesis omitted (frame `lockedF`; the concept is the adequate one,
   whose nature includes `true`'s existence unconditionally);
2. concept adequacy omitted (frame `lockedF`; unconditional essential
   existence, empty concept);
3. the essentialist account omitted (frame `lockedF`; no essences, empty
   concept: `true` necessary with no essential ground);
4. unrequired-by-others omitted (frame `requiredFrame`; `false`'s nature
   requires `true`'s existence conditionally on its own, the concept is the
   adequate one). -/
def KantAdequacyOmissions : Prop :=
  (FoundationalF lockedF true noPower ∧
    ¬ ExistenceNotConceptual lockedF (adequateConcept (fEssentialExistence lockedF)) ∧
    ConceptAdequateToEssence (adequateConcept (fEssentialExistence lockedF))
      (fEssentialExistence lockedF) ∧
    EssentialExclusionAccount lockedF true (fEssentialExistence lockedF) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (fEssentialExistence lockedF) ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF lockedF true noPower ∧
    ExistenceNotConceptual lockedF (emptyConcept (W := Bool)) ∧
    ¬ ConceptAdequateToEssence (emptyConcept (W := Bool)) (fEssentialExistence lockedF) ∧
    EssentialExclusionAccount lockedF true (fEssentialExistence lockedF) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (fEssentialExistence lockedF) ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF lockedF true noPower ∧
    ExistenceNotConceptual lockedF (emptyConcept (W := Bool)) ∧
    ConceptAdequateToEssence (emptyConcept (W := Bool)) (noEssence (W := Bool)) ∧
    ¬ EssentialExclusionAccount lockedF true (noEssence (W := Bool)) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (noEssence (W := Bool)) ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF requiredFrame true noPower ∧
    ExistenceNotConceptual requiredFrame (adequateConcept (otherRequiresF requiredFrame)) ∧
    ConceptAdequateToEssence (adequateConcept (otherRequiresF requiredFrame))
      (otherRequiresF requiredFrame) ∧
    EssentialExclusionAccount requiredFrame true (otherRequiresF requiredFrame) ∧
    ¬ FoundationalExistenceUnrequiredByOthers requiredFrame true essenceByBeing esseTrue
      receivedNone noneHolds heatFail noPower (otherRequiresF requiredFrame) ∧
    ¬ FoundationalBeingsContingentAt requiredFrame true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower)

/-- Omission models of the factorization of `565ccd6c` (the act–fact link and
exercise in the nature ⊢ esse = essence puts existence in the nature), each on
frame `bothContingent` with distinct principles, `true`'s esse equal to its
essence and the conclusion failing:
1. the act–fact link omitted (every principle exercised at every point,
   including where its owner is absent; exercise in the nature holds);
2. exercise in the nature omitted (no essential truths; the link holds). -/
def FactorizationOmissions : Prop :=
  (EsseIsEssence essenceOfB esseOfB true ∧
    ¬ EsseExercisedWhereExists bothContingent exercisedEverywhere esseOfB ∧
    IdentityPutsExerciseInNature exercisedEverywhere everywhereExercise essenceOfB esseOfB ∧
    ¬ EsseEssenceIsEssentialExistence bothContingent essenceOfB esseOfB everywhereExercise) ∧
  (EsseIsEssence essenceOfB esseOfB true ∧
    EsseExercisedWhereExists bothContingent (exercisedBy bothContingent) esseOfB ∧
    ¬ IdentityPutsExerciseInNature (exercisedBy bothContingent) (noEssence (W := Bool))
      essenceOfB esseOfB ∧
    ¬ EsseEssenceIsEssentialExistence bothContingent essenceOfB esseOfB
      (noEssence (W := Bool)))

/-- All models. -/
def Models : Prop :=
  KantAquinasModel ∧ ConditionalIdentityModel ∧ KantAdequacyOmissions ∧ FactorizationOmissions

/-- Laws and models together. -/
def Controls : Prop := Laws ∧ Models

end Model

end TruthCore.Ontology.ExistenceInEssence
