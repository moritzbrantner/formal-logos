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
  determination contained in a concept of `x`. The concept relation
  `Contains` is a stated primitive (`ConceptContent`); which concept is meant
  (ours, given by `x`'s relations to its effects, or one adequate to `x`'s
  nature) is fixed by the premises that hold of it, in particular concept
  adequacy (`ConceptAdequateToEssence`).
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

**Points as logical space, access as real possibility.** The frame's points
are the represented (logical) space; accessibility is real possibility.
Existence-conditional essences and entailment of existence quantify over all
points; necessity and contingency over accessible ones. Kant's thesis in sense
(a) (`ExistenceNotConceptual`) therefore yields a *representable* absence, and
reaches a *real* one only through a further bridge (`Model.Laws`, law 5).

**Act versus fact.** `Exercised v p` (`EsseExercisedAt`) is a stated
primitive: the principle `p` is in act at point `v`; for an esse principle,
that act of being is exercised there. It is world-indexed, unlike the q.3 a.4
`InAct x esse`. The passage from the act of being to the existence fact
`ExistsAt` is the explicit premise `EsseExercisedWhereExists`. The bridge
`EsseEssenceIsEssentialExistence` (statement `565ccd6c`) passes from (c) to
(b); it factors into that act–fact link and `IdentityPutsExerciseInNature`
(the exercise of an identity being's esse lies in its nature, unconditionally).

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

/-- The conceptual-content relation, a stated primitive: `ConceptContent
Contains x φ` says that the world-proposition `φ` is a determination contained
in a concept of `x` (a parameter wrapper over `Contains`). Examples: "is a
coin" and "is worth a hundred thalers" are contained in the concept of a
hundred thalers; "is the first cause of whatever else exists" is contained in
a concept of the first mover formed from its effects. Non-examples: what lies
in a thing's nature but is unknown to the thinker whose concept it is; what is
true of the thing only by accident. Distinct from essential truth (ESSENCE_5):
related only by the explicit bridge `ConceptAdequateToEssence`. Structural
properties assumed: none. -/
def ConceptContent (Contains : B → (W → Prop) → Prop) (x : B) (φ : W → Prop) : Prop :=
  Contains x φ

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
exists is a determination contained in the supplied concept of `x`. The
target of Kant's thesis and the ontological argument's step. -/
def ConceptContainsExistence (F : CausalityFrame W B T R) (Contains : B → (W → Prop) → Prop)
    (x : B) : Prop :=
  ConceptContent Contains x (fun v => F.history.ontic.ExistsAt v x)

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
determination contained in the supplied concept of any thing entails that
thing's existence over the represented points. "Whatever be the content of our
conception of an object, it is necessary to go beyond it, if we wish to
predicate existence of the object" (Kant, *Critique of Pure Reason*,
Meiklejohn translation, Transcendental Dialectic, Book II, ch. III, sect. IV;
read, see the note). It implies that no concept contains existence (law 1). It
is about concepts, not natures: it reaches essential truths only through
concept adequacy (laws 2–3). -/
def ExistenceNotConceptual (F : CausalityFrame W B T R)
    (Contains : B → (W → Prop) → Prop) : Prop :=
  ∀ x φ, ConceptContent Contains x φ → ¬ EntailsExistence F φ x

/-- OPEN (concept adequacy): whatever lies in a being's nature is contained in
the supplied concept of it. False of a concept formed only from a being's
effects, whenever the being's nature has content not given by those effects
(the reading of ST I q.2 a.1 recorded in the note); true by construction of a
concept adequate to the nature (the "ratio" in itself). -/
def ConceptAdequateToEssence (Contains : B → (W → Prop) → Prop)
    (Essential : B → (W → Prop) → Prop) : Prop :=
  ∀ (x : B) (φ : W → Prop), EssentialTruth Essential x φ → ConceptContent Contains x φ

/-- OPEN (act identity puts existence in the concept): whatever has its esse
identical with its essence has its existence contained in the supplied
concept of it. For a concept adequate to the nature this is the step of ST I
q.2 a.1 from "God is His own existence" to "the predicate is the same as the
subject" (read; analyst reading, see the note). -/
def IdentityInConcept (F : CausalityFrame W B T R) (Contains : B → (W → Prop) → Prop)
    (essenceOf esseOf : B → P) : Prop :=
  ∀ x, EsseIsEssence essenceOf esseOf x → ConceptContainsExistence F Contains x

/-- OPEN (the act–fact link): every being's act of being is exercised at
exactly the points where the being exists. The explicit passage from esse as
act (`EsseExercisedAt`) to existence as the world-relative fact (`ExistsAt`). -/
def EsseExercisedWhereExists (F : CausalityFrame W B T R) (Exercised : W → P → Prop)
    (esseOf : B → P) : Prop :=
  ∀ v x, EsseExercisedAt Exercised v (esseOf x) ↔ F.history.ontic.ExistsAt v x

/-- OPEN (exercise in the nature): whatever has its esse identical with its
essence has, in its nature, that its esse is exercised: unconditionally, the
proposition true exactly where that act is exercised. Existence-conditional
essentialism rejects it for any such being whose absence is representable,
given the act–fact link (law 6). -/
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

open TruthCore.Modal.ModalGrounding (FoundationalBeingsContingentAt)
open TruthCore.Modal.ModalGrounding.Model (frameOn toTrue univ bothHere bothContingent lockedF
  fEssentialExistence noEssence otherRequiresF FoundationalF)
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
5. Kant's thesis reaches real possibility of absence only by identifying the
   represented space with real possibility: with access from `w` to every
   point, a being existing at `w` with a nonempty concept is contingent at `w`.
6. Existence-conditional essences, the act–fact link and exercise in the
   nature exclude every esse–essence identity whose absence is representable.
7. Under the act–fact link, at every point where an identity being exists its
   essence is exercised: the conditional reading of exercise in the nature is
   satisfied by every identity being, necessary or not.
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
    essential truth make `x` necessary. -/
def Laws : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (Contains : B → (W → Prop) → Prop),
    ExistenceNotConceptual F Contains → ∀ x, ¬ ConceptContainsExistence F Contains x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (Contains Essential : B → (W → Prop) → Prop),
    ExistenceNotConceptual F Contains → ConceptAdequateToEssence Contains Essential →
    ∀ x, ¬ NatureEntailsExistence F Essential x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (Contains Essential : B → (W → Prop) → Prop)
    (essenceOf esseOf : B → P),
    ExistenceNotConceptual F Contains → ConceptAdequateToEssence Contains Essential →
    EsseEssenceIsEssentialExistence F essenceOf esseOf Essential →
    ∀ x, ¬ EsseIsEssence essenceOf esseOf x) ∧
  (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (Contains : B → (W → Prop) → Prop)
    (essenceOf esseOf : B → P),
    ExistenceNotConceptual F Contains → IdentityInConcept F Contains essenceOf esseOf →
    ∀ x, ¬ EsseIsEssence essenceOf esseOf x) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (Contains : B → (W → Prop) → Prop) (w : W),
    ExistenceNotConceptual F Contains → (∀ v, F.history.ontic.frame.access w v) →
    ∀ x φ, F.history.ontic.ExistsAt w x → ConceptContent Contains x φ →
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
    (∃ φ, EssentialTruth Essential x φ) → NecessaryAt F.history.ontic w x)

/-! ### Model ingredients

Beings are `Bool`: `true` is the identity candidate (esse equal to essence
under `esseTrue`/`essenceByBeing`), `false` a second being whose esse and
essence differ. Points are `Bool`. -/

/-- Access only to point `true`; both beings exist only at point `true`. The
point `false` is represented (thinkable) but not really possible from `true`. -/
def kantFrame : CausalityFrame Bool Bool Unit Bool := frameOn toTrue bothHere noCause noPrior

/-- Universal access; `true` everywhere, `false` only at point `true`. -/
def requiredFrame : CausalityFrame Bool Bool Unit Bool := frameOn univ xContingent noCause noPrior

/-- A concept of `true` formed from its effects: "if anything else exists,
`true` exists" (the first cause of whatever else exists). -/
def effectConcept {W : Type} (F : CausalityFrame W Bool Unit Bool) (x : Bool)
    (φ : W → Prop) : Prop :=
  x = true ∧ φ = fun v => F.history.ontic.ExistsAt v false → F.history.ontic.ExistsAt v true

/-- Every principle is in act exactly at point `true`. -/
def exercisedHere (v _ : Bool) : Prop := v = true

/-- Every principle is in act at every point. -/
def exercisedEverywhere (_ _ : Bool) : Prop := True

/-- `true`'s nature includes only the conditional exercise of its esse ("if
`true` exists, its act of being is exercised"). -/
def conditionalExercise (F : CausalityFrame Bool Bool Unit Bool) (x : Bool)
    (φ : Bool → Prop) : Prop :=
  x = true ∧ φ = fun v => F.history.ontic.ExistsAt v true → exercisedHere v true

/-- `true`'s nature includes the exercise of its esse under the decoupled
interpretation `exercisedEverywhere`. -/
def everywhereExercise (x : Bool) (φ : Bool → Prop) : Prop :=
  x = true ∧ φ = fun v => exercisedEverywhere v true

/-- **kantAquinas** (frame `kantFrame`, reading point `true`). With the concept
formed from effects: Kant's thesis holds, no concept contains `true`'s
existence, and neither concept adequacy nor the identity-to-concept bridge
holds. Meanwhile `true` is foundational with esse equal to essence; the
act–fact link, exercise in the nature, the unconditional bridge `565ccd6c`,
essence grounds necessity, constitutive essential existence and necessity all
hold; and its absence is representable (point `false`) though not really
possible. With the concept adequate to the nature (the essential relation
itself): concept adequacy and the identity-to-concept bridge hold and Kant's
thesis fails. Admissible on a Thomist reading of ST I q.2 a.1 (not
self-evident to us, self-evident in itself) with Kant's thesis restricted to
concepts formed from effects, and on the distinction of logical from real
possibility (Kant's note 67 in the Meiklejohn translation of the same section). -/
def KantAquinasModel : Prop :=
  FoundationalF kantFrame true noPower ∧
  ExistenceNotConceptual kantFrame (effectConcept kantFrame) ∧
  ¬ ConceptContainsExistence kantFrame (effectConcept kantFrame) true ∧
  ¬ ConceptAdequateToEssence (effectConcept kantFrame) (fEssentialExistence kantFrame) ∧
  ¬ IdentityInConcept kantFrame (effectConcept kantFrame) essenceByBeing esseTrue ∧
  EsseIsEssence essenceByBeing esseTrue true ∧
  EsseExercisedWhereExists kantFrame exercisedHere esseTrue ∧
  IdentityPutsExerciseInNature exercisedHere (fEssentialExistence kantFrame) essenceByBeing
    esseTrue ∧
  EsseEssenceIsEssentialExistence kantFrame essenceByBeing esseTrue
    (fEssentialExistence kantFrame) ∧
  EssenceGroundsNecessity kantFrame true (fEssentialExistence kantFrame) ∧
  EssentialExistence kantFrame (fEssentialExistence kantFrame) true ∧
  NecessaryAt kantFrame.history.ontic true true ∧
  (∃ v, ¬ kantFrame.history.ontic.ExistsAt v true) ∧
  ¬ ExistenceNotConceptual kantFrame (fEssentialExistence kantFrame) ∧
  ConceptAdequateToEssence (fEssentialExistence kantFrame) (fEssentialExistence kantFrame) ∧
  IdentityInConcept kantFrame (fEssentialExistence kantFrame) essenceByBeing esseTrue

/-- **conditionalIdentity** (frame `bothContingent`, reading point `true`):
`true` is foundational with esse equal to essence and the act–fact link
holds, but its nature includes the exercise of its esse only conditionally.
Existence-conditional essences, essence grounds necessity, the essentialist
account of possibility, unrequired-by-others, Kant's thesis for the concept
adequate to the nature and concept adequacy hold; exercise in the nature, the
unconditional bridge and the identity-to-concept bridge fail; no essential
truth entails `true`'s existence; `true` is contingent and every foundational
being is contingent. Admissible on a Fine/Lowe existence-conditional
essentialism with Kant's thesis extended to adequate concepts. -/
def ConditionalIdentityModel : Prop :=
  FoundationalF bothContingent true noPower ∧
  EsseIsEssence essenceByBeing esseTrue true ∧
  EsseExercisedWhereExists bothContingent exercisedHere esseTrue ∧
  ExistenceConditionalEssences bothContingent (conditionalExercise bothContingent) ∧
  ¬ IdentityPutsExerciseInNature exercisedHere (conditionalExercise bothContingent)
    essenceByBeing esseTrue ∧
  ¬ EsseEssenceIsEssentialExistence bothContingent essenceByBeing esseTrue
    (conditionalExercise bothContingent) ∧
  EssenceGroundsNecessity bothContingent true (conditionalExercise bothContingent) ∧
  EssentialExclusionAccount bothContingent true (conditionalExercise bothContingent) ∧
  FoundationalExistenceUnrequiredByOthers bothContingent true essenceByBeing esseTrue
    receivedNone noneHolds heatFail noPower (conditionalExercise bothContingent) ∧
  ExistenceNotConceptual bothContingent (conditionalExercise bothContingent) ∧
  ConceptAdequateToEssence (conditionalExercise bothContingent)
    (conditionalExercise bothContingent) ∧
  ¬ IdentityInConcept bothContingent (conditionalExercise bothContingent) essenceByBeing
    esseTrue ∧
  ¬ NatureEntailsExistence bothContingent (conditionalExercise bothContingent) true ∧
  ContingentAt bothContingent.history.ontic true true ∧
  FoundationalBeingsContingentAt bothContingent true essenceByBeing esseTrue receivedNone
    noneHolds heatFail noPower

/-- Omission models of the Kant-adequacy argument (Kant's thesis, concept
adequacy, the essentialist account, unrequired-by-others ⊢ every foundational
being is contingent), each with `true` foundational at `true` and the verdict
failing:
1. Kant's thesis omitted (frame `lockedF`; the concept is the nature, which
   includes `true`'s existence unconditionally);
2. concept adequacy omitted (frame `lockedF`; unconditional essential
   existence, empty concept);
3. the essentialist account omitted (frame `lockedF`; no essences, no concept:
   `true` necessary with no essential ground);
4. unrequired-by-others omitted (frame `requiredFrame`; `false`'s nature
   requires `true`'s existence conditionally on its own, the concept is the
   nature). -/
def KantAdequacyOmissions : Prop :=
  (FoundationalF lockedF true noPower ∧
    ¬ ExistenceNotConceptual lockedF (fEssentialExistence lockedF) ∧
    ConceptAdequateToEssence (fEssentialExistence lockedF) (fEssentialExistence lockedF) ∧
    EssentialExclusionAccount lockedF true (fEssentialExistence lockedF) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (fEssentialExistence lockedF) ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF lockedF true noPower ∧
    ExistenceNotConceptual lockedF (noEssence (W := Bool)) ∧
    ¬ ConceptAdequateToEssence (noEssence (W := Bool)) (fEssentialExistence lockedF) ∧
    EssentialExclusionAccount lockedF true (fEssentialExistence lockedF) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (fEssentialExistence lockedF) ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF lockedF true noPower ∧
    ExistenceNotConceptual lockedF (noEssence (W := Bool)) ∧
    ConceptAdequateToEssence (noEssence (W := Bool)) (noEssence (W := Bool)) ∧
    ¬ EssentialExclusionAccount lockedF true (noEssence (W := Bool)) ∧
    FoundationalExistenceUnrequiredByOthers lockedF true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower (noEssence (W := Bool)) ∧
    ¬ FoundationalBeingsContingentAt lockedF true essenceByBeing esseTrue receivedNone noneHolds
      heatFail noPower) ∧
  (FoundationalF requiredFrame true noPower ∧
    ExistenceNotConceptual requiredFrame (otherRequiresF requiredFrame) ∧
    ConceptAdequateToEssence (otherRequiresF requiredFrame) (otherRequiresF requiredFrame) ∧
    EssentialExclusionAccount requiredFrame true (otherRequiresF requiredFrame) ∧
    ¬ FoundationalExistenceUnrequiredByOthers requiredFrame true essenceByBeing esseTrue
      receivedNone noneHolds heatFail noPower (otherRequiresF requiredFrame) ∧
    ¬ FoundationalBeingsContingentAt requiredFrame true essenceByBeing esseTrue receivedNone
      noneHolds heatFail noPower)

/-- Omission models of the factorization of `565ccd6c` (the act–fact link and
exercise in the nature ⊢ esse = essence puts existence in the nature), each on
frame `bothContingent` with `true`'s esse equal to its essence and the
conclusion failing:
1. the act–fact link omitted (`true`'s act of being exercised at every point,
   including where `true` is absent; exercise in the nature holds);
2. exercise in the nature omitted (no essential truths; the link holds). -/
def FactorizationOmissions : Prop :=
  (EsseIsEssence essenceByBeing esseTrue true ∧
    ¬ EsseExercisedWhereExists bothContingent exercisedEverywhere esseTrue ∧
    IdentityPutsExerciseInNature exercisedEverywhere everywhereExercise essenceByBeing esseTrue ∧
    ¬ EsseEssenceIsEssentialExistence bothContingent essenceByBeing esseTrue
      everywhereExercise) ∧
  (EsseIsEssence essenceByBeing esseTrue true ∧
    EsseExercisedWhereExists bothContingent exercisedHere esseTrue ∧
    ¬ IdentityPutsExerciseInNature exercisedHere (noEssence (W := Bool)) essenceByBeing
      esseTrue ∧
    ¬ EsseEssenceIsEssentialExistence bothContingent essenceByBeing esseTrue
      (noEssence (W := Bool)))

/-- All models. -/
def Models : Prop :=
  KantAquinasModel ∧ ConditionalIdentityModel ∧ KantAdequacyOmissions ∧ FactorizationOmissions

/-- Laws and models together. -/
def Controls : Prop := Laws ∧ Models

end Model

end TruthCore.Ontology.ExistenceInEssence
