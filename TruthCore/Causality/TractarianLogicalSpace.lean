module

public import TruthCore.Causality.LogicalNecessityProfiles
public import TruthCore.Logic.AtomismIndependence
public import TruthCore.Logic.StrengthComparison

/-!
# Tautology, logical space and the necessary-being node

Analyst formulation, attribution deferred (logic first). Tractatus locators
are navigation only and no source claim is made: tautology as truth for all
truth-possibilities of the elementary propositions (4.46ff., 6.1ff.), "there is
only logical necessity" (6.37, 6.375), the independence of states of affairs
(2.061, 4.211, 5.134) and the persistence of objects (2.022-2.027). The texts
are contested; none of the formal readings below is attributed to them.

The module adds one sense of "necessary" and one model shape:

* `Tautology` (NECESSARY_16): a formula of the truth-functional fragment of
  the existing `Modal.Formula` language (`BoxFree`: no box or diamond) that
  holds under every assignment of truth values to its atoms. It is a bounded
  instance of NECESSARY_5 ("its denial is contradictory") for one chosen logic:
  classical two-valued truth-functional semantics over the whole function
  space `A → Prop`.
* `LogicalSpaceAt` (combinatorial logical space): every assignment of truth
  values to the atoms is realized at some world accessible from `w`. It reuses
  `AtomismIndependence.Saturates` with the valuation itself as the report map,
  so no new saturation notion is introduced.

The route's NECESSARY_2 (box-existence over `m.ontic.frame`) is untouched.
`OnlyLogicalNecessityAt` is a formal rival thesis about the box of the same
frame, and `ElementaryExistenceAt` is the stronger thesis that the existence of
each candidate is itself a free coordinate of logical space. Neither is
asserted; both are inputs of checked consequences.
-/

@[expose] public section

namespace TruthCore.Causality.TractarianLogicalSpace

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.LogicalNecessityProfiles
open TruthCore.Causality.LogicalNecessityContrast (DenialContradictory)
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Logic.StrengthComparison (ComparisonSpec)

/-! ## The truth-functional fragment and NECESSARY_16 -/

/-- The truth-functional fragment: neither box nor diamond occurs. Atoms,
falsum and implication (hence negation and conjunction) are admitted. -/
def BoxFree {A : Type} : Formula A → Prop
  | .atom _ => True
  | .falsum => True
  | .imp φ ψ => BoxFree φ ∧ BoxFree ψ
  | .box _ => False
  | .diamond _ => False

/-- Truth-functional evaluation under one assignment `s` of truth values to
the atoms. Modal formulas are outside the fragment and evaluate to `False`;
no theorem below uses that clause except to show they are not tautologies. -/
def TFHolds {A : Type} (s : A → Prop) : Formula A → Prop
  | .atom a => s a
  | .falsum => False
  | .imp φ ψ => TFHolds s φ → TFHolds s ψ
  | .box _ => False
  | .diamond _ => False

/-- NECESSARY_16, tautology: a truth-functional formula true under EVERY
assignment of truth values to its atoms (all of `A → Prop`, not a selected
subset). Truth in one model, box-truth on a frame or consequence of a theory
is not required and does not suffice. -/
def Tautology {A : Type} (φ : Formula A) : Prop :=
  BoxFree φ ∧ ∀ s : A → Prop, TFHolds s φ

/-! ## Certified difference of NECESSARY_16 over NECESSARY_14 (#1598) -/

/-- Tautology over K validity of the same formula; the difference is exactly
membership in the truth-functional fragment. No background. -/
def tautologyOverKValidity {A : Type} (φ : Formula A) : ComparisonSpec where
  stronger := Tautology φ
  weaker := AllFrameKValidity φ
  delta := BoxFree φ

/-- Exact factorization: a formula is a tautology iff it is K-valid and
box-free, for every atom type and formula. -/
def TautologyOverKValidityExact : Prop :=
  ∀ {A : Type} (φ : Formula A), Tautology φ ↔ AllFrameKValidity φ ∧ BoxFree φ

/-! ## Combinatorial logical space -/

/-- Logical space at `w` for the valuation `V`: every assignment of truth
values to the atoms is the atomic profile of some world accessible from `w`
(the atoms vary jointly and freely). This is `Saturates` with the valuation
as report map; it says nothing about which atoms are elementary in reality. -/
def LogicalSpaceAt {W A : Type} (F : Frame W) (V : Valuation W A) (w : W) : Prop :=
  TruthCore.Logic.AtomismIndependence.Saturates F V w

/-- Rival thesis "only logical necessity" at `w` (formal reading): every
truth-functional formula boxed at `w` in the frame `F` under valuation `V` is a
NECESSARY_16 tautology. It quantifies over box-free formulas only. -/
def OnlyLogicalNecessityAt {W A : Type} (F : Frame W) (V : Valuation W A) (w : W) : Prop :=
  ∀ φ : Formula A, BoxFree φ → Holds F V w (.box φ) → Tautology φ

/-- Elementary existence at `w`: the existence facts of the candidates are
themselves free coordinates of logical space, that is, every combination of
existence and non-existence of the candidates is realized at a world
accessible from `w` in the route's frame. -/
def ElementaryExistenceAt {W B : Type} (o : Ontic W B) (w : W) : Prop :=
  LogicalSpaceAt o.frame (existenceValuation o) w

/-- Negation of `ElementaryExistenceAt`: some combination of existence facts
of the candidates is realized at no world accessible from `w`. -/
def NotElementaryExistenceAt {W B : Type} (o : Ontic W B) (w : W) : Prop :=
  ¬ ElementaryExistenceAt o w

/-! ## Controls: laws, the Tractarian model and the joint route model -/

namespace Model

/-- Two atomic states of affairs, two objects (stipulated sizes). -/
abbrev Fact := Bool
abbrev Obj := Bool

/-- A world is a complete assignment of obtaining/not obtaining to the
states of affairs: the worlds ARE the points of logical space. -/
abbrev World := Fact → Prop

/-- Every world is accessible from every world. -/
def space : Frame World := ⟨fun _ _ => True⟩

/-- The states of affairs that obtain at a world are the ones it assigns. -/
def factV : Valuation World Fact := fun w a => w a

/-- Objects exist at every world: they are not states of affairs but what
every world is composed from (the persistence of objects, 2.027, as
navigation). This is a stipulation of the model, not a source claim. -/
def objOntic : Ontic World Obj where
  frame := space
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

/-- A contrast ontology in which candidate existence IS elementary: a world
assigns existence to candidates freely. -/
def freeOntic : Ontic (Obj → Prop) Obj where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => w x
  Causes := fun _ _ _ => False

/-- The route's one-point signature placed in Tractarian logical space with
one atomic fact: the one candidate exists at every world. -/
def tractProfile : Profile (Unit → Prop) Control.unitSignature.Being where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (one-point root inventory: the model tests modal structure and logical space, not the concrete/abstract line; no reality claim)
  grounds := fun _ _ _ => False

/-- One-fact valuation on the same worlds as `tractProfile`. -/
def unitFactV : Valuation (Unit → Prop) Unit := fun w a => w a

def p : Formula Fact := .atom true
def identity : Formula Fact := .imp p p
def axiomK : Formula Fact := .imp (.box (.imp p p)) (.imp (.box p) (.box p))

/-- General laws relating NECESSARY_16 to the existing senses:
1. on the truth-functional fragment, Kripke truth is truth-functional truth
   under the world's atomic profile;
2. tautologies are boxed at every world of every frame;
3. on the fragment, K validity (NECESSARY_14) gives tautology;
4. on the fragment and an inhabited frame, selected-frame validity
   (NECESSARY_13) gives tautology;
5. on the fragment and an inhabited frame, tautology gives frame-relative
   `DenialContradictory`; given excluded middle as an explicit antecedent, the
   converse holds;
6. tautology gives contradictory truth-functional denial (the NECESSARY_5
   form for this logic); given excluded middle, the converse holds;
7. in logical space, a box-free formula is boxed exactly when it is a
   tautology;
8. in logical space, any truth-functional formula that is an exact existence
   dictionary for a box-existent bearer is a tautology. -/
def Laws : Prop :=
  (∀ (W A : Type) (F : Frame W) (V : Valuation W A) (w : W) (φ : Formula A),
    BoxFree φ → (Holds F V w φ ↔ TFHolds (V w) φ)) ∧
  (∀ (W A : Type) (F : Frame W) (V : Valuation W A) (w : W) (φ : Formula A),
    Tautology φ → Holds F V w (.box φ)) ∧
  (∀ (A : Type) (φ : Formula A), BoxFree φ → AllFrameKValidity φ → Tautology φ) ∧
  (∀ (W A : Type) (F : Frame W) (_ : W) (φ : Formula A),
    BoxFree φ → SelectedFrameValidity F φ → Tautology φ) ∧
  (∀ (W A : Type) (F : Frame W) (_ : W) (φ : Formula A), BoxFree φ →
    (Tautology φ → DenialContradictory F φ) ∧
    ((∀ q : Prop, q ∨ ¬ q) → DenialContradictory F φ → Tautology φ)) ∧
  (∀ (A : Type) (φ : Formula A),
    (Tautology φ → BoxFree φ ∧ ¬ ∃ s : A → Prop, TFHolds s (Formula.neg φ)) ∧
    ((∀ q : Prop, q ∨ ¬ q) →
      BoxFree φ → (¬ ∃ s : A → Prop, TFHolds s (Formula.neg φ)) → Tautology φ)) ∧
  (∀ (W A : Type) (F : Frame W) (V : Valuation W A) (w : W) (φ : Formula A),
    LogicalSpaceAt F V w → BoxFree φ → (Holds F V w (.box φ) ↔ Tautology φ)) ∧
  (∀ (W A B : Type) (o : Ontic W B) (V : Valuation W A) (w : W) (φ : Formula A) (n : B),
    LogicalSpaceAt o.frame V w → BoxFree φ → ExistenceDictionary o V φ n →
      BoxExistsAt o w n → Tautology φ)

/-- The Tractarian model and the two contrasts, on explicit finite types:
1. the worlds form logical space for the state-of-affairs valuation, the frame
   is S5, and only logical necessity holds for that valuation;
2. every atomic state of affairs is contingent: possible, possibly not, and
   not boxed;
3. both (distinct) objects are NECESSARY_2 box-existent, and object existence
   is not elementary;
4. the identity tautology is an exact existence dictionary for each object,
   an atom is not, and no boxed formula is a tautology;
5. strictness: the K axiom instance `□(p→p) → (□p → □p)` is NECESSARY_14
   K-valid but not a NECESSARY_16 tautology. It is a substitution instance of
   a propositional tautology; strictness comes only from the restriction to
   the truth-functional fragment, so every K-valid formula containing box is
   a witness equally;
6. in the contrast ontology where existence is elementary, no candidate is
   box-existent at any world. -/
def TractarianModel : Prop :=
  (∀ w, LogicalSpaceAt space factV w) ∧ FrameSatisfies .S5 space ∧
  (∀ w, OnlyLogicalNecessityAt space factV w) ∧
  (∀ w a, Holds space factV w (.diamond (.atom a)) ∧
    Holds space factV w (.diamond (Formula.neg (.atom a))) ∧
    ¬ Holds space factV w (.box (.atom a))) ∧
  (∀ w, BoxExistsAt objOntic w true ∧ BoxExistsAt objOntic w false ∧
    NotElementaryExistenceAt objOntic w) ∧
  (∀ x, ExistenceDictionary objOntic factV identity x ∧
    ¬ ExistenceDictionary objOntic factV p x) ∧
  (∀ φ : Formula Fact, ¬ Tautology (.box φ)) ∧
  (AllFrameKValidity axiomK ∧ ¬ Tautology axiomK) ∧
  (∀ w, ElementaryExistenceAt freeOntic w ∧ ∀ x, ¬ BoxExistsAt freeOntic w x)

/-- Joint route model: on ONE frame, the route's S5 frame premise and the S5
necessary-being node hold for the one-point signature's root, while the
state-of-affairs valuation on the same worlds forms logical space and
satisfies only logical necessity, and the root's existence is not elementary.
The stipulated divine fields of the one-point signature are not evidence. -/
def JointRouteModel : Prop :=
  ∀ w : Unit → Prop,
    OnticFrameS5 tractProfile ∧
    NecessaryRootBoxS5 Control.unitSignature tractProfile w (fun _ _ => False) ∧
    LogicalSpaceAt tractProfile.ontic.frame unitFactV w ∧
    OnlyLogicalNecessityAt tractProfile.ontic.frame unitFactV w ∧
    NotElementaryExistenceAt tractProfile.ontic w

/-- The batch controls. -/
def Controls : Prop := Laws ∧ TractarianModel ∧ JointRouteModel

end Model

end TruthCore.Causality.TractarianLogicalSpace
