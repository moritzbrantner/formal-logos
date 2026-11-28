module

public import TruthCore.Causality.PossibiliaContent
public import TruthCore.Causality.AxiarchicGuidance
public import TruthCore.Causality.ImitabilityGrounding

/-! # Intrinsic plurality: real identity, one act, and differentiating content

Analyst formulations, attribution deferred. This diagnoses the intrinsic branch
of the disagreement at `ContainedStandInIsApprehended` and
`NonRealContainmentIsApprehension`; it does not settle either bridge.

A map from modes or intentional contents to their real bearer/realizer is not
Lean equality of those modes. Injectivity would make equality of realizers
collapse the modes; it is an additional, consequential extensionality premise.
Likewise, a ranking that factors through the realizer alone cannot distinguish
modes whose realizer is the same. Weak common grounding says neither that the
map is injective nor that the ranking factors through it. The same distinction
applies to many objects understood in one act.

The exchange-symmetry test makes the remaining demand precise. If a proposed
description preserves an exchange of two modes, and that description exhausts
the grounds of an asymmetric ranking in the specified symmetry-respecting
sense, it cannot rank one exchanged mode above the other. Neither a common
source nor uniform apprehension supplies symmetry-breaking information.
Primitive mode-sensitive formal or dispositional structure is retained as an
explicit alternative: the control supplies a value table, not an explanation
of why that table is the value order or why its plurality is metaphysically
admissible. An intentional account needs discriminating content too.

The finite controls reuse the existing source, candidates, stand-ins, simplicity
and cognition criteria. They add an actual giving exercise to the same shared
CausalityFrame, with an existing contingent effect and an accessible no-effect
world. Apprehension is the only independently varied field. A single generic
operation carries all the modes on both assignments; it is an act of
apprehension only on the apprehending assignment. Its identity with the one
real nature is a stipulated realization, not a deduction of divine simplicity.

Every control is a structural surrogate. In particular, containing unapprehended
modes does not certify explanatory or modal mind-independence; the world-free
mode/act tables are rigid by construction, not proved necessary. The chosen
constitutive simplicity counts real constituents only. No model certifies the
coherence of formal distinctions, all senses of simplicity, a noncognitive
necessary source, or a simple intellect. The production clauses do not explain
selection or infer apprehension from successful correspondence. -/

@[expose] public section

namespace TruthCore.Causality.ImitabilityPlurality

open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence (ConstitutivelySimple)

/-- A permutation preserves the supplied description of each mode. The
description is explicitly selected data, not an assertion that every real or
explanatory fact has been included. -/
def PreservesDescription {C K : Type} (description : C → K) (σ : C ≃ C) : Prop :=
  ∀ c, description (σ c) = description c

/-- OPEN explanatory completeness constraint: a permutation preserving the
supplied mode descriptions preserves their ranking. Common grounding in one
source does not imply it. A primitive mode-sensitive ranking can deny it for
a description that records only the common source; a fuller description may
instead break the permutation. The condition is imposed identically on
intentional contents and unapprehended formal/dispositional modes. -/
def RankingRespectsDescriptionSymmetries {C K : Type} (description : C → K)
    (rank : C → C → Prop) : Prop :=
  ∀ σ : C ≃ C, PreservesDescription description σ →
    ∀ c d, rank c d ↔ rank (σ c) (σ d)

/-- Three limits on an argument from one real source or one act to no plurality.

1. Collapse of modes requires injectivity of their real-realization map.
2. Collapse of an irreflexive ranking requires realization of that ranking on
   the real realizers alone; the second law composes the existing
   `unindividuatedNotFavoured`, without inferring that all containment is real.
3. Exchange symmetry blocks an asymmetric ranking only under the explicit
   symmetry-respecting completeness condition.

These are universal conditional laws, not assertions that injectivity, bare
realizer factorization or the selected description's completeness is true. -/
def IdentityAndRankingLaws : Prop :=
  (∀ (B C A : Type) (RealConstituent : B → A → Prop) (b : B) (realize : C → A),
    ConstitutivelySimple RealConstituent b →
    (∀ c, RealConstituent b (realize c)) →
    Function.Injective realize → Subsingleton C) ∧
  (∀ (B C A : Type) (RealConstituent : B → A → Prop) (b : B) (realize : C → A)
      (rank : C → C → Prop) (realRank : A → A → Prop),
    ConstitutivelySimple RealConstituent b →
    (∀ c, RealConstituent b (realize c)) →
    (∀ c, ¬ rank c c) →
    (∀ c d, rank c d ↔ InvImage realRank realize c d) →
      ∀ c d, ¬ rank c d) ∧
  (∀ (C K : Type) (description : C → K) (rank : C → C → Prop),
    (∀ c d, rank c d → ¬ rank d c) →
    RankingRespectsDescriptionSymmetries description rank →
    ∀ (σ : C ≃ C), PreservesDescription description σ →
      ∀ c d, σ c = d → σ d = c → ¬ rank c d)

namespace Control

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better)
open TruthCore.Causality.ImpersonalFoundationJoint.Control (favTok hasSrc personalSrc noInputs gg)
open TruthCore.Causality.AxiarchicFoundation.Control
  (Item contains produces aboutItem appInner appNone recog)
open TruthCore.Causality.PossibiliaContent
  (NonRealContained NoPresentCandidates)
open TruthCore.Causality.PossibiliaContent.Control (realBlob laneC simple rootCrit)
open TruthCore.Causality.IntentionalExemplarExtension (RootToEsseCauseAt)
open TruthCore.Causality.IntentionalExemplarExtension.Control (frame rootProfile)

/-- The existing necessary-source/contingent-effect frame, with an actual
giving exercise restored. At world true the source true gives being to false;
at world false it gives nothing. Existence, actual-root grounding and CAUSE_2
are the existing fields. This is a finite interpretation, not a theory of
which determinate good explains the contingent exercise. -/
def producingFrame : CausalityFrame Bool Bool Unit Unit :=
  { frame with GivesAt := fun w g x _ => w = true ∧ g = true ∧ x = false }

/-- Every mode has the same real bearer. This noninjective map is not an
assertion that all modes are literally the same element of their own type. -/
def realBearer (_ : Outcome) : Bool := true

/-- Every mode is realized in the source's one real nature. -/
def realizer (_ : Outcome) : Item := Item.blob

/-- A single generic operation carries all the modes. It is not defined as
intellectual; apprehension is stated separately. -/
def actOf (_ : Outcome) : Unit := ()

/-- Only the source exercises the selected generic operation. -/
def operates (b : Bool) (_ : Unit) : Prop := b = true

/-- The operation has the same real realization as the modes. -/
def actRealizer (_ : Unit) : Item := Item.blob

/-- Primitive mode-sensitive values realizing the existing `better` table.
This specifies the order; it does not derive value from mere common grounding.
At cBetter, c has value 2, d value 1, and z and omission value 0. Other
scenarios retain the existing D-realization/valueless assignments. -/
def weight : Scenario → Outcome → Nat
  | .valueless, _ => 0
  | .cBetter, .c => 2
  | s, o => if fits s o then 1 else 0

/-- Exchange c and d, leaving z and omission fixed. -/
def exchange : Outcome ≃ Outcome where
  toFun := fun o => match o with | .c => .d | .d => .c | .z => .z | .none => .none
  invFun := fun o => match o with | .c => .d | .d => .c | .z => .z | .none => .none
  left_inv := by intro o; cases o <;> rfl
  right_inv := by intro o; cases o <;> rfl

/-- Both assignments use this same structure. Distinct modes are contained
without being real constituents; their common realizer is a real constituent.
The source's necessary existence is joint with concrete, contingent production.
The source has exactly one selected operation, with the same real realization
as every mode. No apprehension condition occurs here. -/
def SharedIntrinsicStructure : Prop :=
  ActualRoot rootProfile true true ∧
  NecessaryAt producingFrame.history.ontic true true ∧
  ContingentAt producingFrame.history.ontic true false ∧
  RootToEsseCauseAt producingFrame rootProfile true ∧
  producingFrame.GivesAt true true false () ∧
  (∀ g x, ¬ producingFrame.GivesAt false g x ()) ∧
  (∀ w g x t, producingFrame.GivesAt w g x t →
    producingFrame.history.ontic.ExistsAt w g ∧
    producingFrame.history.ontic.ExistsAt w x ∧
    producingFrame.CausesIn g x producingFrame.esse) ∧
  simple realBlob ∧
  laneC contains noInputs Item.inner ∧
  NoPresentCandidates noInputs ∧
  hasSrc personalSrc true (favTok better) ∧ gg better ∧
  (∀ o, NonRealContained contains realBlob true (Item.inner o) ∧
    ¬ produces true (Item.inner o)) ∧
  (∀ o, realBearer o = true ∧ realizer o = Item.blob ∧
    realBlob true (realizer o) ∧ actRealizer (actOf o) = realizer o) ∧
  (∀ s x y, better s x y ↔ weight s y < weight s x) ∧
  (∀ o, operates true (actOf o)) ∧
  (∀ a, operates true a → a = ())

/-- All of the source's mode-contents are apprehended through its one selected
operation. Apprehension is an explicit conjunct, not inferred from the
operation's uniqueness or its mode-sensitive ranking. Distinct contents and
distinct operations are separate types. -/
def OneActApprehendsModes (Apprehends : Bool → Item → Prop) : Prop :=
  ∃ a, operates true a ∧ (∀ a', operates true a' → a' = a) ∧
    ∀ o, actOf o = a ∧ Apprehends true (Item.inner o)

/-- The same intrinsic structure, interpreted as intentional contents or as
unapprehended formal/dispositional modes. The first has many apprehended
contents in one operation and satisfies both existing cognition criteria; the
second has no apprehension and fails both. Failure is due to the explicit empty
apprehension assignment. This comparison adds no independent evidence for
philosophical parity: its structural equality is by construction. -/
def MatchedApprehensionAssignments : Prop :=
  SharedIntrinsicStructure ∧
  (OneActApprehendsModes appInner ∧ rootCrit noInputs aboutItem appInner ∧
    recog personalSrc Item.inner appInner) ∧
  ((∀ b e, ¬ appNone b e) ∧ ¬ OneActApprehendsModes appNone ∧
    ¬ rootCrit noInputs aboutItem appNone ∧ ¬ recog personalSrc Item.inner appNone)

/-- Omission controls for literal identity and bare-description sufficiency.

The c/d modes are distinct while both their real bearers and their acts are
equal. Neither map is injective. The same exchange preserves the common source,
the common act, and the uniform apprehension descriptions on both assignments.
Neither the bare-source nor bare-act description satisfies the ranking's
symmetry condition. The primitive weight description does satisfy it and is
not preserved by the c/d exchange. The last two clauses rule out realizing the
irreflexive cBetter order on the common source or common act alone.

What the richer description supplies is explicit discriminating information;
the table neither derives its own metaphysical status nor turns aboutness or
correspondence into cognition. -/
def IdentityAndSymmetryControls : Prop :=
  (Outcome.c ≠ Outcome.d ∧ realBearer .c = realBearer .d ∧ actOf .c = actOf .d) ∧
  ¬ Function.Injective realBearer ∧ ¬ Function.Injective actOf ∧
  PreservesDescription realBearer exchange ∧
  PreservesDescription actOf exchange ∧
  PreservesDescription (fun o => appInner true (Item.inner o)) exchange ∧
  PreservesDescription (fun o => appNone true (Item.inner o)) exchange ∧
  (∀ x y, better .cBetter x y → ¬ better .cBetter y x) ∧
  better .cBetter .c .d ∧
  ¬ RankingRespectsDescriptionSymmetries realBearer (better .cBetter) ∧
  ¬ RankingRespectsDescriptionSymmetries actOf (better .cBetter) ∧
  RankingRespectsDescriptionSymmetries (weight .cBetter) (better .cBetter) ∧
  ¬ PreservesDescription (weight .cBetter) exchange ∧
  (∀ rel : Bool → Bool → Prop,
    ¬ (∀ x y, better .cBetter x y ↔ InvImage rel realBearer x y)) ∧
  (∀ rel : Unit → Unit → Prop,
    ¬ (∀ x y, better .cBetter x y ↔ InvImage rel actOf x y))

/-- Joint intrinsic-plurality, one-act, identity and symmetry controls. -/
def IntrinsicPluralityControls : Prop :=
  MatchedApprehensionAssignments ∧ IdentityAndSymmetryControls

end Control

/-! ## Restoring a positive intrinsic basis and productive relevance

This supplement uses the SAME source/effect frame and stand-in indices as the
first controls. It adds the existing PSR arena and truthmaker interfaces, and
the explicit priority tests of `ImitabilityGrounding`. Item, fact and real
constituent identity remain separate: `Fact.mode o` is the fact of availability
of the mode whose stand-in is `Item.inner o`, not an identification of that fact
with its item or the source.

The source's intrinsic nature is assigned a primitive value table. It is a
positive bearer-based basis: the existing source makes its own nature fact
true, and that fact has admitted priority paths to the mode/ranking facts.
The unapprehended assignment routes these paths directly through its modes;
the personal assignment routes them through its one cognitive exercise. In
both cases the ranking contributes to productive exercise in the SAME strict
fact-priority relation, and exercise contributes to the effect's existence.

This is an explicit selected interpretation of explanatory dependence, not a
proof that its edges exhaust metaphysical dependence. The noncognitive row has
no cognitive path into its modes/rank within that interpretation, and positive
source-nature paths remain when effects are absent. The personal row meets the
same source-basis and productive-relevance requirements, with cognitive paths.
The nature table's status as non-composing intrinsic formal/dispositional
structure, or as the content of a simple act, remains OPEN on each side.

Giving includes the ranking as a condition; flattening the table removes that
exercise. This local omission control does not re-explain the still-specified
effect's existence. The world-true exercise condition is itself primitive:
neither account here explains why the contingent exercise occurs, and the
priority relation is explicitly nonnecessitating. These limits prevent the
positive restoration from silently becoming a theory of free selection. -/
namespace PositiveControl

open TruthCore.Causality.ImitabilityPlurality.Control
open TruthCore.Causality.ImitabilityGrounding
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.AxiarchicFoundation.Control (Item appInner appNone)
open TruthCore.Explanation.PSRStrength (Arena Coherent Factive Necessitating)
open TruthCore.Explanation.TruthmakerTheories (Making Sound MakerNecessitation)

/-- Facts of this fragment. `cognition` is the one source cognitive exercise;
no other cognitive exercise is represented. Thus the no-cognitive-path clause
has an explicit scope, rather than quantifying over an unspecified ontology. -/
inductive Fact
  | sourceExists
  | nature
  | mode (o : Outcome)
  | ranking
  | cognition
  | exercise
  | effectExists
  deriving DecidableEq

/-- The selected source's primitive mode-sensitive value table. Assigning this
function to one real nature does not prove that its distinctions are non-real.
That is the same OPEN application of constituent simplicity on both accounts. -/
def sourceValue (values : Outcome → Nat) (b : Bool) (o : Outcome) : Nat :=
  if b then values o else 0

def values : Outcome → Nat := weight .cBetter

/-- A selected, nonnecessitating productive mechanism. The original contingent
exercise condition and the c-over-d ranking both have to hold. -/
def directedFrame (value : Outcome → Nat) : CausalityFrame Bool Bool Unit Unit :=
  { producingFrame with GivesAt := fun v b e t =>
      producingFrame.GivesAt v b e t ∧ sourceValue value b .d < sourceValue value b .c }

/-- The personal parameter selects the presence of the source's single
cognitive exercise. Nature/mode facts require the actual source and the
specified intrinsic table; the ranking additionally requires its strict
inequality. Exercise is present only at the produced world. -/
def holds (personal : Bool) (value : Outcome → Nat) (v : Bool) : Fact → Prop
  | .sourceExists => producingFrame.history.ontic.ExistsAt v true
  | .nature => producingFrame.history.ontic.ExistsAt v true ∧
      ∀ o, sourceValue value true o = value o
  | .mode o => producingFrame.history.ontic.ExistsAt v true ∧
      sourceValue value true o = value o
  | .ranking => producingFrame.history.ontic.ExistsAt v true ∧
      sourceValue value true .d < sourceValue value true .c
  | .cognition => producingFrame.history.ontic.ExistsAt v true ∧ personal = true
  | .exercise => v = true ∧ sourceValue value true .d < sourceValue value true .c
  | .effectExists => producingFrame.history.ontic.ExistsAt v false

/-- Levels certify strictness of the selected priority graph. They are not
degrees of being, weights of goodness, or a universal ordering of explanations. -/
def level : Fact → Nat
  | .sourceExists => 0
  | .nature => 1
  | .cognition => 2
  | .mode _ => 3
  | .ranking => 4
  | .exercise => 5
  | .effectExists => 6

/-- Positive explanatory contributions in the fragment. The two readings have
the same endpoints and value table; they differ on whether the source-nature
path to its modes passes through cognition. -/
def contribution (personal : Bool) (p q : Fact) : Prop :=
  (p = .nature ∧ ((personal = false ∧ ∃ o, q = .mode o) ∨
    (personal = true ∧ q = .cognition))) ∨
  (personal = true ∧ p = .cognition ∧ ∃ o, q = .mode o) ∨
  ((p = .mode .c ∨ p = .mode .d) ∧ q = .ranking) ∨
  (p = .ranking ∧ q = .exercise) ∨
  (p = .exercise ∧ q = .effectExists)

/-- An admitted primitive priority step is factive and strictly increasing.
Its substantive explanatory reading is stipulated, not obtained from the
numeric level test or from mere correspondence. -/
def step (personal : Bool) (value : Outcome → Nat) (v : Bool) (p q : Fact) : Prop :=
  holds personal value v p ∧ holds personal value v q ∧
    level p < level q ∧ contribution personal p q

/-- Existing explanation interface, with Mathlib transitive closure of the
explicit primitive contributions. Both actual and absent-effect worlds retain
the source, modes, ranking and their positive source-nature priority paths. -/
def arena (personal : Bool) (value : Outcome → Nat) : Arena Bool Bool Fact where
  ontic := (directedFrame value).history.ontic
  holds := holds personal value
  exist := fun b => if b then .sourceExists else .effectExists
  explains := fun v => Relation.TransGen (step personal value v)
  conjunct := Eq

/-- The source is the bearer making its own intrinsic nature fact true.
This is an explicit interpretation of the existing primitive Making, not an
identification of truthmaking with the source's efficient giving. -/
def natureMaker : Making Bool Bool Fact :=
  fun v b f => b = true ∧ f = .nature ∧ producingFrame.history.ontic.ExistsAt v b

/-- The original apprehension assignments, used to bind the new cognition
fact to the existing source-level apprehension relation. -/
def apprehends (personal : Bool) : Bool → Item → Prop :=
  if personal then appInner else appNone

/-- Matched positive requirements on either account: an actual source-nature
maker, modes/rank before effects, positive source-nature priority paths,
nonnecessitating strict priority, and relevance to actual productive giving. -/
def SourceBasedAccount (personal : Bool) (value : Outcome → Nat) : Prop :=
  Coherent (arena personal value) ∧ Factive (arena personal value) ∧
  Sound (arena personal value) natureMaker ∧
  MakerNecessitation (arena personal value) natureMaker ∧
  (∀ v, natureMaker v true .nature) ∧
  (∀ v o, (arena personal value).holds v (.mode o) ∧
    (arena personal value).explains v .nature (.mode o)) ∧
  (∀ v, (arena personal value).holds v .ranking ∧
    (arena personal value).explains v .nature .ranking) ∧
  ¬ (arena personal value).ontic.ExistsAt false false ∧
  ¬ Necessitating (arena personal value) ∧
  (∀ v, FactPriorityAsymmetricAt (arena personal value) v ∧
    FactPriorityTransitiveAt (arena personal value) v) ∧
  ModeExplainsProductionAt (arena personal value) true .ranking .exercise ∧
  GivingExercisePriorityAt (directedFrame value) (arena personal value)
    true true .exercise () ∧
  NoEffectGroundedGivingAt (directedFrame value) (arena personal value)
    true true .ranking ()

/-- Restored commitments on the same necessary simple source. The cognitive
fact is equivalent to apprehending all the modes through the source's one act.
Only the personal account has cognitive priority paths; both have the positive
source-nature paths and productive relevance required by SourceBasedAccount.
All absent paths concern this explicitly represented explanatory fragment.
The final omission changes only the table supplied to the giving mechanism. -/
def Certificate : Prop :=
  SharedIntrinsicStructure ∧
  SourceBasedAccount false values ∧ SourceBasedAccount true values ∧
  (∀ personal v, (arena personal values).holds v .cognition ↔
    OneActApprehendsModes (apprehends personal)) ∧
  (∀ b e, ¬ apprehends false b e) ∧
  (∀ v o, ¬ (arena false values).explains v .cognition (.mode o)) ∧
  (∀ v, ¬ (arena false values).explains v .cognition .ranking) ∧
  (∀ v o, (arena true values).explains v .cognition (.mode o)) ∧
  (∀ v, (arena true values).explains v .cognition .ranking) ∧
  OneActApprehendsModes (apprehends true) ∧
  (∀ v b e t, (directedFrame values).GivesAt v b e t ↔
    producingFrame.GivesAt v b e t) ∧
  (directedFrame values).GivesAt true true false () ∧
  (∀ v b e t, ¬ (directedFrame (fun _ => 0)).GivesAt v b e t)

end PositiveControl

end TruthCore.Causality.ImitabilityPlurality
