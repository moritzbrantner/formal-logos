module

public import TruthCore.Causality.ImpersonalFoundationJoint

/-! # Where are a value-responsive source's non-present candidates individuated? (#2145, premise lane C)

Analyst formulations, attribution deferred (logic first). See
`docs/notes/causal-perfection-transfer.md`, section "Individuating non-present
candidates: the axiarchic rival and the cognition criterion".

The cognition criterion of Lane 4 (`GoodGeneralFavouringIsApprehension`) says
that a bearer whose favouring depends, for some pair of candidates at least one
of which is not a present input, on their value with their end content held
fixed, apprehends some content about a candidate. The impersonal good-general
(axiarchic) rival denies it. This module does not test the criterion against
the rival's verdict; it asks a prior question that both must answer. To favour
`x` over `y` by value, `x` and `y` must figure in the favouring as two distinct
items before either is produced. Where are they individuated?

**Realization on items.** A bearer's *stand-in* assignment `stand b x` names the
real item through which candidate `x` figures in `b`'s favouring: for a present
input it may be the input itself; for a non-present candidate it is something
else (an abstract candidate or value-fact, an idea, a mode of imitability, a
power directed to `x`, or the bearer's one undifferentiated nature). A favouring
determination is *realized on items* when, in every scenario, its profile is the
inverse image (`InvImage`) of a relation among the stand-ins; the relation is
indexed by the favouring profile, so several favourings of one bearer are not
excluded. Realization with irreflexivity only requires favoured pairs to have
distinct stand-ins. It does not require the stand-ins to be real in any further
sense: the identity assignment satisfies it, and candidates as their own
stand-ins fall under the independent locus. The demand for real terms is carried
by `NoIndependentStandIn`, not by realization.

The shape `stand : B → X → C` assumes that, for each bearer, every way a
candidate figures in its favourings goes through one stand-in item. That is the
substantive coverage assumption; the coverage of the three loci below is
trivial by comparison.

**Three loci.** Relative to a bearer an item is contained in it (`Contains`),
produced by it (`Produces`), or independent of it (neither). With excluded
middle these cover every item; since `Independent` is defined as the complement,
that coverage is trivial. The individuation trilemma:

1. *independent realm* (Leslie-type requiredness of abstract value-facts, a
   demiurge's independent Forms): excluded by the open `NoIndependentStandIn`;
2. *in the source* (ideas, modes of imitability, powers directed to their
   manifestations): reached when the other two are excluded; whether it is
   apprehension is the open `ContainedStandInIsApprehended`;
3. *nowhere* (one undifferentiated item for every candidate): with item
   realization and irreflexivity it gives no favouring of one candidate over
   another (`unindividuatedNotFavoured`, in the results module). In the
   registered derivation this exclusion only discharges the individuation
   conjunct of the recognition bridge; without that conjunct realization and
   irreflexivity are not needed.

A produced item outside the bearer (a realm the source makes) is excluded by the
open `NoMerelyProducedStandIn` (source-of-differences reasoning).

`Contains`, `Produces`, `About` and `Apprehends` are free. Nothing in a type
separates intentional containment (an idea) from virtual containment (a power
directed to a manifestation): that is exactly the step the open recognition
bridge takes. Given the other five premises of the registered derivation, that
bridge is strictly stronger than the cognition criterion
(`ContainedStandInYieldsApprehension` and the results-module lemmas), so the
derivation relocates and localizes the dispute; it adds no warrant against a
rival who grants the other premises. Every model in `Control` is a finite structural surrogate; it
witnesses only the stated formal interpretation, never a metaphysical
possibility. -/

@[expose] public section

namespace TruthCore.Causality.AxiarchicFoundation

open TruthCore.Causality.GoodFavouring (BecauseOfGoodness)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral GoodGeneralFavouringIsApprehension)

variable {B D S X Z C : Type}

/-- OPEN item realization: for every bearer `b` and every favouring determination
`favours φ` of `b`, in every scenario `s`, `φ s` favours `x` over `y` exactly when
the relation `rel b φ s` holds between the stand-ins `stand b x` and `stand b y`
(the profile is the inverse image of an item relation). The relation is indexed
by the favouring profile, so a bearer may have several favourings realized on the
same stand-ins: one favouring per bearer is not built in (that is the separate
open bridge `OneFavouringRealization`). What realization constrains, together with
irreflexivity, is only that favoured pairs have distinct stand-ins
(`unindividuatedNotFavoured`). It does not by itself require the stand-ins to be
"real" in any further sense: the identity assignment (candidates as their own
stand-ins) satisfies it, and such an assignment falls under the independent locus
excluded by `NoIndependentStandIn`. -/
def FavouringRealizedOnItems (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (stand : B → X → C) (rel : B → GoodFavouring.Profile S X → S → C → C → Prop) : Prop :=
  ∀ b φ, Has b (favours φ) → ∀ s x y, φ s x y ↔ InvImage (rel b φ s) (stand b) x y

/-- OPEN irreflexivity: no favouring determination favours a candidate over
itself in any scenario. Weaker than the asymmetry (net favouring) that the #2163
favouring standard assumes. -/
def FavouringIrreflexive (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D) :
    Prop :=
  ∀ b φ, Has b (favours φ) → ∀ s x, ¬ φ s x x

/-! ## Three senses of containment (disambiguation CONTAINED_IN)

The locus bridges and the antecedent of the recognition bridge use containment in
the generic sense. The recognition bridge's consequent (the contained stand-in is
an apprehended content about the candidate) is containment in the intentional
sense; the rival's contained-but-unapprehended stand-ins (powers, modes of
imitability) are containment in the virtual sense. The recognition bridge is the
explicit passage from the generic to the intentional sense. The intentional and
virtual senses are reduced here to the free relations `Apprehends` and `About`;
the classical difference between having the form of another as other and having
the power to produce it is not captured beyond that. The premise types
use these declarations: `Independent` and `NoMerelyProducedStandIn` state
containment as `ContainsGenerically` (CONTAINED_IN_1), and the recognition bridge's
antecedent is `ContainsGenerically` while its consequent is `ContainsIntentionally`
(CONTAINED_IN_2), so binding can see which sense each premise uses and the bridge
is the only premise reaching both. -/

/-- CONTAINED_IN_1 (generic): the item is contained in the bearer, intentionally or
virtually; the relation does not say which. -/
def ContainsGenerically (Contains : B → C → Prop) (b : B) (e : C) : Prop := Contains b e

/-- CONTAINED_IN_2 (intentional): the item is contained in the bearer and the bearer
apprehends it as a content about some candidate. -/
def ContainsIntentionally (Contains : B → C → Prop) (About : C → X → Prop)
    (Apprehends : B → C → Prop) (b : B) (e : C) : Prop :=
  Contains b e ∧ (∃ x, About e x) ∧ Apprehends b e

/-- CONTAINED_IN_3 (virtual): any item contained in the bearer without being
apprehended by it, for example a power to produce, a mode in which the bearer
is imitable, its one undifferentiated nature or a sub-personal item. -/
def ContainsVirtually (Contains : B → C → Prop) (Apprehends : B → C → Prop) (b : B) (e : C) :
    Prop :=
  Contains b e ∧ ¬ Apprehends b e

/-- An item `e` is independent of the bearer `b`: `b` neither contains nor produces it. -/
def Independent (Contains Produces : B → C → Prop) (b : B) (e : C) : Prop :=
  ¬ ContainsGenerically Contains b e ∧ ¬ Produces b e

/-- OPEN own-favouring bridge (horn 1 excluded): the stand-in of a candidate that
is not a present input, in a bearer's own favouring determination, is not
independent of that bearer. An independent item can make a difference to a
bearer by acting on it (then it is a present input) or by being represented in
it (then something contained stands for it); a third, sui generis mode (value
directly efficacious on the bearer) is what this bridge denies. -/
def NoIndependentStandIn (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (Present : S → X → Prop) (stand : B → X → C) (Contains Produces : B → C → Prop) : Prop :=
  ∀ b φ s x, Has b (favours φ) → ¬ Present s x → ¬ Independent Contains Produces b (stand b x)

/-- OPEN source-of-differences bridge for produced stand-ins: the stand-in of a
non-present candidate in a bearer's own favouring is not an item that the bearer
merely produces without containing it. A bearer that produced distinct items for
`x` and `y` would already have to discriminate them (ST I q.14 a.6, navigation
only: a common principle must contain what distinguishes its effects), and that
discrimination, not the produced item, is then the first stand-in. -/
def NoMerelyProducedStandIn (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (Present : S → X → Prop) (stand : B → X → C) (Contains Produces : B → C → Prop) : Prop :=
  ∀ b φ s x, Has b (favours φ) → ¬ Present s x →
    ¬ (Produces b (stand b x) ∧ ¬ ContainsGenerically Contains b (stand b x))

/-- OPEN containment-recognition bridge: if a bearer's favouring determination
depends on value with end content fixed (BECAUSE_OF_GOODNESS_2) for a pair `z`,
`w` in either order, `z` is not a present input, the stand-in of `z` is contained
in the bearer, and it differs from the stand-in of `w` (it individuates `z`
against `w`), then that contained stand-in is a content about `z` that the bearer
itself apprehends, that is, contains intentionally (CONTAINED_IN_2, which includes
the containment and adds aboutness and apprehension). Its antecedent adds
containment (CONTAINED_IN_1) and individuation, but given
the other premises of the registered derivation every good-general bearer meets
them, so it narrows nothing there; its consequent is more specific (the
apprehended content is the stand-in). Given those premises it is strictly
stronger than the cognition criterion. It is the step from a contained,
individuating, value-guiding item to intentional presence, which a virtual
(power-to-produce, mode-of-imitability) reading of the containment denies. -/
def ContainedStandInIsApprehended (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (stand : B → X → C) (Contains : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ b φ s z w, Has b (favours φ) →
    (BecauseOfGoodness good fitOf φ s z w ∨ BecauseOfGoodness good fitOf φ s w z) →
    ¬ Present s z → ContainsGenerically Contains b (stand b z) → stand b z ≠ stand b w →
      About (stand b z) z ∧ ContainsIntentionally Contains About Apprehends b (stand b z)

/-- The containment-recognition bridge with its consequent weakened to the
cognition criterion's: some content about some candidate is apprehended by the
bearer. Lean-only comparison notion (semantic challenge probe): the criterion
implies it outright, and with the other five premises of the registered
derivation it implies the criterion, so given those premises the registered
bridge `ContainedStandInIsApprehended` is strictly stronger than the criterion. -/
def ContainedStandInYieldsApprehension (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (stand : B → X → C) (Contains : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ b φ s z w, Has b (favours φ) →
    (BecauseOfGoodness good fitOf φ s z w ∨ BecauseOfGoodness good fitOf φ s w z) →
    ¬ Present s z → ContainsGenerically Contains b (stand b z) → stand b z ≠ stand b w →
      ∃ c y, About c y ∧ Apprehends b c

/-! ## Finite controls

The carrier is Lane 4's: the source `true` of the #2153/#1873 two-being profile,
its determinations `Det`, the good-tracking source profile `personalSrc` (it has
`esse`, the good-general token and the favouring `better`), the Lane 2b
scenarios, outcomes, `better` and `fits`, and no present inputs. Only the
stand-in assignment, the item relation, the loci and the apprehension relation
vary between rows. -/
namespace Control

open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better)
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok hasSrc personalSrc noInputs)

/-- Items a candidate can figure through. `inner o`: a determination contained
in the source that stands for `o` (an idea, a mode of imitability, or a power
directed to `o`; the type does not say which). `realm o`: an item independent of
the source (an abstract candidate or value-fact). `made o`: an item the source
produces outside itself. `blob`: the source's one undifferentiated nature. -/
inductive Item
  | inner (o : Outcome)
  | realm (o : Outcome)
  | made (o : Outcome)
  | blob
  deriving DecidableEq

/-- Every bearer's stand-in for `o` is `k o`. -/
def standVia (k : Outcome → Item) : Bool → Outcome → Item := fun _ => k

/-- The item relation induced by `better` along `k`. -/
def relVia (k : Outcome → Item) :
    Bool → GoodFavouring.Profile Scenario Outcome → Scenario → Item → Item → Prop :=
  fun _ _ s e e' => ∃ x y, k x = e ∧ k y = e' ∧ better s x y

/-- The source contains its inner items and its one nature. -/
def contains (b : Bool) (e : Item) : Prop :=
  b = true ∧ (e = Item.blob ∨ ∃ o, e = Item.inner o)

/-- The source produces the `made` items. -/
def produces (b : Bool) (e : Item) : Prop := b = true ∧ ∃ o, e = Item.made o

/-- An item is about `o` when it is one of the items standing for `o`. This is a
stretched reading of `About` (DEF `3ece6dfe`, a content that represents a
candidate): it counts non-representational items (an independent value-fact, a
produced item, a power) as "about" what they stand for. A rival in the
contained-unapprehended row may deny `About` as well as `Apprehends`. -/
def aboutItem (e : Item) (o : Outcome) : Prop :=
  e = Item.inner o ∨ e = Item.realm o ∨ e = Item.made o

/-- The source apprehends its inner items (the personal assignment). -/
def appInner (b : Bool) (e : Item) : Prop := b = true ∧ ∃ o, e = Item.inner o

/-- Nothing apprehends anything. -/
def appNone (_ : Bool) (_ : Item) : Prop := False

/-- Control for the relocation finding: the one nature `blob` counts as about
every outcome. -/
def aboutOrBlob (e : Item) (o : Outcome) : Prop := e = Item.blob ∨ aboutItem e o

/-- Control for the relocation finding: the source apprehends only its one nature. -/
def appBlob (b : Bool) (e : Item) : Prop := b = true ∧ e = Item.blob

/-- A non-contrastive favouring: in `cBetter` every outcome over every outcome
(itself included), in other scenarios nothing. -/
def allIn : GoodFavouring.Profile Scenario Outcome := fun s _ _ => s = Scenario.cBetter

/-- A source whose only favouring is `allIn`. -/
def allInSrc : Set Det := {Det.esse, Det.fav allIn}

/-- Item realization on Lane 4's carrier. -/
def realized (src : Set Det) (k : Outcome → Item)
    (rel : Bool → GoodFavouring.Profile Scenario Outcome → Scenario → Item → Item → Prop) : Prop :=
  FavouringRealizedOnItems (hasSrc src) favTok (standVia k) rel
/-- Irreflexivity on the carrier. -/
def irrefl (src : Set Det) : Prop := FavouringIrreflexive (hasSrc src) favTok
/-- The own-favouring bridge on the carrier. -/
def own (src : Set Det) (k : Outcome → Item) : Prop :=
  NoIndependentStandIn (hasSrc src) favTok noInputs (standVia k) contains produces
/-- The source-of-differences bridge on the carrier. -/
def notMade (src : Set Det) (k : Outcome → Item) : Prop :=
  NoMerelyProducedStandIn (hasSrc src) favTok noInputs (standVia k) contains produces
/-- The containment-recognition bridge on the carrier. -/
def recog (src : Set Det) (k : Outcome → Item) (app : Bool → Item → Prop) : Prop :=
  ContainedStandInIsApprehended (hasSrc src) favTok better fits noInputs (standVia k) contains
    aboutItem app
/-- The cognition criterion on the carrier, with items as contents. -/
def crit (src : Set Det) (app : Bool → Item → Prop) : Prop :=
  GoodGeneralFavouringIsApprehension (hasSrc src) favTok better fits noInputs aboutItem app

/-- The individuation trilemma on one carrier. Every row has a source with a
good-general favouring (the good-tracking `better`, or in row 6 `allIn`). Each
failing row fails exactly one of the five non-logical premises; the criterion
fails in it.

1. Personal: ideas contained in the source, individuating each outcome and
   apprehended. Every premise and the criterion hold.
2. Contained but unapprehended (noncognitive imitability exemplars, or powers
   directed to their manifestations): the same stand-ins, relation and loci as
   row 1; only apprehension is empty. Only the recognition bridge fails.
3. Independent realm (Leslie-type requiredness of abstract value-facts; a
   demiurge's independent Forms, if apprehension were added): only the
   own-favouring bridge fails.
4. Produced realm (the source makes items outside itself and they guide its
   favouring): only the source-of-differences bridge fails.
5. Nowhere, good-tracking favouring: one undifferentiated item for every outcome.
   No item relation whatever realizes the favouring; the other premises hold.
6. Nowhere, realized: the favouring `allIn`, realized on the one item, is
   good-general in the formal sense but favours every outcome over itself in
   `cBetter`. Only irreflexivity fails.

Artifacts: in rows 3 to 6 the recognition bridge holds only vacuously (no
contained individuating stand-in), and the criterion fails there because those
rows assign `appNone`, not because of the failed premise; with `appInner` the
criterion would hold in rows 3 to 5. The rows show that each premise is needed
for the derivation, not that its failure refutes the criterion. -/
def AxiarchicControls : Prop :=
  (realized personalSrc Item.inner (relVia Item.inner) ∧ irrefl personalSrc ∧
    own personalSrc Item.inner ∧ notMade personalSrc Item.inner ∧
    recog personalSrc Item.inner appInner ∧ crit personalSrc appInner) ∧
  (realized personalSrc Item.inner (relVia Item.inner) ∧ irrefl personalSrc ∧
    own personalSrc Item.inner ∧ notMade personalSrc Item.inner ∧
    ¬ recog personalSrc Item.inner appNone ∧ ¬ crit personalSrc appNone) ∧
  (realized personalSrc Item.realm (relVia Item.realm) ∧ irrefl personalSrc ∧
    ¬ own personalSrc Item.realm ∧ notMade personalSrc Item.realm ∧
    recog personalSrc Item.realm appNone ∧ ¬ crit personalSrc appNone) ∧
  (realized personalSrc Item.made (relVia Item.made) ∧ irrefl personalSrc ∧
    own personalSrc Item.made ∧ ¬ notMade personalSrc Item.made ∧
    recog personalSrc Item.made appNone ∧ ¬ crit personalSrc appNone) ∧
  ((∀ rel, ¬ realized personalSrc (fun _ => Item.blob) rel) ∧ irrefl personalSrc ∧
    own personalSrc (fun _ => Item.blob) ∧ notMade personalSrc (fun _ => Item.blob) ∧
    recog personalSrc (fun _ => Item.blob) appNone ∧ ¬ crit personalSrc appNone) ∧
  (realized allInSrc (fun _ => Item.blob) (fun _ _ s _ _ => s = Scenario.cBetter) ∧
    ¬ irrefl allInSrc ∧ own allInSrc (fun _ => Item.blob) ∧
    notMade allInSrc (fun _ => Item.blob) ∧ recog allInSrc (fun _ => Item.blob) appNone ∧
    ImpersonalFoundationJoint.Control.gg allIn ∧ allIn Scenario.cBetter .c .c ∧
    ¬ crit allInSrc appNone)

end Control

/-! ## What value-dependence of an aligned order witnesses

A profile that tracks an intrinsic order `f` other than value (aligned powers, A3)
is good-general as soon as `f` and the value order coincide on one witnessing
pair at one scenario and fail together at one scenario agreeing on the control
(law 3 of `GoodDependenceLaws`). It need not coincide with value anywhere else.
The finite witness below has two strict orders on three candidates that agree on
the witnessing pair, fail together in the second scenario, and rank another pair
oppositely in the first. -/
namespace AlignmentControl

/-- Two scenarios with the same end content. -/
inductive Sc
  | s0
  | s1

/-- Three candidates. -/
inductive Ca
  | a
  | b
  | c
  deriving DecidableEq

/-- The value order: at `s0`, `a` over `b` and `c` over `a`; nothing at `s1`. -/
def value : Sc → Ca → Ca → Prop
  | .s0, .a, .b => True
  | .s0, .c, .a => True
  | _, _, _ => False

/-- An intrinsic power order: at `s0`, `a` over `b` and `a` over `c`; nothing at
`s1`. -/
def power : Sc → Ca → Ca → Prop
  | .s0, .a, .b => True
  | .s0, .a, .c => True
  | _, _, _ => False

/-- One end content for both scenarios. -/
def sameEnd (_ : Sc) : Unit := ()

/-- No candidate is a present input. -/
def noneHere (_ : Sc) (_ : Ca) : Prop := False

/-- The power-tracking profile is good-general (the two orders coincide on `a`
over `b` at `s0` and both fail at `s1`), both orders are irreflexive and
asymmetric, and they rank `a` and `c` oppositely at `s0`. -/
def WitnessOnlyAlignment : Prop :=
  ImpersonalFoundationJoint.GoodGeneral value sameEnd noneHere power ∧
  (∀ s x y, value s x y → ¬ value s y x) ∧ (∀ s x y, power s x y → ¬ power s y x) ∧
  power .s0 .a .c ∧ value .s0 .c .a

end AlignmentControl

end TruthCore.Causality.AxiarchicFoundation
