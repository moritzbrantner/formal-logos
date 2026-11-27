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
inverse image (`InvImage`) of a relation among the stand-ins. This is a reading
of a real favouring relation of a real bearer: its terms are real items, even
when the candidates are not.

**Three loci.** Relative to a bearer an item is contained in it (`Contains`),
produced by it (`Produces`), or independent of it (neither). With excluded
middle these cover every item. The individuation trilemma:

1. *independent realm* (Leslie-type requiredness of abstract value-facts, a
   demiurge's independent Forms): excluded by the open `NoIndependentStandIn`;
2. *in the source* (ideas, modes of imitability, powers directed to their
   manifestations): reached when the other two are excluded; whether it is
   apprehension is the open `ContainedStandInIsApprehended`;
3. *nowhere* (one undifferentiated item for every candidate): with item
   realization and irreflexivity it gives no favouring of one candidate over
   another (`unindividuatedNotFavoured`, in the results module).

A produced item outside the bearer (a realm the source makes) is excluded by the
open `NoMerelyProducedStandIn` (source-of-differences reasoning).

`Contains`, `Produces`, `About` and `Apprehends` are free. Nothing in a type
separates intentional containment (an idea) from virtual containment (a power
directed to a manifestation): that is exactly the step the open recognition
bridge takes. Every model in `Control` is a finite structural surrogate; it
witnesses only the stated formal interpretation, never a metaphysical
possibility. -/

@[expose] public section

namespace TruthCore.Causality.AxiarchicFoundation

open TruthCore.Causality.GoodFavouring (BecauseOfGoodness)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral GoodGeneralFavouringIsApprehension)

variable {B D S X Z C : Type}

/-- OPEN item realization: for every bearer `b` and every favouring determination
`favours φ` of `b`, in every scenario `s`, `φ s` favours `x` over `y` exactly when
the relation `rel b s` holds between the stand-ins `stand b x` and `stand b y`
(the profile is the inverse image of an item relation). A real favouring relation
of a real bearer has real items as its terms, even when the candidates do not
exist. -/
def FavouringRealizedOnItems (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (stand : B → X → C) (rel : B → S → C → C → Prop) : Prop :=
  ∀ b φ, Has b (favours φ) → ∀ s x y, φ s x y ↔ InvImage (rel b s) (stand b) x y

/-- OPEN irreflexivity: no favouring determination favours a candidate over
itself in any scenario. Weaker than the asymmetry (net favouring) that the #2163
favouring standard assumes. -/
def FavouringIrreflexive (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D) :
    Prop :=
  ∀ b φ, Has b (favours φ) → ∀ s x, ¬ φ s x x

/-- An item `e` is independent of the bearer `b`: `b` neither contains nor produces it. -/
def Independent (Contains Produces : B → C → Prop) (b : B) (e : C) : Prop :=
  ¬ Contains b e ∧ ¬ Produces b e

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
    ¬ (Produces b (stand b x) ∧ ¬ Contains b (stand b x))

/-- OPEN containment-recognition bridge: if a bearer's favouring determination
depends on value with end content fixed (BECAUSE_OF_GOODNESS_2) for a pair `z`,
`w` in either order, `z` is not a present input, the stand-in of `z` is contained
in the bearer, and it differs from the stand-in of `w` (it individuates `z`
against `w`), then that contained stand-in is a content about `z` that the bearer
itself apprehends. It is narrower than the cognition criterion in its antecedent
(containment and individuation are required) and more specific in its consequent
(the apprehended content is the stand-in). It is the step from a contained,
individuating, value-guiding item to intentional presence, which a virtual
(power-to-produce) reading of the containment denies. -/
def ContainedStandInIsApprehended (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (stand : B → X → C) (Contains : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ b φ s z w, Has b (favours φ) →
    (BecauseOfGoodness good fitOf φ s z w ∨ BecauseOfGoodness good fitOf φ s w z) →
    ¬ Present s z → Contains b (stand b z) → stand b z ≠ stand b w →
      About (stand b z) z ∧ Apprehends b (stand b z)

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
def relVia (k : Outcome → Item) : Bool → Scenario → Item → Item → Prop :=
  fun _ s e e' => ∃ x y, k x = e ∧ k y = e' ∧ better s x y

/-- The source contains its inner items and its one nature. -/
def contains (b : Bool) (e : Item) : Prop :=
  b = true ∧ (e = Item.blob ∨ ∃ o, e = Item.inner o)

/-- The source produces the `made` items. -/
def produces (b : Bool) (e : Item) : Prop := b = true ∧ ∃ o, e = Item.made o

/-- An item is about `o` when it is one of the items standing for `o`. -/
def aboutItem (e : Item) (o : Outcome) : Prop :=
  e = Item.inner o ∨ e = Item.realm o ∨ e = Item.made o

/-- The source apprehends its inner items (the personal assignment). -/
def appInner (b : Bool) (e : Item) : Prop := b = true ∧ ∃ o, e = Item.inner o

/-- Nothing apprehends anything. -/
def appNone (_ : Bool) (_ : Item) : Prop := False

/-- A non-contrastive favouring: in `cBetter` every outcome over every outcome
(itself included), in other scenarios nothing. -/
def allIn : GoodFavouring.Profile Scenario Outcome := fun s _ _ => s = Scenario.cBetter

/-- A source whose only favouring is `allIn`. -/
def allInSrc : Set Det := {Det.esse, Det.fav allIn}

/-- Item realization on Lane 4's carrier. -/
def realized (src : Set Det) (k : Outcome → Item) (rel : Bool → Scenario → Item → Item → Prop) :
    Prop :=
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
   `cBetter`. Only irreflexivity fails. -/
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
  (realized allInSrc (fun _ => Item.blob) (fun _ s _ _ => s = Scenario.cBetter) ∧
    ¬ irrefl allInSrc ∧ own allInSrc (fun _ => Item.blob) ∧
    notMade allInSrc (fun _ => Item.blob) ∧ recog allInSrc (fun _ => Item.blob) appNone ∧
    ImpersonalFoundationJoint.Control.gg allIn ∧ allIn Scenario.cBetter .c .c ∧
    ¬ crit allInSrc appNone)

end Control

end TruthCore.Causality.AxiarchicFoundation
