module

public import TruthCore.Causality.AxiarchicFoundation

/-! # Do possibilities need a mind? Non-real plurality at a simple root (#2145, lane H1)

Analyst formulations, attribution deferred (logic first). Author names (Leibniz,
Augustine, Plantinga, Brentano, Molnar, Scotus, Zalta, Bird) are navigation, not
verified source claims. See `docs/notes/causal-perfection-transfer.md`, section
"Do possibilities need a mind? Conceptualism and non-real plurality at a simple root".

This is a horizontal argument family for the cognition route. Lane C located the
dispute between the personal source and the noncognitive imitability-exemplar
rival (A4) at the containment-recognition bridge `ContainedStandInIsApprehended`
and recorded "same demand, different proposed payments": both need many
value-ranked, individuating items in one simple nature.

**The demand, derived.** A bearer is *constitutively simple* (reused
`ObjectiveEminence.ConstitutivelySimple`) when it has at most one real
constituent. If a good-general favouring of a simple bearer has only non-present
candidates (as at a root before production), item realization and irreflexivity
give two distinct stand-ins, the two locus bridges place both in the bearer, and
simplicity forbids both being real constituents. So some stand-in is contained
in the bearer without being a real constituent of it (`NonRealContained`). This
holds for both sides: it excludes ideas as a real plurality of representations
and powers as a real plurality of directed properties (Molnar-type physical
intentionality) alike (results module: `simpleBearerHasNonRealStandIn`,
`realStandInsGiveNoGoodGeneralFavouring`).

**The conceptualist premise.** `NonRealContainmentIsApprehension`: whatever is
in a bearer without being a real constituent of it is apprehended by that
bearer. It is a general thesis about non-real being, not a thesis about
favouring. It is related to the classical dictum that beings of reason have
being only in an intellect, but it is not a consequence of it: it drops the
dependence, indexes apprehension to the containing bearer, and ranges over every
non-real contained item rather than over beings of reason (the two ranges
coincide only if every non-real item is a being of reason, which A4 denies). Its
warrant is assessed in other domains (negations, possibilia,
propositions, relations to non-existents, distinctions within one thing). The
rival A4 denies it: its modes are non-real, contained and mind-independent (a
Scotist formal distinction a parte rei is the developed precedent). The content
premise `NonRealStandInIsAbout` says that such a stand-in is about its
candidate; a template reading of the modes denies it.

`RealConstituent`, `Contains`, `About` and `Apprehends` are free. Nothing in a
type says what non-real being is; the premises say only where it is found. Every
model in `Control` is a finite structural surrogate; it witnesses only the
stated formal interpretation, never a metaphysical possibility. -/

@[expose] public section

namespace TruthCore.Causality.PossibiliaContent

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral)
open TruthCore.Causality.AxiarchicFoundation (ContainsGenerically)
open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence (ConstitutivelySimple)

variable {W B D S X Z C : Type}

/-- NON-REAL CONTAINMENT: the item `e` is in the bearer `b` (CONTAINED_IN_1,
intentionally or virtually) without being a real constituent of `b`. On the
personal account a divine idea is such an item (a relation of reason, in being
understood); on the rival A4 a mode of imitability is (mind-independent). -/
def NonRealContained (Contains RealConstituent : B → C → Prop) (b : B) (e : C) : Prop :=
  ContainsGenerically Contains b e ∧ ¬ RealConstituent b e

/-- OPEN reading of commitment (a) of #2145 for actual roots: every actual root
at `w` is constitutively simple, with at most one real constituent. Non-real
items (objects of understanding, modes, distinctions of reason) are not counted. -/
def RootsConstitutivelySimple (m : Profile W B) (w : W) (RealConstituent : B → C → Prop) :
    Prop :=
  ∀ r, ActualRoot m w r → ConstitutivelySimple RealConstituent r

/-- OPEN, the creative carrier: no candidate of the favourings under consideration
is a present input in any scenario (the candidates are possible products, none
of which yet exists). `Present` is shared by every bearer and not indexed by the
bearer, so this is a global property of the carrier; it is appropriate where the
candidates are a root's possible effects and false on a carrier with present
inputs. -/
def NoPresentCandidates (Present : S → X → Prop) : Prop := ∀ s x, ¬ Present s x

/-- OPEN conceptualist premise about non-real being (analyst formulation):
whatever is in a bearer without being a real constituent of it is apprehended by
that bearer. Compared with the classical dictum that beings of reason have being
only in an intellect, it is weaker in dropping the dependence (it says only
"apprehended") and stronger in indexing apprehension to the containing bearer
(the dictum allows some other intellect). It also ranges over every non-real
contained item, not only over beings of reason; the dictum reaches A4's modes
only if every non-real item is a being of reason, which A4 denies. So it is not
a consequence of the dictum. It is general: it does not mention favouring, value
or roots. A
bearer that apprehends nothing contains no non-real item. Denied by an account
on which a simple nature contains mind-independent non-real modes (A4, the #1892
objective-eminence status). -/
def NonRealContainmentIsApprehension (Contains RealConstituent : B → C → Prop)
    (Apprehends : B → C → Prop) : Prop :=
  ∀ b e, NonRealContained Contains RealConstituent b e → Apprehends b e

/-- OPEN content premise, in its weakest form for the route: a stand-in through
which a non-present candidate figures in a bearer's favouring, if it is in the
bearer without being a real constituent of it, is about that candidate (DEF
`3ece6dfe`: it represents the candidate). Denied by a template reading, on which
a mode individuates the candidate only as whatever would match it. -/
def NonRealStandInIsAbout (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (Present : S → X → Prop) (stand : B → X → C) (Contains RealConstituent : B → C → Prop)
    (About : C → X → Prop) : Prop :=
  ∀ b φ s x, Has b (favours φ) → ¬ Present s x →
    NonRealContained Contains RealConstituent b (stand b x) → About (stand b x) x

/-- The ROOT cognition criterion: every actual root at `w` whose favouring
determination is good-general apprehends some content about some candidate. The
weaker sibling of the cognition criterion `GoodGeneralFavouringIsApprehension`,
restricted to actual roots. -/
def RootGoodGeneralFavouringIsApprehension (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ φ, Has r (favours φ) → GoodGeneral good fitOf Present φ →
    ∃ c y, About c y ∧ Apprehends r c

/-- Lean-only relocation notion (pre-report probe): the conceptualist premise
restricted to the root route. At an actual root with a good-general favouring,
a non-real contained stand-in of a non-present candidate yields some apprehended
content about some candidate. Given the other premises it is equivalent to the
root criterion (results module), so it would be a relocation; the registered
premise is the general `NonRealContainmentIsApprehension`. -/
def NonRealStandInYieldsApprehension (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (stand : B → X → C) (Contains RealConstituent : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ φ s x, Has r (favours φ) → GoodGeneral good fitOf Present φ →
    ¬ Present s x → NonRealContained Contains RealConstituent r (stand r x) →
      ∃ c y, About c y ∧ Apprehends r c

/-! ## Finite controls

Lane C's carrier (`AxiarchicFoundation.Control`): the source `true` of the
#2153 two-being profile, the good-tracking favouring `better`, the Lane 2b
scenarios and outcomes, and its item type (`inner o`, `realm o`, `made o`,
`blob`). Rows vary the real constituents, the containment relation, the present
inputs, aboutness and apprehension. -/
namespace Control

open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better)
open TruthCore.Causality.ImpersonalFoundationJoint.Control (Det favTok hasSrc personalSrc noInputs)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.AxiarchicFoundation
open TruthCore.Causality.AxiarchicFoundation.Control

/-- Only the source's one nature is a real constituent (a simple source). -/
def realBlob (b : Bool) (e : Item) : Prop := b = true ∧ e = Item.blob

/-- Every contained item is a real constituent (a composite source whose inner
items are real directed properties or real representations). -/
def realContained (b : Bool) (e : Item) : Prop := contains b e

/-- The source contains only its one nature. -/
def containsBlob (b : Bool) (e : Item) : Prop := b = true ∧ e = Item.blob

/-- Every outcome except `c` is a present input. -/
def onlyCAbsent (_ : Scenario) (o : Outcome) : Prop := o ≠ Outcome.c

/-- Stand-ins with only `c` absent: `c` through the source's nature, every present
outcome through itself (an item independent of the source). -/
def patientStand (o : Outcome) : Item := if o = Outcome.c then Item.blob else Item.realm o

/-- Nothing is about anything. -/
def aboutNone (_ : Item) (_ : Outcome) : Prop := False

/-- The source apprehends only the inner item standing for `c`. -/
def appInnerC (b : Bool) (e : Item) : Prop := b = true ∧ e = Item.inner Outcome.c

/-- Lane C's five individuation premises, with a given containment relation and
present-input relation. -/
def laneC (Cont : Bool → Item → Prop) (Pres : Scenario → Outcome → Prop)
    (k : Outcome → Item) : Prop :=
  TruthCore.Logic.ExcludedMiddle ∧
  FavouringRealizedOnItems (hasSrc personalSrc) favTok (standVia k) (relVia k) ∧
  FavouringIrreflexive (hasSrc personalSrc) favTok ∧
  NoIndependentStandIn (hasSrc personalSrc) favTok Pres (standVia k) Cont produces ∧
  NoMerelyProducedStandIn (hasSrc personalSrc) favTok Pres (standVia k) Cont produces

/-- Simplicity of roots on the carrier. -/
def simple (real : Bool → Item → Prop) : Prop := RootsConstitutivelySimple rootProfile true real
/-- The conceptualist premise on the carrier. -/
def nra (Cont real app : Bool → Item → Prop) : Prop :=
  NonRealContainmentIsApprehension Cont real app
/-- The content premise on the carrier. -/
def ca (Cont : Bool → Item → Prop) (Pres : Scenario → Outcome → Prop) (k : Outcome → Item)
    (real : Bool → Item → Prop) (about : Item → Outcome → Prop) : Prop :=
  NonRealStandInIsAbout (hasSrc personalSrc) favTok Pres (standVia k) Cont real about
/-- The root criterion on the carrier. -/
def rootCrit (Pres : Scenario → Outcome → Prop) (about : Item → Outcome → Prop)
    (app : Bool → Item → Prop) : Prop :=
  RootGoodGeneralFavouringIsApprehension rootProfile true (hasSrc personalSrc) favTok better fits
    Pres about app

/-- One carrier, five rows. Every row keeps Lane C's five individuation premises
and has the good-tracking favouring at the root `true`.

1. Personal (ideas as objects of understanding): the inner items are contained,
   non-real (only the nature is real), about their outcomes and apprehended.
   Every premise and the root criterion hold.
2. A4 (mind-independent non-real modes): row 1 with nothing apprehended. Only
   the conceptualist premise fails, and the root criterion fails.
3. Real plurality (Molnar-type real directed powers, or real representations, in
   a composite source): every contained item is real. Only root simplicity fails;
   the conceptualist and content premises hold vacuously (nothing non-real is
   contained); the root criterion fails with nothing apprehended.
4. Template reading: row 1 with nothing about anything. Only the content premise
   fails; the root criterion fails (apprehension without aboutness).
5. Present inputs: every outcome except `c` is present, `c` stands through the
   source's one nature, present outcomes through themselves; the source contains
   only its nature. Only `NoPresentCandidates` fails; the root criterion fails
   with nothing apprehended.

Artifacts: rows 1 and 2 differ only in apprehension, by construction (A4 is
defined as a structural duplicate). Row 4 assigns apprehension to isolate the
content premise; the template rival as such also denies apprehension. Row 3
keeps every contained item real, so the simple-source theorem's conclusion is
blocked by the failed simplicity, not shown false of composite thinkers. In rows
2, 3 and 5 the root criterion fails because the row assigns no apprehension;
row 5 shows that `NoPresentCandidates` is needed for the derivation, not that
present inputs exclude apprehension. -/
def PossibiliaControls : Prop :=
  (laneC contains noInputs Item.inner ∧ simple realBlob ∧ NoPresentCandidates noInputs ∧
    nra contains realBlob appInner ∧ ca contains noInputs Item.inner realBlob aboutItem ∧
    rootCrit noInputs aboutItem appInner) ∧
  (laneC contains noInputs Item.inner ∧ simple realBlob ∧ NoPresentCandidates noInputs ∧
    ¬ nra contains realBlob appNone ∧ ca contains noInputs Item.inner realBlob aboutItem ∧
    ¬ rootCrit noInputs aboutItem appNone) ∧
  (laneC contains noInputs Item.inner ∧ ¬ simple realContained ∧ NoPresentCandidates noInputs ∧
    nra contains realContained appNone ∧ ca contains noInputs Item.inner realContained aboutItem ∧
    ¬ rootCrit noInputs aboutItem appNone) ∧
  (laneC contains noInputs Item.inner ∧ simple realBlob ∧ NoPresentCandidates noInputs ∧
    nra contains realBlob appInner ∧ ¬ ca contains noInputs Item.inner realBlob aboutNone ∧
    ¬ rootCrit noInputs aboutNone appInner) ∧
  (laneC containsBlob onlyCAbsent patientStand ∧ simple realBlob ∧
    ¬ NoPresentCandidates onlyCAbsent ∧ nra containsBlob realBlob appNone ∧
    ca containsBlob onlyCAbsent patientStand realBlob aboutItem ∧
    ¬ rootCrit onlyCAbsent aboutItem appNone)

/-- Relocation probe (Comparator companion): with the personal row's stand-ins,
the root criterion and every other premise hold, while the general conceptualist
premise fails, because the source apprehends the stand-in of `c` but not the
non-real stand-in of `d`. So the root criterion with the other premises does not
give the conceptualist premise: given them, it is strictly stronger than the
root criterion. -/
def RootCriterionWithoutConceptualism : Prop :=
  laneC contains noInputs Item.inner ∧ simple realBlob ∧ NoPresentCandidates noInputs ∧
    ca contains noInputs Item.inner realBlob aboutItem ∧ rootCrit noInputs aboutItem appInnerC ∧
    ¬ nra contains realBlob appInnerC

end Control

end TruthCore.Causality.PossibiliaContent
