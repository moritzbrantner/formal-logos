module

public import TruthCore.Causality.PurityCriteria

/-! # Natural and rational appetite under one standard of favouring (#2145, lane H3)

Analyst formulations, attribution deferred (logic first). See
`docs/notes/causal-perfection-transfer.md`, section "Natural or rational
appetite? The purity premises and the object of an original source's
favouring".

Premise lane P left the purity family at a crux. Measured per bearer (a
favouring is measured by the formal object of its kind of operation), the
verdict on a favouring fixed to end content D "turns on whether a root's
favouring is a natural or a rational appetite". This module separates the two
things that phrase joins.

* **Mode: what fixes the favouring.** A favouring profile is *fixed by* a
  scenario feature `f` when scenarios that agree on `f` receive the same
  favouring (`FixedBy`, Mathlib's `Function.FactorsThrough`). A *natural*
  appetite is fixed by the bearer's natural state (`NaturalState`: its
  non-apprehensive state in each scenario, the response of its form or nature
  to the candidates). A *rational* appetite is fixed by its apprehension state
  (`ApprehensionState`: what the bearer apprehends of the candidates in each
  scenario). The two states are distinct structures, so a natural state cannot
  be passed where an apprehension state is required. The two modes are not
  exclusive in Lean: a favouring is fixed by both when the two states are
  correlated in the scenario space.
* **Object: what the favouring is measured by.** A formal-object assignment
  `obj` gives the ranking that measures each favouring (the formal object of its
  kind, not its particular content). The per-bearer standard bridge
  `PureFavouringTracksItsObject` says that a pure favouring makes exactly the
  verdicts of its formal object. The object premise
  `ActualRootFavouringObjectIsValue` says that the formal object of every
  favouring of an actual root is the value order (STANDARD_OF_FAVOURING_1).

Neither the bridge nor the object premise mentions a mode. Whether natural or
rational appetite is the crux of the purity family is therefore a question about
how mode and object are related. The results module tests that relation in both
directions:

* the *fixer law*: whatever fixes a good-general favouring must itself separate
  two scenarios of one end-realization class at which value differs on the
  witnessing pair;
* *ad unum*: if a natural state is fixed by end-realization
  (`NaturalStateAdUnum`, determination of a natural form to one end), no natural
  appetite fixed by it is good-general, so under the mode dichotomy every
  good-general favouring is rational. A natural state that responds to the
  candidates' full content is the countermodel.

Every model in `Control` is a finite structural surrogate. It witnesses only the
stated formal interpretation, never a metaphysical possibility. Which account a
row represents (Lane 2b's D-directed nature, imitability exemplarism, rational
exercise, a determined will) is an interpretive assignment. -/

@[expose] public section

namespace TruthCore.Causality.AppetiteStandard

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.GoodFavouring (Tracks)
open TruthCore.Causality.PurityCriteria (ValueStandardOrder)

variable {W B D S X K Y : Type}

/-! ## Mode: what fixes a favouring -/

/-- The favouring profile `φ` is FIXED BY the scenario feature `f`: any two
scenarios on which `f` agrees receive the same favouring (`φ` factors through
`f`). It says what the favouring's verdicts can respond to, not that `f` causes
them. -/
def FixedBy (φ : GoodFavouring.Profile S X) (f : S → K) : Prop :=
  Function.FactorsThrough φ f

/-- A bearer's NATURAL STATE: in each variation scenario, its non-apprehensive
state, that is, the response of its form or nature to the candidates, whatever
it is (a power directed to manifestations, a mode in which it is imitable, an
end-directed tendency). It is intended to contain nothing the bearer
apprehends; the type does not enforce that. A distinct structure from
`ApprehensionState`. -/
structure NaturalState (S K : Type) where
  /-- The non-apprehensive state in each scenario. -/
  state : S → K

/-- A bearer's APPREHENSION STATE: in each variation scenario, what it
apprehends of the candidates (the contents present to it as known). A bearer
that apprehends nothing has a constant apprehension state. A distinct structure
from `NaturalState`. -/
structure ApprehensionState (S Y : Type) where
  /-- The apprehension state in each scenario. -/
  state : S → Y

/-- NATURAL APPETITE (favouring-profile level): the favouring is fixed by the
bearer's natural state. Its verdicts follow the bearer's form or nature without
passing through apprehension. -/
def NaturalAppetite (n : NaturalState S K) (φ : GoodFavouring.Profile S X) : Prop :=
  FixedBy φ n.state

/-- RATIONAL APPETITE (favouring-profile level, appetite following
apprehension): the favouring is fixed by the bearer's apprehension state. Its
verdicts follow what the bearer apprehends. -/
def RationalAppetite (a : ApprehensionState S Y) (φ : GoodFavouring.Profile S X) : Prop :=
  FixedBy φ a.state

/-- The apprehension state is the same in every scenario. A bearer that
apprehends nothing (a noncognitive bearer) has one; so does a bearer whose
apprehension does not vary with the candidates. -/
def ConstantApprehension (a : ApprehensionState S Y) : Prop :=
  ∀ s t, a.state s = a.state t

/-- OPEN, Lean-only: DETERMINATION TO ONE END (ad unum) of a natural state. Any
two scenarios that agree on end-realization give the same natural state: the
nature responds to the candidates only through whether they realize its end. -/
def NaturalStateAdUnum {Z : Type} (n : NaturalState S K) (fitOf : S → Z) : Prop :=
  Function.FactorsThrough n.state fitOf

/-! ## Object: what a favouring is measured by -/

/-- OPEN per-bearer standard bridge (the per-bearer reading of the loss and
arbitrariness bridges together): every favouring determination that is pure
(DEF-PURE-PERFECTION, the same `Pure` parameter as the #2153 premises) makes
exactly the verdicts of its own formal object `obj φ`. The formal object is the
ranking that measures the favouring's *kind* of operation (for a will, the good;
for a natural tendency, the end of the nature), not its particular content: with
`obj φ := φ` the bridge would be trivial, and that reading is not intended. -/
def PureFavouringTracksItsObject (Pure : D → Prop) (favours : GoodFavouring.Profile S X → D)
    (obj : GoodFavouring.Profile S X → S → X → X → Prop) : Prop :=
  ∀ φ, Pure (favours φ) → Tracks φ (obj φ)

/-- OPEN object premise: the formal object of every favouring determination of an
actual root at `w` is the value order `v` (STANDARD_OF_FAVOURING_1, the relation
`v.better`). It does not say whether that favouring is a natural or a rational
appetite. -/
def ActualRootFavouringObjectIsValue (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (obj : GoodFavouring.Profile S X → S → X → X → Prop)
    (v : ValueStandardOrder S X) : Prop :=
  ∀ r, ActualRoot m w r → ∀ φ, Has r (favours φ) → obj φ = v.better

/-- Lean-only kind rule for rational appetite: the formal object of a favouring
that is a rational appetite of bearer `b` (fixed by `b`'s apprehension state) is
the value order. It is the "formal object of willing is the good" half of lane
P's per-bearer reading. Natural appetites are left free: their formal object is
the end of the nature, whatever it is. -/
def RationalObjectIsValue (app : B → ApprehensionState S Y)
    (obj : GoodFavouring.Profile S X → S → X → X → Prop) (v : ValueStandardOrder S X) : Prop :=
  ∀ b φ, RationalAppetite (app b) φ → obj φ = v.better

/-! ## Finite controls

The carrier is the #2153 / #2172 one used by `PurityCriteria.Control`: the
two-being `rootProfile` (source `true`, the only actual root at `true`), the
structural `composite`, `prior` and `rep`, the Lane 2b scenarios, outcomes and
profiles, and the determinations `esse`, `goodGen` and one favouring token per
profile. The natural and apprehension states below are assignments only. -/
namespace Control

open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder dNature determinedWill)
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok noInputs hasSrc personalSrc dNatureSrc purePos pureNoGG roots criterion appSource
    appNone)
open TruthCore.Causality.PurityCriteria (MissesVerdict UnbackedVerdict)
open TruthCore.Causality.PurityCriteria.Control (purity varies generalFor chanceSrc pureChance)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)

/-- Good-generality on the carrier (value read off `better`, no present inputs). -/
def gg (φ : GoodFavouring.Profile Scenario Outcome) : Prop :=
  TruthCore.Causality.ImpersonalFoundationJoint.GoodGeneral better fits noInputs φ

/-- A natural state that responds to the candidates' full content. On this
carrier a scenario is individuated by the candidates' content, so the state is
the scenario itself. Interpretation: the imitability-exemplar rival (A4), whose
nature contains distinct, value-ranked modes for the candidates without
apprehending them. -/
def contentState : NaturalState Scenario Scenario := ⟨id⟩

/-- A natural state determined to one end: it records only which candidates
realize D (Lane 2b's D-directed generative nature). -/
def endState : NaturalState Scenario (Outcome → Bool) := ⟨fits⟩

/-- A natural state that plays no role in the favouring (the same in every
scenario). -/
def inertState : NaturalState Scenario Unit := ⟨fun _ => ()⟩

/-- Nothing is apprehended in any scenario (a noncognitive bearer). -/
def noApprehension : ApprehensionState Scenario Unit := ⟨fun _ => ()⟩

/-- The bearer apprehends the candidates' full content, value included, in each
scenario (veridical apprehension; the personal source). -/
def fullApprehension : ApprehensionState Scenario Scenario := ⟨id⟩

/-- The mode-by-object grid on one carrier. Rows are (mode, object) pairs; the
favouring profiles are Lane 2b's.

1. (natural, the good), the imitability-exemplar rival: `better` is a natural
   appetite of the content state and not a rational appetite of the empty
   apprehension state; it is good-general; the content state is not determined
   to one end.
2. (rational, the good), the personal source: `better` is a rational appetite of
   the full apprehension state and not a natural appetite of the inert state; it
   is good-general.
3. (natural, D), the D-directed nature: a natural appetite of the end state,
   which is determined to one end; not a rational appetite of the empty
   apprehension state; not good-general.
4. (rational, D), the determined will: a rational appetite of the full
   apprehension state, not a natural appetite of the inert state, not
   good-general.
5. Per-bearer verdicts. Each good-tracking row makes exactly the verdicts of its
   object, the value order; the D-directed nature makes exactly the verdicts of
   its object, D-realization; the determined will, measured by the good as its
   kind's object, misses a value verdict.
6. Common-value verdicts are the same in both modes: the good-tracking profile
   neither misses nor adds a value verdict; the D-directed profile misses one.
7. The cognition criterion separates rows 1 and 2 on the same profile: with the
   good-tracking source it holds when the source apprehends and fails when
   nothing is apprehended. -/
def AppetiteGrid : Prop :=
  (NaturalAppetite contentState better ∧ ¬ RationalAppetite noApprehension better ∧ gg better ∧
    ¬ NaturalStateAdUnum contentState fits) ∧
  (RationalAppetite fullApprehension better ∧ ¬ NaturalAppetite inertState better ∧ gg better) ∧
  (NaturalAppetite endState dNature ∧ NaturalStateAdUnum endState fits ∧
    ¬ RationalAppetite noApprehension dNature ∧ ¬ gg dNature) ∧
  (RationalAppetite fullApprehension determinedWill ∧ ¬ NaturalAppetite inertState determinedWill ∧
    ¬ gg determinedWill) ∧
  (Tracks better better ∧ Tracks dNature fitOrder ∧ MissesVerdict better determinedWill) ∧
  (¬ MissesVerdict better better ∧ ¬ UnbackedVerdict better better ∧ MissesVerdict better dNature) ∧
  (criterion personalSrc appSource ∧ ¬ criterion personalSrc appNone)

/-- The per-bearer bridge on the carrier, with formal-object assignment `obj`. -/
def ownObj (pure : Det → Prop) (obj : GoodFavouring.Profile Scenario Outcome →
    Scenario → Outcome → Outcome → Prop) : Prop :=
  PureFavouringTracksItsObject pure favTok obj

/-- The object premise on the carrier, with the value order whose relation is `std`. -/
def object (src : Set Det) (obj : GoodFavouring.Profile Scenario Outcome →
    Scenario → Outcome → Outcome → Prop) (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  ActualRootFavouringObjectIsValue rootProfile true (hasSrc src) favTok obj ⟨std⟩

/-- The formal-object assignment that measures every favouring by `std` (one
kind, with object `std`). -/
def objAll (std : GoodFavouring.Profile Scenario Outcome) :
    GoodFavouring.Profile Scenario Outcome → Scenario → Outcome → Outcome → Prop :=
  fun _ => std

/-- Controls for the formal-object route to horn A's conclusion. Each row lists
which premises hold and which fail, on one carrier.

1. Positive witness: the good-tracking source, every favouring measured by value.
   The same row in natural mode: its favouring is a natural appetite of the
   content state, it apprehends nothing (`appNone`), and the cognition criterion
   fails; every premise and the conclusion still hold.
2. A composite root (the D-directed favouring): only the no-limiting-principle
   premise fails.
3. The D-directed favouring counted impure at an unlimited root: only RootPurity
   fails.
4. The empty (chance) favouring counted pure, measured by value: only the
   per-bearer bridge fails.
5. The D-directed nature measured by its own end (its formal object is
   D-realization, as a natural appetite's object is the end of its nature): the
   per-bearer bridge, RootPurity and variation hold, and only the object premise
   fails. This is the D-rival's row.
6. The value order coincides with D-realization: only variation fails. -/
def FormalObjectControls : Prop :=
  (roots False ∧ purity personalSrc purePos False ∧ ownObj purePos (objAll better) ∧
    object personalSrc (objAll better) better ∧ varies better ∧ generalFor better personalSrc ∧
    NaturalAppetite contentState better ∧ ¬ RationalAppetite noApprehension better ∧
    ¬ criterion personalSrc appNone) ∧
  (¬ roots True ∧ purity dNatureSrc purePos True ∧ ownObj purePos (objAll better) ∧
    object dNatureSrc (objAll better) better ∧ varies better ∧ ¬ generalFor better dNatureSrc) ∧
  (roots False ∧ ¬ purity dNatureSrc purePos False ∧ ownObj purePos (objAll better) ∧
    object dNatureSrc (objAll better) better ∧ varies better ∧ ¬ generalFor better dNatureSrc) ∧
  (roots False ∧ purity chanceSrc pureChance False ∧ ¬ ownObj pureChance (objAll better) ∧
    object chanceSrc (objAll better) better ∧ varies better ∧ ¬ generalFor better chanceSrc) ∧
  (roots False ∧ purity dNatureSrc pureNoGG False ∧ ownObj pureNoGG (objAll fitOrder) ∧
    ¬ object dNatureSrc (objAll fitOrder) better ∧ varies better ∧
    ¬ generalFor better dNatureSrc) ∧
  (roots False ∧ purity dNatureSrc pureNoGG False ∧ ownObj pureNoGG (objAll fitOrder) ∧
    object dNatureSrc (objAll fitOrder) fitOrder ∧ ¬ varies fitOrder ∧
    ¬ generalFor fitOrder dNatureSrc)

end Control

end TruthCore.Causality.AppetiteStandard
