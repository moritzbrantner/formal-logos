module

public import TruthCore.Causality.RootPerfectionIntellect
public import TruthCore.Causality.GoodFavouring
public import TruthCore.Causality.RootPositiveIntellectWill

/-! # Joint coherence of a simple, noncognitive, finality-originating foundation (#2145, Investigation 4)

Analyst formulations, attribution deferred (logic first). See
`docs/notes/causal-perfection-transfer.md`, section "Joint coherence of a simple,
necessary, noncognitive, finality-originating foundation".

The cross-family argument joins three earlier slices on shared vocabulary:

* the #2153 admissible family, its limitation bridge `PositiveProfileExclusionLimits`
  (the structural L, derived there from the RootPurity bridge and joint
  compossibility) and the absence trichotomy;
* the Lane 2b favouring profiles of `GoodFavouring` (a source's favouring in each
  variation scenario) and its controlled-dependence reading BECAUSE_OF_GOODNESS_2
  (`BecauseOfGoodness`);
* the #2125 / Lane 1b intellect vocabulary (`GodHasIntellect`, finite reach).

The results take the shared `CausalityFrame` (#1784): the "distinct simply prior
being" of the #2153 limiting principle is the frame's `PriorSimply` (PRIOR_1).
The grounding profile, compositeness and the represented essence and esse are
not frame fields and stay explicit parameters, as in #2153.

**Favouring determinations.** `favours φ` is the real determination "the bearer's
own favouring is the profile φ" (one token per profile). `goodGen` is the real
determination "the bearer favours the better as such". Neither token is fixed in
Lean; their content enters only through the open bridge
`OneFavouringRealization`: every admissible profile (a set of determinations a
simple, unreceived, necessary source could jointly have) is realized by ONE
favouring profile ψ, every favouring token in it names ψ, and if it contains
`goodGen` then ψ is good-general. The "one" is where simplicity enters: a
composite source could have a fixed natural inclination and a good-general
appetite as two distinct powers, and the `anyFamily` control (two favourings
jointly admissible) is exactly that case.

**Good-general favouring** (`GoodGeneral`, profile level): for some scenario and
pair of candidates, the favouring depends on betterness with the end-realization
feature held fixed (BECAUSE_OF_GOODNESS_2) and at least one of the two candidates
is not a present input of the favouring at that scenario. The second clause
separates a comparator that responds only to inputs actually present to it (a
balance); the first separates a disposition whose favouring factors through its
fixed end content (law 1 of `GoodDependenceLaws`).

**Cognition criterion** (`GoodGeneralFavouringIsApprehension`): a bearer whose
favouring determination is good-general apprehends some content about a
candidate. It is an OPEN analyst bridge. Its two clauses are characterized
without reference to persons; it applies in the same way to rational exercise
and to an impersonal good-general nature, which `GoodFavouring` represents by the
same function.

Every model in `Control` is a finite structural surrogate. It witnesses only the
stated formal interpretation, never a metaphysical possibility. -/

@[expose] public section

namespace TruthCore.Causality.ImpersonalFoundationJoint

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.GoodFavouring (BecauseOfGoodness)

variable {W B D S X Z C : Type}

/-- GOOD-GENERAL favouring profile: in some scenario `s`, for candidates `x`, `y`
of which at least one is not a present input at `s`, the profile's favouring of
`x` over `y` depends on the betterness standard `good` with the end-realization
feature `fitOf` held fixed (BECAUSE_OF_GOODNESS_2, `BecauseOfGoodness`). -/
def GoodGeneral (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (φ : GoodFavouring.Profile S X) : Prop :=
  ∃ s x y, BecauseOfGoodness good fitOf φ s x y ∧ (¬ Present s x ∨ ¬ Present s y)

/-- OPEN one-favouring realization (the simplicity bridge for favouring): every
admissible profile `q` is realized by one favouring profile `ψ`; every favouring
token in `q` names `ψ`, and if `q` contains the good-general token then `ψ` is
good-general. It is a reading of what the favouring tokens and admissibility
mean, not a theorem about them. -/
def OneFavouringRealization (Admissible : Set D → Prop)
    (favours : GoodFavouring.Profile S X → D) (goodGen : D) (good : S → X → X → Prop)
    (fitOf : S → Z) (Present : S → X → Prop) : Prop :=
  ∀ q, Admissible q → ∃ ψ : GoodFavouring.Profile S X,
    (∀ φ, favours φ ∈ q → φ = ψ) ∧ (goodGen ∈ q → GoodGeneral good fitOf Present ψ)

/-- OPEN, analyst formulation: favouring the better as such is a pure perfection
in the sense of the supplied `Pure` (DEF-PURE-PERFECTION), the same parameter as
in the #2153 premises. -/
def GoodGeneralityIsPure (Pure : D → Prop) (goodGen : D) : Prop := Pure goodGen

/-- Every favouring determination of an actual root at `w` is good-general. -/
def ActualRootFavouringIsGoodGeneral (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ φ, Has r (favours φ) → GoodGeneral good fitOf Present φ

/-- OPEN, the weakest form of commitment (e) used here: every actual root at `w`
has an own favouring determination. ORIGINAL_FINALITY_1 at a root (an own
favouring that prefers the better and depends on end-realization) includes it;
the finality conditions themselves are not used. -/
def ActualRootsHaveOwnFavouring (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) : Prop :=
  ∀ r, ActualRoot m w r → ∃ φ, Has r (favours φ)

/-- OPEN cognition criterion: any bearer whose favouring determination is
good-general apprehends some content about some candidate. -/
def GoodGeneralFavouringIsApprehension (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ x φ, Has x (favours φ) → GoodGeneral good fitOf Present φ →
    ∃ c y, About c y ∧ Apprehends x c

/-- A bearer apprehends through good-general favouring: it has a good-general
favouring determination and apprehends some content about some candidate. The
conjunction does not say that the apprehension governs the favouring
(BECAUSE_OF_GOODNESS_3). -/
def ApprehendsThroughGoodGeneralFavouring (Has : B → D → Prop)
    (favours : GoodFavouring.Profile S X → D) (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) (About : C → X → Prop) (Apprehends : B → C → Prop) (x : B) :
    Prop :=
  (∃ φ, Has x (favours φ) ∧ GoodGeneral good fitOf Present φ) ∧
    ∃ c y, About c y ∧ Apprehends x c

/-- Every actual root at `w` apprehends through good-general favouring. -/
def ActualRootsApprehendThroughGoodGeneralFavouring (m : Profile W B) (w : W)
    (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ r, ActualRoot m w r →
    ApprehendsThroughGoodGeneralFavouring Has favours good fitOf Present About Apprehends r

/-- OPEN recognition bridge: every GOD_4 bearer that apprehends through
good-general favouring satisfies the unary `HasIntellect` of HAS_INTELLECT_1. It
carries the intellectual, as against sensory, grade: favouring by the betterness
of candidates that are not present inputs, with their end content held fixed, is
read as grasping goodness as such. It is sufficiency only. -/
def GodGoodGeneralApprehensionIsIntellect (IsGod HasIntellect : B → Prop)
    (Has : B → D → Prop) (favours : GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop) : Prop :=
  ∀ g, IsGod g →
    ApprehendsThroughGoodGeneralFavouring Has favours good fitOf Present About Apprehends g →
      HasIntellect g

/-! ## Finite controls

The carrier is the #2153 one: the two-being, two-world `rootProfile` of the
#1873 controls (source `true`, the only actual root at world `true`; effect
`false`, grounded by it and existing only at world `true`), with the structural
`composite`, `prior` and `rep` of `RootPerfectionExclusion.Control`. The
favouring profiles, scenarios, outcomes, `fits` and `better` are those of
`GoodFavouring.Model` (Lane 2b). Determinations: `esse`, the good-general token,
and one favouring token per profile. These are assignments of the stated
relations only. -/
namespace Control

open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better)

/-- Control determinations. -/
inductive Det
  | esse
  | goodGen
  | fav (φ : GoodFavouring.Profile Scenario Outcome)

/-- The favouring tokens. -/
def favTok : GoodFavouring.Profile Scenario Outcome → Det := Det.fav

/-- No candidate is a present input of the favouring (a source prior to
production). -/
def noInputs (_ : Scenario) (_ : Outcome) : Prop := False

/-- Every candidate is a present input (a balance comparing what is on its pans). -/
def allPresent (_ : Scenario) (_ : Outcome) : Prop := True

/-- Good-general favouring on the control carrier. -/
def gg (φ : GoodFavouring.Profile Scenario Outcome) : Prop := GoodGeneral better fits noInputs φ

/-- The simple family: at most one favouring token, and the good-general token
only with a good-general favouring. -/
def simpleFamily (q : Set Det) : Prop :=
  (∀ φ ψ, Det.fav φ ∈ q → Det.fav ψ ∈ q → φ = ψ) ∧
    (Det.goodGen ∈ q → ∀ φ, Det.fav φ ∈ q → gg φ)

/-- The simple family without the good-general token (case (i) for it). -/
def noGoodGenFamily (q : Set Det) : Prop := simpleFamily q ∧ Det.goodGen ∉ q

/-- Every profile is admissible: two favourings may be had together. -/
def anyFamily (_ : Set Det) : Prop := True

/-- Purity: `esse`, good-generality and the good-tracking favouring. -/
def purePos (d : Det) : Prop :=
  d = Det.esse ∨ d = Det.goodGen ∨ d = Det.fav better
/-- Purity as the D-nature rival assigns it: `esse`, good-generality and both
the good-tracking and the D-directed favouring. -/
def pureRival (d : Det) : Prop :=
  d = Det.esse ∨ d = Det.goodGen ∨ d = Det.fav better ∨
    d = Det.fav GoodFavouring.Model.dNature
/-- Purity with good-generality impure: `esse` and the D-directed favouring. -/
def pureNoGG (d : Det) : Prop := d = Det.esse ∨ d = Det.fav GoodFavouring.Model.dNature
/-- Purity: `esse` and good-generality only. -/
def pureEsseGG (d : Det) : Prop := d = Det.esse ∨ d = Det.goodGen

/-- The source `true` has `src`; the effect has only `esse`. -/
def hasSrc (src : Set Det) : Bool → Det → Prop
  | true, d => d ∈ src
  | false, d => d = Det.esse

/-- The good-tracking source profile. -/
def personalSrc : Set Det := {Det.esse, Det.goodGen, Det.fav better}
/-- The D-directed source profile (generative finality determined to D). -/
def dNatureSrc : Set Det := {Det.esse, Det.fav GoodFavouring.Model.dNature}
/-- A D-directed favouring together with the good-general token. -/
def mixedSrc : Set Det := {Det.esse, Det.goodGen, Det.fav GoodFavouring.Model.dNature}
/-- A good-general token with no favouring token. -/
def bareGGSrc : Set Det := {Det.esse, Det.goodGen}

/-- Contents are named by candidates. -/
def aboutC (k y : Outcome) : Prop := k = y
/-- The source apprehends every content. -/
def appSource (x : Bool) (_ : Outcome) : Prop := x = true
/-- Nothing apprehends anything. -/
def appNone (_ : Bool) (_ : Outcome) : Prop := False

/-- GOD_4 names `n`; `HasIntellect` holds of `true` exactly when `p`. -/
def isGod (n x : Bool) : Prop := x = n
def intellectIf (p : Prop) (x : Bool) : Prop := x = true ∧ p

/-- The #1873 causality frame with the #2153 structural priority as its
`PriorSimply` field: the source is simply prior to the effect. -/
def jointFrame : TruthCore.Causality.Frame.CausalityFrame Bool Bool Unit Unit :=
  { TruthCore.Causality.IntentionalExemplarExtension.Control.frame with
    PriorSimply := TruthCore.Causality.RootPerfectionExclusion.Control.prior }

open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootPerfectionExclusion.Control (composite rep)
open TruthCore.Causality.GoodFavouring.Model (dNature determinedWill goodGeneral rational proxy chance)
open TruthCore.Causality.GoodFavouring (OriginalFinality OriginalFinalityForGood)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.RootPerfectionExclusion
  (RootProfilesAdmissible PureDeterminationsAdmissible PureExtensionsAdmissible
    PositiveProfileExclusionLimits)

/-- No actual root at `true` has a represented limiting principle (`a30c5963`). -/
def roots (c : Prop) : Prop :=
  ActualRootsWithoutLimitingPrinciple rootProfile true (composite c) jointFrame.PriorSimply rep rep
/-- The structural L bridge (`4ff76ab8`). -/
def limits (adm : Set Det → Prop) (src : Set Det) (pure : Det → Prop) (c : Prop) : Prop :=
  PositiveProfileExclusionLimits adm (hasSrc src) pure (composite c) jointFrame.PriorSimply rep rep
/-- The RootPurity bridge (`c78c77da`), one input of the derived L. -/
def purity (src : Set Det) (pure : Det → Prop) (c : Prop) : Prop :=
  UnlimitedDeterminationsArePure (composite c) jointFrame.PriorSimply rep rep (hasSrc src) pure
/-- Joint compossibility (`500d0e2d`), the other input of the derived L. -/
def extend (adm : Set Det → Prop) (pure : Det → Prop) : Prop := PureExtensionsAdmissible adm pure
/-- Root-profile admissibility (`0a9d3a40`). -/
def rootAdm (adm : Set Det → Prop) (src : Set Det) : Prop :=
  RootProfilesAdmissible rootProfile true adm (hasSrc src)
/-- Pure admissibility (`ee287fd3`). -/
def pureAdm (adm : Set Det → Prop) (pure : Det → Prop) : Prop :=
  PureDeterminationsAdmissible adm pure
/-- Purity of good-generality. -/
def ggPure (pure : Det → Prop) : Prop := GoodGeneralityIsPure pure Det.goodGen
/-- One-favouring realization. -/
def realizes (adm : Set Det → Prop) : Prop :=
  OneFavouringRealization adm favTok Det.goodGen better fits noInputs
/-- Horn A's conclusion. -/
def general (src : Set Det) : Prop :=
  ActualRootFavouringIsGoodGeneral rootProfile true (hasSrc src) favTok better fits noInputs
/-- Commitment (e), weakest form. -/
def favouring (src : Set Det) : Prop := ActualRootsHaveOwnFavouring rootProfile true (hasSrc src) favTok
/-- The cognition criterion. -/
def criterion (src : Set Det) (app : Bool → Outcome → Prop) : Prop :=
  GoodGeneralFavouringIsApprehension (hasSrc src) favTok better fits noInputs aboutC app
/-- Horn B's conclusion. -/
def apprehends (src : Set Det) (app : Bool → Outcome → Prop) : Prop :=
  ActualRootsApprehendThroughGoodGeneralFavouring rootProfile true (hasSrc src) favTok better fits
    noInputs aboutC app
/-- Finite grounding reach (`75974d26`) with GOD_4 naming `n`. -/
def reach (n : Bool) : Prop :=
  TruthCore.Causality.ActualAncestralSource.GodReachesActualConcreta rootProfile true (isGod n)
/-- The recognition bridge. -/
def recognition (n : Bool) (i : Prop) (src : Set Det) (app : Bool → Outcome → Prop) : Prop :=
  GodGoodGeneralApprehensionIsIntellect (isGod n) (intellectIf i) (hasSrc src) favTok better fits
    noInputs aboutC app
/-- GOD_4 HAS_INTELLECT_1 on the carrier. -/
def godIntellect (n : Bool) (i : Prop) : Prop :=
  TruthCore.Case.Catholicism.GodHasIntellect (isGod n) (intellectIf i)

/-- Horn A controls. Each row lists which premises hold and which fail, on the
same carrier; every failing row has the D-directed favouring at the root, so the
conclusion fails there.
1. positive witness: the good-tracking source; every premise, the two inputs of
   the derived L, and the conclusion;
2. a composite root: only the no-limiting-principle premise fails;
3a. the D-directed favouring counted impure: only L fails, and of its inputs the
   RootPurity bridge fails while joint compossibility holds;
3b. the D-directed favouring counted pure (the rival's purity): only L fails,
   and of its inputs joint compossibility fails while RootPurity holds;
4. the D-directed favouring together with the good-general token: only
   root-profile admissibility fails;
5. the good-general token in no admissible profile (case (i)): only pure
   admissibility fails;
6. good-generality impure: only its purity fails;
7. every profile admissible, so two favourings can be had together: only
   one-favouring realization fails. -/
def FavouringControls : Prop :=
  (roots False ∧ limits simpleFamily personalSrc purePos False ∧ rootAdm simpleFamily personalSrc ∧
    pureAdm simpleFamily purePos ∧ ggPure purePos ∧ realizes simpleFamily ∧
    general personalSrc ∧ purity personalSrc purePos False ∧ extend simpleFamily purePos) ∧
  (¬ roots True ∧ limits simpleFamily dNatureSrc purePos True ∧ rootAdm simpleFamily dNatureSrc ∧
    pureAdm simpleFamily purePos ∧ ggPure purePos ∧ realizes simpleFamily ∧
    ¬ general dNatureSrc) ∧
  (roots False ∧ ¬ limits simpleFamily dNatureSrc purePos False ∧
    rootAdm simpleFamily dNatureSrc ∧ pureAdm simpleFamily purePos ∧ ggPure purePos ∧
    realizes simpleFamily ∧ ¬ general dNatureSrc ∧ ¬ purity dNatureSrc purePos False ∧
    extend simpleFamily purePos) ∧
  (roots False ∧ ¬ limits simpleFamily dNatureSrc pureRival False ∧
    rootAdm simpleFamily dNatureSrc ∧ pureAdm simpleFamily pureRival ∧ ggPure pureRival ∧
    realizes simpleFamily ∧ ¬ general dNatureSrc ∧ purity dNatureSrc pureRival False ∧
    ¬ extend simpleFamily pureRival) ∧
  (roots False ∧ limits simpleFamily mixedSrc purePos False ∧ ¬ rootAdm simpleFamily mixedSrc ∧
    pureAdm simpleFamily purePos ∧ ggPure purePos ∧ realizes simpleFamily ∧
    ¬ general mixedSrc) ∧
  (roots False ∧ limits noGoodGenFamily dNatureSrc pureEsseGG False ∧
    rootAdm noGoodGenFamily dNatureSrc ∧ ¬ pureAdm noGoodGenFamily pureEsseGG ∧
    ggPure pureEsseGG ∧ realizes noGoodGenFamily ∧ ¬ general dNatureSrc) ∧
  (roots False ∧ limits simpleFamily dNatureSrc pureNoGG False ∧
    rootAdm simpleFamily dNatureSrc ∧ pureAdm simpleFamily pureNoGG ∧ ¬ ggPure pureNoGG ∧
    realizes simpleFamily ∧ ¬ general dNatureSrc) ∧
  (roots False ∧ limits anyFamily dNatureSrc purePos False ∧ rootAdm anyFamily dNatureSrc ∧
    pureAdm anyFamily purePos ∧ ggPure purePos ∧ ¬ realizes anyFamily ∧ ¬ general dNatureSrc)

/-- Horn B controls: a positive witness and, for each of the three premises, a
row where it fails, the others hold and the conclusion fails. The last row is
the standing good-general rival: a root with good-general favouring that
apprehends nothing. -/
def ApprehensionControls : Prop :=
  (general personalSrc ∧ favouring personalSrc ∧ criterion personalSrc appSource ∧
    apprehends personalSrc appSource) ∧
  (¬ general dNatureSrc ∧ favouring dNatureSrc ∧ criterion dNatureSrc appSource ∧
    ¬ apprehends dNatureSrc appSource) ∧
  (general bareGGSrc ∧ ¬ favouring bareGGSrc ∧ criterion bareGGSrc appSource ∧
    ¬ apprehends bareGGSrc appSource) ∧
  (general personalSrc ∧ favouring personalSrc ∧ ¬ criterion personalSrc appNone ∧
    ¬ apprehends personalSrc appNone)

/-- How the criterion classifies the Lane 2b profiles and a balance.
1. The good-general nature and rational exercise (the same function) are
   good-general, witnessed at `cBetter` with `actual` as the scenario that holds
   end-realization fixed; the counterpossible `valueless` scenario is not used.
2. The D-nature, the determined will, the proxy and chance are not.
3. A balance that tracks betterness but only among present inputs is not.
4. If betterness is the D-realization ordering itself (no variation of goodness
   at fixed end content), not even the good-tracking profile is good-general. -/
def CriterionTable : Prop :=
  (gg goodGeneral ∧ gg rational ∧ goodGeneral = rational) ∧
  (¬ gg dNature ∧ ¬ gg determinedWill ∧ ¬ gg proxy ∧ ¬ gg chance) ∧
  ¬ GoodGeneral better fits allPresent better ∧
  ¬ GoodGeneral GoodFavouring.Model.fitOrder fits noInputs better

/-- Recognition-step controls: a positive witness and, for three of the four
premises, a row where it fails, the others hold and GOD_4 HAS_INTELLECT_1 fails
(the root-existence premise holds on every assignment of this carrier). -/
def IntellectStepControls : Prop :=
  (TruthCore.Causality.RootPositiveIntellectWill.ActualRootExistsAt rootProfile true ∧
    reach true ∧ apprehends personalSrc appSource ∧
    recognition true True personalSrc appSource ∧ godIntellect true True) ∧
  (reach true ∧ ¬ apprehends dNatureSrc appSource ∧
    recognition true False dNatureSrc appSource ∧ ¬ godIntellect true False) ∧
  (¬ reach false ∧ apprehends personalSrc appSource ∧
    recognition false True personalSrc appSource ∧ ¬ godIntellect false True) ∧
  (reach true ∧ apprehends personalSrc appSource ∧
    ¬ recognition true False personalSrc appSource ∧ ¬ godIntellect true False)

open TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control
  (FirstSourceFrame)
open TruthCore.Causality.SelectionScope (WithholdsEachAt WithholdsAllAt NecessarilyGivesSomeAt)
open TruthCore.Causality.SelectionScope.Model (replGivingG)

/-- Joint configurations on one carrier (structural surrogates).

Shared by every row: (a) and (b) as the #1892 `FirstSourceFrame` (necessary
actual root, nonvacuous pure act, constitutive simplicity, own being) and no
represented limiting principle; (d) the root grounds the effect, which does not
exist at world `false`. The omission scope of (d) is the §61 replacement frame
on ANOTHER carrier (each recipient withheld somewhere, never total refraining):
that the source of one carrier is the giver of the other is an open
cross-carrier identification.

1. The D-directed impersonal root: it has the D-directed favouring, which has
   ORIGINAL_FINALITY_1 and lacks ORIGINAL_FINALITY_2 for c over z; it apprehends
   nothing; commitment (e) holds and the cognition criterion holds vacuously; and
   horn A's conclusion fails, so by `actualRootFavouringIsGoodGeneral` at least
   one premise of horn A fails (rows 2–7 of `FavouringControls` exhibit each
   option).
2. The good-general impersonal root: good-tracking favouring with
   ORIGINAL_FINALITY_2, apprehending nothing; horn A's conclusion and (e) hold,
   and the criterion fails.
3. The personal root: the same favouring with apprehension; every premise of
   both horns and both conclusions hold. -/
def JointConfigurations : Prop :=
  (FirstSourceFrame ∧ roots False ∧ rootProfile.grounds true true false ∧
    ¬ rootProfile.ontic.ExistsAt false false ∧
    WithholdsEachAt replGivingG false .g ∧ ¬ WithholdsAllAt replGivingG false .g ∧
    NecessarilyGivesSomeAt replGivingG false .g) ∧
  (hasSrc dNatureSrc true (Det.fav dNature) ∧
    OriginalFinality better GoodFavouring.Model.fitOrder dNature .actual .c .z ∧
    ¬ OriginalFinalityForGood better GoodFavouring.Model.fitOrder fits dNature .actual .c .z ∧
    (∀ k, ¬ appNone true k) ∧ favouring dNatureSrc ∧ criterion dNatureSrc appNone ∧
    ¬ general dNatureSrc) ∧
  (hasSrc personalSrc true (Det.fav goodGeneral) ∧
    OriginalFinalityForGood better GoodFavouring.Model.fitOrder fits goodGeneral .actual .c .z ∧
    (∀ k, ¬ appNone true k) ∧ general personalSrc ∧ favouring personalSrc ∧
    ¬ criterion personalSrc appNone) ∧
  (hasSrc personalSrc true (Det.fav rational) ∧
    OriginalFinalityForGood better GoodFavouring.Model.fitOrder fits rational .actual .c .z ∧
    appSource true .c ∧ general personalSrc ∧ favouring personalSrc ∧
    criterion personalSrc appSource ∧ apprehends personalSrc appSource)

end Control

end TruthCore.Causality.ImpersonalFoundationJoint
