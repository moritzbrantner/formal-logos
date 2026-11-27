module

public import TruthCore.Causality.ImpersonalFoundationJoint
public import TruthCore.Causality.RootPerfectionIntellect

/-! # When is a restriction of content a limitation? Criteria for the purity premises (#2145, premise lane P)

Analyst formulations, attribution deferred (logic first). See
`docs/notes/causal-perfection-transfer.md`, section "When is a restriction of
content a limitation? The purity premises under one criterion".

The purity family carries the pure-perfection route and horn A of #2145: the
purity of wisdom (`44e39691`), the purity of good-generality (`e2357adc`), joint
compossibility (`500d0e2d`, relocated into requirement form through `0c8631bd`)
and one favouring per source (`3e6ae3e7`). The positive warrant recorded for
`e2357adc` is the principle "restriction of content is limitation". This module
states candidate criteria for that principle precisely enough that they can be
applied to every side by the same function and can fail.

* **A. Standard-relative loss and arbitrariness.** A favouring profile is
  measured against a standard `std` (a ranking of candidates in each variation
  scenario). It *misses* a verdict of the standard when the standard ranks `x`
  over `y` at `s` and the profile does not favour `x` over `y` there
  (`MissesVerdict`); it makes an *unbacked* verdict when it favours `x` over `y`
  at `s` and the standard does not rank them so (`UnbackedVerdict`). The two
  OPEN bridges `MissingVerdictIsImpure` and `UnbackedVerdictIsImpure` read
  "restriction of content is limitation" as: a favouring determination that
  misses, or adds to, the verdicts of the standard is not a pure perfection.
  Their content depends on which standard is supplied; with `std` the value
  ranking (DEF 071b24f0) they are the value-relative form, and with `std` the
  end-realization ordering they are the D-relative form. Both forms use the same
  functions.
* **Variation.** `BetternessVariesWithinEndClass` is good-generality of the
  standard itself: betterness ranks some pair at one scenario and not at another
  that agrees on end-realization. It is the fourth member of the #2172
  `variationCore`.
* **Symmetric alternatives.** `ExclusiveTokens` (no admissible profile has two
  distinct tokens of one family) and `PurityParity` (two tokens of the family
  are pure together or not at all) state what an intrinsic, exclusive choice
  between alternatives on a par would be.
* **B. Reference class.** `EnumerativeConstitutivity` is the inference from
  "every known instance of a kind has a feature" to "the feature is constitutive
  of the kind".
* **C. Tensed knowing.** A temporal knower's state at each time
  (`KnowsAt`), the tensed truths at each time (`TrueAt`), tensed omniscience,
  veridicality and immutability of the state.

Every model in `Control` is a finite structural surrogate. It witnesses only the
stated formal interpretation, never a metaphysical possibility. -/

@[expose] public section

namespace TruthCore.Causality.PurityCriteria

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral)

variable {S X Z D A : Type}

/-! ## A. Standard-relative loss and arbitrariness -/

/-- The profile `φ` MISSES a verdict of the standard `std`: at some scenario the
standard ranks `x` over `y` and `φ` does not favour `x` over `y`. With `std` the
value ranking, the profile fails to favour something that is better. -/
def MissesVerdict (std φ : GoodFavouring.Profile S X) : Prop :=
  ∃ s x y, std s x y ∧ ¬ φ s x y

/-- The profile `φ` makes an UNBACKED verdict relative to `std`: at some scenario
it favours `x` over `y` although the standard does not rank `x` over `y`. With
`std` the value ranking, it prefers something that is not better (a tie-break or
a preference against value). -/
def UnbackedVerdict (std φ : GoodFavouring.Profile S X) : Prop :=
  ∃ s x y, φ s x y ∧ ¬ std s x y

/-- OPEN loss bridge, the first half of "restriction of content is
limitation": a favouring determination whose profile misses a verdict of the
standard `std` is not pure (DEF-PURE-PERFECTION, the same `Pure` parameter as the
#2153 premises). Its content depends on the standard supplied. -/
def MissingVerdictIsImpure (Pure : D → Prop) (favours : GoodFavouring.Profile S X → D)
    (std : GoodFavouring.Profile S X) : Prop :=
  ∀ φ, MissesVerdict std φ → ¬ Pure (favours φ)

/-- OPEN arbitrariness bridge, the second half: a favouring determination whose
profile makes a verdict that the standard does not back is not pure. With `std`
the value ranking it says that a standing preference among value-tied candidates
is not a pure perfection; it says nothing about a contingent selection among
them that is not part of the profile. -/
def UnbackedVerdictIsImpure (Pure : D → Prop) (favours : GoodFavouring.Profile S X → D)
    (std : GoodFavouring.Profile S X) : Prop :=
  ∀ φ, UnbackedVerdict std φ → ¬ Pure (favours φ)

/-- OPEN variation premise: betterness varies within an end-realization class.
For some scenario `s` and pair `x`, `y`, at least one of them not a present input
at `s`, `good` ranks `x` over `y` at `s` and does not at some scenario that
agrees with `s` on end-realization. It is good-generality of the standard
itself; its denial (betterness factors through end-realization) is the fourth
member of `variationCore`. -/
def BetternessVariesWithinEndClass (good : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) : Prop :=
  GoodGeneral good fitOf Present good

/-! ## Symmetric alternatives -/

/-- No admissible profile contains two distinct tokens of the family `tok`
(one choice, or one favouring, per admissible profile). The first conjunct of
`OneFavouringRealization` is this for the favouring tokens. -/
def ExclusiveTokens (Admissible : Set D → Prop) (tok : A → D) : Prop :=
  ∀ q, Admissible q → ∀ a b, tok a ∈ q → tok b ∈ q → a = b

/-- The alternatives `a` and `b` are on a par in purity: one token is pure exactly
when the other is. For two candidates that no feature distinguishes for the
standard (value-tied, the case where a selection is free), nothing makes one
selection a purer actuality than the other. -/
def PurityParity (Pure : D → Prop) (tok : A → D) (a b : A) : Prop :=
  Pure (tok a) ↔ Pure (tok b)

/-! ## B. Reference class for constitutive features -/

variable {K F Y : Type}

/-- The enumerative rule: if a kind has a known instance and every known
instance has a feature, the feature is constitutive of the kind. -/
def EnumerativeConstitutivity (KnownInstance : Y → K → Prop) (HasFeature : Y → F → Prop)
    (Constitutive : F → K → Prop) : Prop :=
  ∀ k f, (∃ y, KnownInstance y k) → (∀ y, KnownInstance y k → HasFeature y f) →
    Constitutive f k

/-- A kind with an impure constitutive feature is not a pure perfection. -/
def ImpureConstitutiveMakesImpure (Constitutive : F → K → Prop) (ImpureFeature : F → Prop)
    (PureKind : K → Prop) : Prop :=
  ∀ k f, Constitutive f k → ImpureFeature f → ¬ PureKind k

/-! ## C. Tensed knowing -/

variable {T C : Type}

/-- Tensed omniscience: at each time the knower knows every content true at that
time. -/
def TensedOmniscience (TrueAt KnowsAt : T → C → Prop) : Prop :=
  ∀ t c, TrueAt t c → KnowsAt t c

/-- The knower knows at each time only what is true at that time. -/
def Veridical (TrueAt KnowsAt : T → C → Prop) : Prop :=
  ∀ t c, KnowsAt t c → TrueAt t c

/-- The knowledge state does not change: what is known at one time is known at
every time. -/
def ImmutableState (KnowsAt : T → C → Prop) : Prop :=
  ∀ t t' c, KnowsAt t c ↔ KnowsAt t' c

/-- Some content is true at one time and not at another (an irreducibly tensed
content such as "it is now t"). -/
def HasTensedContent (TrueAt : T → C → Prop) : Prop :=
  ∃ c t t', TrueAt t c ∧ ¬ TrueAt t' c

/-! ## Finite controls

The carrier is the #2172 one (`ImpersonalFoundationJoint.Control`): the #2153
two-being, two-world `rootProfile` (source `true`, the only actual root at
`true`), the structural `composite`, `prior` and `rep`, the Lane 2b scenarios,
outcomes and profiles, and the determinations `esse`, `goodGen` and one
favouring token per profile. These are assignments of the stated relations only;
they say nothing about what favouring, purity or value are. -/
namespace Control

open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder dNature chance)
open TruthCore.Causality.ImpersonalFoundationJoint (ActualRootFavouringIsGoodGeneral)
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok noInputs hasSrc personalSrc dNatureSrc purePos pureNoGG roots jointFrame)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootPerfectionExclusion.Control (composite rep)
open TruthCore.Causality.RootPurity (UnlimitedDeterminationsArePure)

/-- A profile favouring every candidate over every candidate in every scenario
(a degenerate, fixed profile used only as the arbitrariness control). -/
def everything : GoodFavouring.Profile Scenario Outcome := fun _ _ _ => True

/-- Source with the empty (chance) favouring. -/
def chanceSrc : Set Det := {Det.esse, Det.fav chance}
/-- Source with the degenerate `everything` favouring. -/
def everythingSrc : Set Det := {Det.esse, Det.fav everything}
/-- Purity: `esse` and the chance favouring. -/
def pureChance (d : Det) : Prop := d = Det.esse ∨ d = Det.fav chance
/-- Purity: `esse` and the `everything` favouring. -/
def pureEverything (d : Det) : Prop := d = Det.esse ∨ d = Det.fav everything

/-- The RootPurity bridge (`c78c77da`) on the carrier. -/
def purity (src : Set Det) (pure : Det → Prop) (c : Prop) : Prop :=
  UnlimitedDeterminationsArePure (composite c) jointFrame.PriorSimply rep rep (hasSrc src) pure
/-- The loss bridge relative to `std`. -/
def loss (pure : Det → Prop) (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  MissingVerdictIsImpure pure favTok std
/-- The arbitrariness bridge relative to `std`. -/
def backed (pure : Det → Prop) (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  UnbackedVerdictIsImpure pure favTok std
/-- Variation of the standard within an end-realization class. -/
def varies (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  BetternessVariesWithinEndClass std fits noInputs
/-- The conclusion `7fca65ec`, good-generality relative to `std`. -/
def generalFor (std : GoodFavouring.Profile Scenario Outcome) (src : Set Det) : Prop :=
  ActualRootFavouringIsGoodGeneral rootProfile true (hasSrc src) favTok std fits noInputs

/-- Controls for the standard route to horn A's conclusion. Each row lists which
premises hold and which fail, on one carrier; in every failing row the
conclusion fails.
1. positive witness: the good-tracking source, value standard;
2. a composite root (the D-directed favouring): only the no-limiting-principle
   premise fails;
3. the D-directed favouring counted impure at an unlimited root: only RootPurity
   fails;
4. the empty (chance) favouring counted pure: only the loss bridge fails;
5. the degenerate `everything` favouring counted pure: only the arbitrariness
   bridge fails;
6. the standard is the end-realization ordering itself (betterness factors
   through end-realization) and the D-directed favouring is pure: only the
   variation premise fails. This is the D-relative form of the bridges: under
   it the D-directed favouring tracks its standard exactly. -/
def StandardControls : Prop :=
  (roots False ∧ purity personalSrc purePos False ∧ loss purePos better ∧
    backed purePos better ∧ varies better ∧ generalFor better personalSrc) ∧
  (¬ roots True ∧ purity dNatureSrc purePos True ∧ loss purePos better ∧
    backed purePos better ∧ varies better ∧ ¬ generalFor better dNatureSrc) ∧
  (roots False ∧ ¬ purity dNatureSrc purePos False ∧ loss purePos better ∧
    backed purePos better ∧ varies better ∧ ¬ generalFor better dNatureSrc) ∧
  (roots False ∧ purity chanceSrc pureChance False ∧ ¬ loss pureChance better ∧
    backed pureChance better ∧ varies better ∧ ¬ generalFor better chanceSrc) ∧
  (roots False ∧ purity everythingSrc pureEverything False ∧ loss pureEverything better ∧
    ¬ backed pureEverything better ∧ varies better ∧ ¬ generalFor better everythingSrc) ∧
  (roots False ∧ purity dNatureSrc pureNoGG False ∧ loss pureNoGG fitOrder ∧
    backed pureNoGG fitOrder ∧ ¬ varies fitOrder ∧ ¬ generalFor fitOrder dNatureSrc)

/-- Standard relativity on the Lane 2b model. In genuine scenarios (all but the
counterpossible `valueless`) the D-directed profile and the good-tracking profile
agree on every verdict except one: `c` over `d` at `cBetter`. The value standard
ranks it and the D-realization ordering does not. So with the value standard
the D-directed profile misses a verdict, and with the D standard the
good-tracking profile makes an unbacked verdict, at the same pair and scenario.
Each profile tracks its own standard exactly. -/
def StandardRelativity : Prop :=
  (∀ s x y, s ≠ .valueless → ¬ (s = .cBetter ∧ x = .c ∧ y = .d) →
    (dNature s x y ↔ better s x y)) ∧
  (better .cBetter .c .d ∧ ¬ dNature .cBetter .c .d) ∧
  MissesVerdict better dNature ∧ UnbackedVerdict fitOrder better ∧
  ¬ MissesVerdict better better ∧ ¬ UnbackedVerdict better better ∧
  ¬ MissesVerdict fitOrder dNature ∧ ¬ UnbackedVerdict fitOrder dNature

/-- A standing physical tie-break: prefer the physical provision type wherever
value does not rank the other candidate higher. -/
def physTieBreak : GoodFavouring.Profile Scenario Outcome :=
  fun s x y => TruthCore.Causality.GoodFavouring.Model.physOrder s x y ∧ ¬ better s y x

/-- A value-free refinement test. Adding the physical tie-break to the
good-tracking profile adds verdicts and never conflicts with it, so the
criterion "a profile strictly refined by a non-conflicting profile is
restricted" would count the good-tracking profile itself as restricted. The
value-relative arbitrariness bridge instead counts the refinement as making an
unbacked verdict. -/
def RefinementCondemnsGoodTracking : Prop :=
  better ≤ better ⊔ physTieBreak ∧ better ≠ better ⊔ physTieBreak ∧
  (∀ s x y, ¬ (better s x y ∧ (better ⊔ physTieBreak) s y x)) ∧
  UnbackedVerdict better (better ⊔ physTieBreak)

/-- Two times, and contents: `now t` (it is now `t`) and `dated t t'` (at time
`t` it is `t'`). -/
inductive TContent
  | now (t : Bool)
  | dated (t t' : Bool)

/-- `now t` is true exactly at `t`; `dated t t'` is true at every time when `t = t'`. -/
def trueAt : Bool → TContent → Prop
  | t, .now t' => t = t'
  | _, .dated a b => a = b

/-- The tenseless knower: at every time it knows exactly the contents true at
every time. -/
def tenseless (_ : Bool) (c : TContent) : Prop := ∀ t, trueAt t c

/-- The tenseless reading on two times: the tenseless knower's state is immutable
and veridical, and for each tensed truth `now t` at `t` it knows the dated
content `dated t t`, but it does not know `now t` at any time; tensed
omniscience fails for it. Tensed content exists, so no knower is at once
tensed-omniscient, veridical and immutable (`tensedOmniscienceExcludesImmutability`). -/
def TenselessReading : Prop :=
  ImmutableState tenseless ∧ Veridical trueAt tenseless ∧
  (∀ t, trueAt t (.now t) ∧ tenseless t (.dated t t)) ∧
  (∀ t t', ¬ tenseless t (.now t')) ∧ ¬ TensedOmniscience trueAt tenseless ∧
  HasTensedContent trueAt

end Control

end TruthCore.Causality.PurityCriteria
