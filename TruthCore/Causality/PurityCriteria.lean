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
  Their content depends on which standard is supplied. The two senses of the
  standard are distinct Lean types: STANDARD_OF_FAVOURING_1 is
  `ValueStandardOrder` (the betterness ranking read as value), and
  STANDARD_OF_FAVOURING_2 is `EndRealizationOrder` (the end-realization
  ordering). The registered value-sense bridges `MissingValueVerdictIsImpure`
  and `UnbackedValueVerdictIsImpure` take a `ValueStandardOrder`, so an
  end-realization order cannot be passed to them without an explicit
  construction of a value order from its relation.
* **Variation.** `BetternessVariesWithinEndClass` (on a `ValueStandardOrder`;
  `StandardVariesWithinEndClass` is the same condition on any ranking) is
  good-generality of the standard itself: betterness ranks some pair at one scenario and not at another
  that agrees on end-realization. Betterness factoring through end-realization
  (the fourth member of the #2172 `variationCore`) implies its denial; the
  converse fails in general because of the present-input clause.
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
is not a pure perfection. It says nothing about a selection among them that is
not a verdict of the favouring profile; whether such a selection is a real
determination of the bearer is a separate question. -/
def UnbackedVerdictIsImpure (Pure : D → Prop) (favours : GoodFavouring.Profile S X → D)
    (std : GoodFavouring.Profile S X) : Prop :=
  ∀ φ, UnbackedVerdict std φ → ¬ Pure (favours φ)

/-- Variation of any ranking `std` within an end-realization class: for some
scenario `s` and pair `x`, `y`, at least one not a present input at `s`, `std`
ranks `x` over `y` at `s` and does not at some scenario agreeing with `s` on
end-realization. It is good-generality of the ranking itself. -/
def StandardVariesWithinEndClass (std : S → X → X → Prop) (fitOf : S → Z)
    (Present : S → X → Prop) : Prop :=
  GoodGeneral std fitOf Present std

/-! ## Senses of the standard of favouring (DISAMB STANDARD_OF_FAVOURING) -/

/-- STANDARD_OF_FAVOURING_1: the betterness ranking read as VALUE. Its field
`better s x y` says that `x` is a better good than `y` at `s`. The field is a
declared PRIMITIVE relation: Lean does not type value. Distinguishing condition:
it is not the end-realization ordering, and nothing here says it factors through
end-realization. A separate structure, so that a value order and an
end-realization order are distinct types: passing between them needs an
explicit construction from the other's relation. -/
structure ValueStandardOrder (S X : Type) where
  /-- `x` is a better good than `y` at the scenario. -/
  better : S → X → X → Prop

/-- STANDARD_OF_FAVOURING_2: an ordering of candidates by end-realization. Its
field `ranks s x y` says that `x` ranks over `y` at `s` by end-realization. A
distinct structure from `ValueStandardOrder`. -/
structure EndRealizationOrder (S X : Type) where
  /-- `x` ranks over `y` at the scenario by realization of the end D. -/
  ranks : S → X → X → Prop

/-- The end-realization ordering of an end-realization feature `fit`: `x` ranks
over `y` at `s` exactly when `x` realizes the end D at `s` and `y` does not (the
Lane 2b `fitOrder` pattern). -/
def EndRealizationStandard (fit : S → X → Bool) : EndRealizationOrder S X :=
  ⟨fun s x y => fit s x = true ∧ fit s y = false⟩

/-- OPEN loss bridge in the value sense (STANDARD_OF_FAVOURING_1): a favouring
determination whose profile misses a verdict of the value order is not pure. -/
def MissingValueVerdictIsImpure (Pure : D → Prop) (favours : GoodFavouring.Profile S X → D)
    (v : ValueStandardOrder S X) : Prop :=
  MissingVerdictIsImpure Pure favours v.better

/-- OPEN arbitrariness bridge in the value sense (STANDARD_OF_FAVOURING_1): a
favouring determination whose profile makes a verdict the value order does not
back is not pure. -/
def UnbackedValueVerdictIsImpure (Pure : D → Prop) (favours : GoodFavouring.Profile S X → D)
    (v : ValueStandardOrder S X) : Prop :=
  UnbackedVerdictIsImpure Pure favours v.better

/-- OPEN variation premise in the value sense: betterness varies within an
end-realization class (`StandardVariesWithinEndClass` of the value order). It
holds exactly when some profile is good-general relative to the value order
(`variationIffSomeGoodGeneral`). Betterness factoring through end-realization
(the fourth member of `variationCore`) implies its denial; the converse fails in
general because of the present-input clause. -/
def BetternessVariesWithinEndClass (v : ValueStandardOrder S X) (fitOf : S → Z)
    (Present : S → X → Prop) : Prop :=
  StandardVariesWithinEndClass v.better fitOf Present

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
/-- The value-sense loss bridge, with the value order whose relation is `std`. -/
def loss (pure : Det → Prop) (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  MissingValueVerdictIsImpure pure favTok ⟨std⟩
/-- The value-sense arbitrariness bridge, with the value order whose relation is `std`. -/
def backed (pure : Det → Prop) (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  UnbackedValueVerdictIsImpure pure favTok ⟨std⟩
/-- Variation of the value order whose relation is `std`. -/
def varies (std : GoodFavouring.Profile Scenario Outcome) : Prop :=
  BetternessVariesWithinEndClass ⟨std⟩ fits noInputs
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
6. the value order coincides with the end-realization ordering (betterness
   factors through end-realization, `variationCore`'s fourth member) and the
   D-directed favouring is pure: only the variation premise fails, and the
   D-directed favouring tracks the value order exactly. Every row uses the
   value sense; the D-relative form appears only in `StandardRelativity`. -/
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

/-- The carrier's value order (STANDARD_OF_FAVOURING_1). -/
def valueOrder : ValueStandardOrder Scenario Outcome := ⟨better⟩
/-- The carrier's end-realization order (STANDARD_OF_FAVOURING_2). -/
def dOrder : EndRealizationOrder Scenario Outcome := EndRealizationStandard fits

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
  MissesVerdict valueOrder.better dNature ∧ UnbackedVerdict dOrder.ranks better ∧
  ¬ MissesVerdict valueOrder.better better ∧ ¬ UnbackedVerdict valueOrder.better better ∧
  ¬ MissesVerdict dOrder.ranks dNature ∧ ¬ UnbackedVerdict dOrder.ranks dNature

/-- Two times and two candidates for the ORIGINAL_FINALITY control: `good` ranks
`true` over `false` at time `true` only; end-realization is constant; nothing
realizes the end. -/
def ofGood (s x y : Bool) : Prop := s = true ∧ x = true ∧ y = false
/-- No candidate realizes the end at any scenario. -/
def ofFit (_ _ _ : Bool) : Prop := False

/-- Exact value tracking with variation does not give ORIGINAL_FINALITY_2: the
profile equal to `good` tracks it exactly and the value order varies within the
(single) end-realization class, yet `OriginalFinalityForGood` fails at every
scenario and pair, because its ORIGINAL_FINALITY_1 component needs dependence on
end-realization (`BecauseOfContent`), which the constant `ofFit` never ranks.
The goodness-dependence component (`BecauseOfGoodness`) does hold. -/
def ExactTrackingWithoutOriginalFinality : Prop :=
  BetternessVariesWithinEndClass (⟨ofGood⟩ : ValueStandardOrder Bool Bool)
      (fun _ => ()) (fun _ _ => False) ∧
  (∃ s x y, TruthCore.Causality.GoodFavouring.BecauseOfGoodness ofGood (fun _ => ()) ofGood s x y) ∧
  ∀ s x y, ¬ TruthCore.Causality.GoodFavouring.OriginalFinalityForGood ofGood ofFit (fun _ => ())
    ofGood s x y

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
