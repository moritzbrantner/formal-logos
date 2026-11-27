module

public import TruthCore.Causality.RootPerfectionExclusion
public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Causality.NecessaryFirstBeing
public import TruthCore.Causality.ActualAncestralSource
public import TruthCore.Causality.PureActRoot
public import TruthCore.Logic.StrengthComparison

/-! # From every pure perfection to intellect, and a constitutive reading of admissibility (#2145)

Analyst formulations, attribution deferred. Two questions of #2145
Investigation 1, second slice.

**A. Purity of intellect.** `ActualRootHasEveryPureDetermination` (`fe67d766`)
says nothing about which determinations are pure. `WisdomIsPure` states that
the one determination `wisdom` used by the `WisdomSelfUnderstanding` bridges is
pure, in the SAME sense: the same parameter `Pure : D → Prop`
(DEF-PURE-PERFECTION: an actuality involving no potency, limitation or
reception). What makes `wisdom` intellectual is not its name. It is fixed only
by the open bridge `WisdomSelfCapacity`: a subsistent bearer of `wisdom` has a
capacity for true content about itself. The purity premise and that bridge
are separate premises about the same token. `PureActRootsKnowThemselves`
is the root-level conclusion of the composed route.
`GodIntrinsicSelfKnowledgeIsIntellect` is the recognition step to the unary
`HasIntellect` of GOD_4 HAS_INTELLECT_1.

**B. Constitutive admissibility.** The #2153 family `Admissible` is a primitive.
`MemberGroundedAdmissibility` gives it a constitutive reading through a
primitive `RequiresLack`: a profile is admissible exactly when none of its
members requires the joint lack of some of its members. The derived
consequences are in the results module. The relation is hand-rolled because
Mathlib's `Set.Pairwise` is binary and skips the diagonal, while this reading
is n-ary (`RequiresLack d S` for a set `S`) and lets a determination exclude
itself. -/

@[expose] public section

namespace TruthCore.Causality.RootPerfectionIntellect

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding (IntrinsicSelfKnowledge)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

variable {W B D C R : Type}

/-! ## A. Purity of intellect -/

/-- OPEN, analyst formulation: the determination `wisdom` (subject-grounded
apprehension, read as the bearer's own apprehension and not as productive or
exemplary wisdom; made intellectual only by the separate `WisdomSelfCapacity`
bridge) is a pure perfection in the sense of the supplied `Pure` parameter
(DEF-PURE-PERFECTION). It is the same parameter as in
`ActualRootHasEveryPureDetermination`, so no sense passage is involved. -/
def WisdomIsPure {D : Type} (Pure : D → Prop) (wisdom : D) : Prop := Pure wisdom

/-- Every actual concrete root at `w` that is PURE_ACT_1 (in potency in no
respect of the independently supplied `InPotency`, DEF-INDEPENDENT-POTENCY) has
intrinsic self-knowledge: a true, actually apprehended and cognitively grounded
content about itself. PURE_ACT_1 is DEF-PURE-ACT (`a49e4cf1`). -/
def PureActRootsKnowThemselves (m : Profile W B) (w : W) (About Correct : C → B → Prop)
    (Apprehends CognitivelyGrounded : B → C → Prop) (InPotency : B → R → Prop) : Prop :=
  ∀ r, ActualRoot m w r → PureAct InPotency r →
    IntrinsicSelfKnowledge About Correct Apprehends CognitivelyGrounded r

/-- OPEN recognition bridge: any GOD_4 bearer with intrinsic self-knowledge
satisfies the unary `HasIntellect` of HAS_INTELLECT_1. It is the same premise
shape as the one `godHasIntellectFromWholePowerWisdom` takes inline. It reads
actual, true, cognitively grounded self-apprehension as sufficient for
intellect; it does not say that intellect requires it. It also carries the
intellectual (as against sensory) grade of HAS_INTELLECT_1: nothing in
`IntrinsicSelfKnowledge` distinguishes the grades. -/
def GodIntrinsicSelfKnowledgeIsIntellect (IsGod HasIntellect : B → Prop)
    (About Correct : C → B → Prop) (Apprehends CognitivelyGrounded : B → C → Prop) : Prop :=
  ∀ g, IsGod g → IntrinsicSelfKnowledge About Correct Apprehends CognitivelyGrounded g →
    HasIntellect g

/-! ## B. A constitutive reading of admissibility -/

/-- A profile in which no member requires the joint lack of some of its
members (DEF: exclusion-free profile).

`RequiresLack d S` is a declared PRIMITIVE. Intended meaning: it belongs to what
`d` is that a bearer of `d` does not have every member of `S`. Examples: having
exactly two units of extent requires the lack of having exactly three
(`S` a singleton); a fixed capacity for two demands requires the lack of
meeting three given demands together (`S` with three members, no pair
excluded). Non-example: knowing a truth requires the lack of nothing.
Distinguishing conditions: it is not actual non-co-occurrence, not the
incompatibility of two descriptions, and not causal prevention. It is directed
(from `d` to `S`) and need not be symmetric. The intended reading is upward
closed in `S` (requiring the lack of `S` together implies requiring the lack
of any superset together); that is not encoded, and nothing makes it
irreflexive. It is a requirement of LACK; a requirement of presence (`d` needs
`e` alongside it) is a different relation and is not expressible by it. -/
def ExclusionFree (RequiresLack : D → Set D → Prop) (q : Set D) : Prop :=
  ∀ d ∈ q, ∀ S ⊆ q, ¬ RequiresLack d S

/-- OPEN constitutive reading of the #2153 admissible family: a profile is
admissible exactly when it is exclusion-free. Every inadmissibility is then
attributed to a member's requirement of a lack. It is neutral about purity.
Because exclusion-freedom is inherited by subsets, it makes the family
downward closed and puts the empty profile in it. It therefore excludes two
kinds of constraint: irreducibly holistic prohibitions that no member's
requirement accounts for, and requirements of PRESENCE (a member that needs
another member alongside it, as in the articulation objection's
`noesis`-needs-an-impure-articulation form, or a family that requires `esse`
in every profile). `ExclusionFreeAdmissible` is its weaker sufficiency
direction, the one the derivations use. -/
def MemberGroundedAdmissibility (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) : Prop :=
  ∀ q, Admissible q ↔ ExclusionFree RequiresLack q

/-- OPEN, the weaker sibling of `MemberGroundedAdmissibility`: every
exclusion-free profile is admissible. It says nothing about inadmissible
profiles being excluded by a member, so it allows requirements of presence
and other extra admissibility constraints. Together with
`PureRequiresNoPureLack` it is equivalent (for a free requirement relation) to
"every profile of pure determinations is admissible"
(`sufficiencyPremisesIffAllPure`). -/
def ExclusionFreeAdmissible (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) : Prop :=
  ∀ q, ExclusionFree RequiresLack q → Admissible q

/-- Difference of member grounding over its sufficiency direction (#1598),
OPEN, not asserted: every admissible profile is exclusion-free (the necessity
direction). It is what member grounding adds: the part that makes every
member's requirement of a lack binding: a profile containing one is
inadmissible. -/
def AdmissibleIsExclusionFree (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) : Prop :=
  ∀ q, Admissible q → ExclusionFree RequiresLack q

/-- The strength comparison of member grounding over its sufficiency direction,
with the necessity direction as its difference. -/
def mgOverSufficiency (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop) :
    TruthCore.Logic.StrengthComparison.ComparisonSpec where
  stronger := MemberGroundedAdmissibility Admissible RequiresLack
  weaker := ExclusionFreeAdmissible Admissible RequiresLack
  delta := AdmissibleIsExclusionFree Admissible RequiresLack

/-- Premise-free equivalence: member grounding holds exactly when its
sufficiency direction and its necessity direction hold. -/
def MGOverSufficiencyExact : Prop :=
  ∀ {D : Type} (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop),
    MemberGroundedAdmissibility Admissible RequiresLack ↔
      ExclusionFreeAdmissible Admissible RequiresLack ∧
        AdmissibleIsExclusionFree Admissible RequiresLack

/-- OPEN: no pure determination requires the joint lack of pure
determinations. The rationale is DEF-PURE-PERFECTION: requiring the lack of a
positive actuality is a limitation of the requirer. It covers single excluded
determinations and joint lacks alike. -/
def PureRequiresNoPureLack (RequiresLack : D → Set D → Prop) (Pure : D → Prop) : Prop :=
  ∀ d S, Pure d → (∀ e ∈ S, Pure e) → ¬ RequiresLack d S

/-! ## Finite controls

The carrier is the #2153 one: the two-being, two-world `rootProfile` (source
`true`, the only actual root at `true`; effect `false`, grounded by it), with
the structural `composite`, `prior` and `rep` of
`RootPerfectionExclusion.Control`. For A, one determination (`Unit`, read as
`wisdom`), contents `Bool` with `about c x := c = x`, and one understanding
respect (`Unit`). For B, the five #1970 determinations. These are assignments of
the stated relations only. -/
namespace Control

open TruthCore.Causality.SourceIntellectControls.ProfileControls (Determination)

/-- The source is its own being (always, or never). -/
def ownIf (p : Prop) (x : Bool) : Prop := x = true ∧ p
/-- The source has `wisdom` exactly when `p`; the effect never. -/
def hasIf (p : Prop) (x : Bool) (_ : Unit) : Prop := x = true ∧ p
/-- `wisdom` is pure exactly when `p`. -/
def pureIf (p : Prop) (_ : Unit) : Prop := p
/-- The source's own content about itself (`true` about `true`), exactly when `p`. -/
def selfIf (p : Prop) (x c : Bool) : Prop := x = true ∧ c = true ∧ p
/-- The source is in potency in the understanding respect exactly when `p`. -/
def potencyIf (p : Prop) (x : Bool) (_ : Unit) : Prop := x = true ∧ p
/-- Contents about a being: the content named by that being. -/
def about (c x : Bool) : Prop := c = x
/-- Every content about a being is correct of it. -/
def correct (c x : Bool) : Prop := c = x
/-- GOD_4 names the being `n`. -/
def isGod (n x : Bool) : Prop := x = n
/-- The unary `HasIntellect` holds of the source exactly when `p`. -/
def intellectIf (p : Prop) (x : Bool) : Prop := x = true ∧ p

/-- The set-level requirement relations of the B controls. -/
def noRequirement (_ : Determination) (_ : Set Determination) : Prop := False
/-- The nonpure `limiter` requires the lack of `noesis`. -/
def limiterExcludesNoesis (d : Determination) (S : Set Determination) : Prop :=
  d = Determination.limiter ∧ S = {Determination.noesis}
/-- The pure `noesis` requires the joint lack of the pure `a` and `b`; no pair
is excluded. -/
def noesisExcludesPair (d : Determination) (S : Set Determination) : Prop :=
  d = Determination.noesis ∧ S = {Determination.a, Determination.b}
/-- The pure `noesis` requires its own lack. -/
def noesisSelfExcluding (d : Determination) (S : Set Determination) : Prop :=
  d = Determination.noesis ∧ S = {Determination.noesis}

open TruthCore.Causality.RootPerfectionExclusion (ActualProfile RootProfilesAdmissible
  PureExtensionsAdmissible PureDeterminationsAdmissible)
open TruthCore.Causality.RootPerfectionExclusion.Control (roots composite prior rep has isPure)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple)
open TruthCore.Causality.PureActRoot
  (ActualRootHasEveryPureDetermination ActualRootDeterminationsArePure)
open TruthCore.Causality.WholePowerPerfection (UnlimitedIsOwnBeing)
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
  (WisdomSelfCapacity SelfCapacityExercisedOrPotent TrueSelfApprehensionGrounded)
open TruthCore.Causality.NecessaryFirstBeing (NecessaryActualFirstPureActAt)
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)

/-! ### Step-one premises and conclusion on the carrier -/

/-- `ownIf o` is its own being whenever it has no limiting principle (`26e8e6ed`). -/
def ownUnlimited (c o : Prop) : Prop := UnlimitedIsOwnBeing (composite c) prior rep rep (ownIf o)
/-- Every actual root has every pure determination (`fe67d766`). -/
def every (h p : Prop) : Prop := ActualRootHasEveryPureDetermination rootProfile true (hasIf h) (pureIf p)
/-- The purity of `wisdom`. -/
def wisdomPure (p : Prop) : Prop := WisdomIsPure (pureIf p) ()
/-- The wisdom-to-self-capacity bridge. -/
def capacity (o h ca : Prop) : Prop :=
  WisdomSelfCapacity (ownIf o) (hasIf h) () about correct (selfIf ca)
/-- The exercise-or-potency bridge, with no potency assigned. -/
def exercise (o ca ap : Prop) : Prop :=
  SelfCapacityExercisedOrPotent (ownIf o) about (selfIf ca) (selfIf ap) (potencyIf False) ()
/-- The cognitive-grounding bridge. -/
def grounding (o ap cg : Prop) : Prop :=
  TrueSelfApprehensionGrounded (ownIf o) about correct (selfIf ap) (selfIf cg)
/-- The step-one conclusion, with potency at the root exactly when `q`. -/
def knows (q ap cg : Prop) : Prop :=
  PureActRootsKnowThemselves rootProfile true about correct (selfIf ap) (selfIf cg) (potencyIf q)

/-! ### Step-two premises and conclusion on the carrier -/

/-- `593d7307` with potency at the root exactly when `q`. -/
def first (q : Prop) : Prop := NecessaryActualFirstPureActAt rootProfile true prior (potencyIf q)
/-- `75974d26` with GOD_4 naming `n`. -/
def reach (n : Bool) : Prop := GodReachesActualConcreta rootProfile true (isGod n)
/-- The recognition bridge. -/
def recognition (n : Bool) (i ap cg : Prop) : Prop :=
  GodIntrinsicSelfKnowledgeIsIntellect (isGod n) (intellectIf i) about correct (selfIf ap) (selfIf cg)
/-- GOD_4 HAS_INTELLECT_1 on the carrier. -/
def godIntellect (n : Bool) (i : Prop) : Prop :=
  TruthCore.Case.Catholicism.GodHasIntellect (isGod n) (intellectIf i)

/-! ### Admissible families for B -/

/-- The pure `a`, `b` and `noesis` are never had together; every smaller
combination is allowed. -/
def bruteTriple (q : Set Determination) : Prop :=
  ¬ (Determination.a ∈ q ∧ Determination.b ∈ q ∧ Determination.noesis ∈ q)
/-- `noesis` needs the impure `limiter` alongside it: a requirement of presence. -/
def needsLimiter (q : Set Determination) : Prop :=
  Determination.noesis ∈ q → Determination.limiter ∈ q
/-- Every determination requires the lack of every infinite set (anchoring control). -/
def infiniteLack (_ : Nat) (S : Set Nat) : Prop := S.Infinite
/-- Every profile is admissible. -/
def anyProfile (_ : Set Determination) : Prop := True
/-- `noesis` is in no admissible profile. -/
def noNoesis (q : Set Determination) : Prop := Determination.noesis ∉ q
/-- The root's actual profile is admissible (`0a9d3a40`). -/
def rootAdm (adm : Set Determination → Prop) (src : Set Determination) : Prop :=
  RootProfilesAdmissible rootProfile true adm (has src)
/-- Every determination of the root is pure (`3b39e0ba`). -/
def rootPure (src : Set Determination) : Prop :=
  ActualRootDeterminationsArePure rootProfile true (has src) isPure

/-- The strictness setting: every profile admissible, `noesis` requiring its
own lack. -/
def strictSetting : TruthCore.Logic.StrengthComparison.ComparisonSpec :=
  mgOverSufficiency anyProfile noesisSelfExcluding

/-- In `strictSetting` the sufficiency direction holds and member grounding
fails. -/
def StrictSeparates : Prop :=
  TruthCore.Logic.StrengthComparison.Separation strictSetting

end Control

end TruthCore.Causality.RootPerfectionIntellect
