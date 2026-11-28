module

public import Mathlib.Order.Minimal
public import Mathlib.Order.Interval.Set.Infinite
public import TruthCore.Causality.SourceIntellectControls
public import TruthCore.Causality.RootPurity
public import TruthCore.Causality.FiniteEsseDependence
public import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution

/-! # Why could a pure perfection be absent at an actual root? (#2145, Investigation 1)

Analyst formulation, attribution deferred. Three candidate explanations of the
absence of one determination `k` at a bearer `x` are compared over ONE supplied
family `Admissible` of intrinsic profiles (sets of real determinations):

1. `AbsenceFromAdmissibility`: no admissible profile contains `k` at all. With
   `Admissible` read as the profiles a metaphysically simple, unreceived source
   could jointly have, this is the home of "k is incompatible with simplicity"
   (for example the real-duality fork of the Plotinian objection), or with the
   other admissibility constraints (unreceivedness, necessity, any further
   warranted incompatibility).
2. `AbsenceFromPositiveProfile`: `k` occurs in some admissible profile, but no
   admissible profile contains both the bearer's actual determinations and `k`.
   When the bearer's own profile is admissible, its positive determinations,
   singly or only jointly, exclude `k`. When NO admissible profile contains
   the bearer's profile, every `k` admissible somewhere falls here vacuously
   (`absenceVacuousWithoutAdmissibleSuperset`; `anchorControl` is such a
   case). Inadmissibility of the profile alone does not give this: the family
   need not be closed downward, so an inadmissible profile can have an
   admissible superset, and its omissions can then be unexplained (case 3).
   So the gloss needs `RootProfilesAdmissible`.
3. `UnexplainedAbsence`: an admissible profile contains the bearer's actual
   determinations together with `k`, yet the bearer lacks `k`. Neither the
   admissibility constraints nor the positive profile fix the omission.

`Admissible` is a declared PRIMITIVE parameter. Intended meaning: the profile
is jointly realizable by a simple, unreceived, necessary source under the
necessary incompatibilities taken as warranted. Distinguishing condition: it is
not "the profile some actual being has" and not a set of possible worlds. Which
profiles are admissible is supplied by each interpretation. The classification
is relative to that family: narrowing it can move an absence from case 3 to
case 1 or 2, which is why each premise below quantifies over the same family.
The "positive nature" of a bearer is represented by its `Has` profile; a
holistic constraint not represented by any determination must be represented
as a restriction of `Admissible`. Such a restriction falls under case 1 only
if it excludes `k` from every admissible profile. If it admits `k` alone but
forbids its combination with the bearer's profile, it falls under case 2;
`ProfileControls.jointConflict` is such a family (every pure pair admissible,
the triple `a`, `b`, `noesis` forbidden). Extrinsic explanation is not one of
the cases. At an `ActualRoot` there is no explanation through the selected
actual-concrete grounding relation, because no actual concrete being grounds
the root. Whether every extrinsic explanation of an absence would supply such
a ground is an OPEN bridge that `ActualRoot` does not contain; reading
`NoUnexplainedAbsenceAtRoots` as excluding all unexplained absences uses it.

The premises below are OPEN analyst bridges. The limitation senses stay
distinct (`DISAMB-NB-A8-LIMITATION-AND-ENTAILMENT`, `DISAMB-ESSE-LIMITATION`):
`PositiveProfileExclusionLimits` targets the structural
`RootMultiplication.HasLimitingPrinciple`, and
`PositiveProfileExclusionLimitsEsse` targets the primitive `Limited` of
`FiniteEsseDependence`. -/

@[expose] public section

namespace TruthCore.Causality.RootPerfectionExclusion

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)
open TruthCore.Causality.SourceIntellectControls (HasCompatibleExtension)

variable {W B D P : Type}

/-- The real-determination profile of a bearer: the set of its `Has` determinations. -/
def ActualProfile (Has : B → D → Prop) (x : B) : Set D := {d | Has x d}

/-- Case (i): `x` lacks `k`, and no admissible profile contains `k`. -/
def AbsenceFromAdmissibility (Admissible : Set D → Prop) (Has : B → D → Prop)
    (x : B) (k : D) : Prop :=
  ¬ Has x k ∧ ∀ q, Admissible q → k ∉ q

/-- Case (ii): `x` lacks `k`; `k` is admissible somewhere, but not together with
all of `x`'s actual determinations. -/
def AbsenceFromPositiveProfile (Admissible : Set D → Prop) (Has : B → D → Prop)
    (x : B) (k : D) : Prop :=
  ¬ Has x k ∧ (∃ q, Admissible q ∧ k ∈ q) ∧
    ¬ HasCompatibleExtension Admissible (ActualProfile Has x) k

/-- Case (iii), brute or unexplained absence: `x` lacks `k` although an
admissible profile contains `x`'s actual determinations and `k`. -/
def UnexplainedAbsence (Admissible : Set D → Prop) (Has : B → D → Prop)
    (x : B) (k : D) : Prop :=
  ¬ Has x k ∧ HasCompatibleExtension Admissible (ActualProfile Has x) k

/-- OPEN: the actual profile of every actual root at `w` is admissible. This
anchors the family to the actual root rather than to some other bearer. -/
def RootProfilesAdmissible (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Has : B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → Admissible (ActualProfile Has r)

/-- OPEN joint compossibility of pure determinations, relative to the family:
adding a pure determination that is admissible somewhere to an admissible
profile of pure determinations yields an admissible profile. It is a one-step
insertion law; it does not say that every set of pure determinations is
admissible, and pairwise compatibility does not imply it. -/
def PureExtensionsAdmissible (Admissible : Set D → Prop) (Pure : D → Prop) : Prop :=
  ∀ q k, Admissible q → (∀ d ∈ q, Pure d) → Pure k →
    (∃ q', Admissible q' ∧ k ∈ q') → Admissible (insert k q)

/-- OPEN: each pure determination occurs in some admissible profile. Its denial
for a given `k` is case (i): `k` is incompatible with the constraints alone. -/
def PureDeterminationsAdmissible (Admissible : Set D → Prop) (Pure : D → Prop) : Prop :=
  ∀ k, Pure k → ∃ q, Admissible q ∧ k ∈ q

/-- OPEN, general over every determination (pure or not): no actual root has an
unexplained absence. Every omission at an actual root is fixed by the
admissibility constraints or by the root's positive profile. It has the same
form for a personal and an impersonal root; given the other premises it is
equivalent, for pure determinations, to the conclusion it is used for. -/
def NoUnexplainedAbsenceAtRoots (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Has : B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, ¬ UnexplainedAbsence Admissible Has r d

/-- The L bridge in the structural sense: a bearer whose admissible actual
profile excludes an admissible pure determination has one of the three
represented limiting principles. -/
def PositiveProfileExclusionLimits (Admissible : Set D → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (Composite : B → Prop) (Prior : B → B → Prop)
    (essence esse : B → P) : Prop :=
  ∀ x k, Admissible (ActualProfile Has x) → Pure k → (∃ q, Admissible q ∧ k ∈ q) →
    ¬ HasCompatibleExtension Admissible (ActualProfile Has x) k →
    HasLimitingPrinciple Composite Prior essence esse x

/-- The L bridge in the formal-limitation sense: the same exclusion makes the
bearer's act of being limited in the primitive `Limited` sense (LIMITED_ESSE_1). -/
def PositiveProfileExclusionLimitsEsse (Admissible : Set D → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (Limited : B → Prop) : Prop :=
  ∀ x k, Admissible (ActualProfile Has x) → Pure k → (∃ q, Admissible q ∧ k ∈ q) →
    ¬ HasCompatibleExtension Admissible (ActualProfile Has x) k → Limited x

/-- OPEN bridge from determination to esse: a bearer that really has a
determination which is not pure (involves potency, limitation or reception,
DEF-PURE-PERFECTION) has limited esse. It mentions no absence. -/
def ImpureDeterminationLimitsEsse (Has : B → D → Prop) (Pure : D → Prop)
    (Limited : B → Prop) : Prop :=
  ∀ x d, Has x d → ¬ Pure d → Limited x

/-! ## Finite controls

The same two beings for every control: the two-being, two-world `rootProfile` of the
#1873 controls (source `true`, the only actual root at `true`; effect `false`,
grounded by it) and, except in the anchoring control (natural-number
determinations), the five #1970 determinations (`esse`, `a`, `b`, `noesis`
pure; `limiter` not pure). The source's profile `src` and the admissible family
vary; the effect always has `esse` and `noesis`. Structural limitation: the
effect has a distinct simply-prior being; the source has none and is composite
exactly when the supplied proposition holds. Represented essence and esse are
the same constant. These are assignments of the stated relations only; they
say nothing about what admissibility, purity or limitation metaphysically are. -/
namespace Control

open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination pure positive effect)

/-- Purity as a predicate: membership in the #1970 pure set. -/
def isPure (d : Determination) : Prop := d ∈ pure

/-- The source has `src`; the effect has `esse` and `noesis`. -/
def has (src : Set Determination) : Bool → Determination → Prop
  | true, d => d ∈ src
  | false, d => d ∈ effect

/-- The source is composite exactly when `c`; the effect is never composite. -/
def composite (c : Prop) (x : Bool) : Prop := x = true ∧ c

/-- The source is simply prior to the effect. -/
def prior (y x : Bool) : Prop := y = true ∧ x = false

/-- One represented principle for both essence and esse. -/
def rep (_ : Bool) : Unit := ()

/-- Finite profiles of natural-number determinations, for the anchoring control. -/
def finiteAdmissible (q : Set Nat) : Prop := q.Finite

/-- Every determination is pure in the anchoring control. -/
def allPure (_ : Nat) : Prop := True

/-- The source has every determination except `0`; the effect has none. -/
def hasFromOne : Bool → Nat → Prop
  | true, d => 1 ≤ d
  | false, _ => False

open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (openProfile finiteMode jointConflict exactClosure)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile about effectOnly)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.PureActRoot (ActualRootHasEveryPureDetermination)
open TruthCore.Causality.FiniteEsseDependence (LimitedEsseHasGroundingGiverAt)

/-- No actual root at `true` has a represented limiting principle. -/
def roots (c : Prop) : Prop :=
  ActualRootsWithoutLimitingPrinciple rootProfile true (composite c) prior rep rep
/-- The open RootPurity bridge on the control carrier. -/
def purity (src : Set Determination) (c : Prop) : Prop :=
  UnlimitedDeterminationsArePure (composite c) prior rep rep (has src) isPure
/-- The structural L bridge on the control carrier. -/
def limits (adm : Set Determination → Prop) (src : Set Determination) (c : Prop) : Prop :=
  PositiveProfileExclusionLimits adm (has src) isPure (composite c) prior rep rep
/-- Joint compossibility on the control carrier. -/
def extend (adm : Set Determination → Prop) : Prop := PureExtensionsAdmissible adm isPure
/-- The root's actual profile is admissible. -/
def rootAdm (adm : Set Determination → Prop) (src : Set Determination) : Prop :=
  RootProfilesAdmissible rootProfile true adm (has src)
/-- Each pure determination is admissible somewhere. -/
def pureAdm (adm : Set Determination → Prop) : Prop := PureDeterminationsAdmissible adm isPure
/-- No unexplained absence at the actual root. -/
def noBrute (adm : Set Determination → Prop) (src : Set Determination) : Prop :=
  NoUnexplainedAbsenceAtRoots rootProfile true adm (has src)
/-- The conclusion `fe67d766` on the control carrier. -/
def full (src : Set Determination) : Prop :=
  ActualRootHasEveryPureDetermination rootProfile true (has src) isPure

/-- A source profile containing the token `noesis` but lacking `a`. No
apprehension relation is assigned with it; it is a profile-level check only. -/
def personal : Set Determination := {Determination.esse, Determination.b, Determination.noesis}
/-- The source's actual profile with a nonpure limiter. -/
def limitedMode : Set Determination := insert Determination.limiter positive

/-- Structural-sense controls for the two E∘L arguments. Each row lists which
premises hold and which fail, on the same carrier:
1. positive witness: every premise and the conclusion;
2. standing rival: only no-unexplained-absence fails; the absence of `noesis`
   is case (iii);
3. pure-content obstruction: joint compossibility and the L bridge fail; the
   absence is case (ii) though every pure pair is admissible (#1970);
4. exact closure: `noesis` is in no admissible profile, case (i);
5. finite-mode blocker without a represented limiting principle: the
   RootPurity bridge and the L bridge fail;
6. the same profile at a composite source: the root's lack of a limiting
   principle fails. -/
def StructuralControls : Prop :=
  (roots False ∧ purity pure False ∧ extend openProfile ∧ limits openProfile pure False ∧
    rootAdm openProfile pure ∧ pureAdm openProfile ∧ noBrute openProfile pure ∧ full pure) ∧
  (roots False ∧ purity positive False ∧ extend openProfile ∧
    limits openProfile positive False ∧ rootAdm openProfile positive ∧ pureAdm openProfile ∧
    ¬ noBrute openProfile positive ∧
    UnexplainedAbsence openProfile (has positive) true Determination.noesis ∧
    ¬ full positive) ∧
  (roots False ∧ purity positive False ∧ ¬ extend jointConflict ∧
    ¬ limits jointConflict positive False ∧ rootAdm jointConflict positive ∧
    pureAdm jointConflict ∧ noBrute jointConflict positive ∧
    AbsenceFromPositiveProfile jointConflict (has positive) true Determination.noesis ∧
    ¬ full positive) ∧
  (roots False ∧ purity positive False ∧ extend exactClosure ∧
    limits exactClosure positive False ∧ rootAdm exactClosure positive ∧
    ¬ pureAdm exactClosure ∧ noBrute exactClosure positive ∧
    AbsenceFromAdmissibility exactClosure (has positive) true Determination.noesis ∧
    ¬ full positive) ∧
  (roots False ∧ ¬ purity limitedMode False ∧ extend finiteMode ∧
    ¬ limits finiteMode limitedMode False ∧ rootAdm finiteMode limitedMode ∧
    pureAdm finiteMode ∧ noBrute finiteMode limitedMode ∧ ¬ full limitedMode) ∧
  (¬ roots True ∧ purity limitedMode True ∧ extend finiteMode ∧
    limits finiteMode limitedMode True ∧ rootAdm finiteMode limitedMode ∧
    pureAdm finiteMode ∧ noBrute finiteMode limitedMode ∧ ¬ full limitedMode)

/-- Anchoring control: an infinite all-pure root profile, finite admissible
profiles. Joint compossibility holds as a one-step insertion law, yet no
admissible profile contains the root's actual profile, so no absence is
unexplained and the root lacks the pure `0`. -/
def AnchorControl : Prop :=
  ActualRootsWithoutLimitingPrinciple rootProfile true (composite False) prior rep rep ∧
  UnlimitedDeterminationsArePure (composite False) prior rep rep hasFromOne allPure ∧
  PureExtensionsAdmissible finiteAdmissible allPure ∧
  PositiveProfileExclusionLimits finiteAdmissible hasFromOne allPure
    (composite False) prior rep rep ∧
  ¬ RootProfilesAdmissible rootProfile true finiteAdmissible hasFromOne ∧
  PureDeterminationsAdmissible finiteAdmissible allPure ∧
  NoUnexplainedAbsenceAtRoots rootProfile true finiteAdmissible hasFromOne ∧
  ¬ ActualRootHasEveryPureDetermination rootProfile true hasFromOne allPure

/-- Nothing is limited. -/
def noLimit (_ : Bool) : Prop := False
/-- Only the source is limited. -/
def sourceLimited (x : Bool) : Prop := x = true
/-- No causal edge in the esse respect. -/
def noCause (_ _ : Bool) (_ : Unit) : Prop := False
/-- The limited-esse giver premise 08178314 on the control carrier. -/
def giver (L : Bool → Prop) : Prop := LimitedEsseHasGroundingGiverAt rootProfile true L noCause ()
/-- The formal-limitation L bridge on the control carrier. -/
def limitsEsse (adm : Set Determination → Prop) (src : Set Determination)
    (L : Bool → Prop) : Prop :=
  PositiveProfileExclusionLimitsEsse adm (has src) isPure L
/-- The determination-to-esse bridge on the control carrier. -/
def impureLimits (src : Set Determination) (L : Bool → Prop) : Prop :=
  ImpureDeterminationLimitsEsse (has src) isPure L

/-- Formal-limitation controls for the second pair of arguments. They evaluate
the giver premise, the determination-to-esse bridge and the formal L bridge
over the admissible families of `StructuralControls` and `AnchorControl`, whose
admissibility, compossibility and no-unexplained-absence facts carry over
unchanged: positive witness; standing rival (only no-unexplained-absence
fails); pure-content obstruction (with nothing limited the L bridge fails, and
joint compossibility fails there); finite-mode blocker with nothing limited
(the determination-to-esse bridge and the L bridge fail); a limited source with
no causal edge (the giver premise fails because the source is a root, which has
no actual concrete ground, and because the causal relation is emptied); the
exact-closure family (the L bridge holds with nothing limited, so the failure of
pure admissibility is the only failing premise there); and the anchoring
control (the L bridge holds with nothing limited, so the failure of root-profile
admissibility is the only failing premise there). -/
def EsseControls : Prop :=
  (giver noLimit ∧ impureLimits pure noLimit ∧ limitsEsse openProfile pure noLimit) ∧
  (giver noLimit ∧ impureLimits positive noLimit ∧ limitsEsse openProfile positive noLimit) ∧
  (giver noLimit ∧ impureLimits positive noLimit ∧ ¬ limitsEsse jointConflict positive noLimit) ∧
  (giver noLimit ∧ ¬ impureLimits limitedMode noLimit ∧
    ¬ limitsEsse finiteMode limitedMode noLimit) ∧
  (¬ giver sourceLimited ∧ impureLimits limitedMode sourceLimited ∧
    limitsEsse finiteMode limitedMode sourceLimited) ∧
  (giver noLimit ∧ limitsEsse exactClosure positive noLimit) ∧
  PositiveProfileExclusionLimitsEsse finiteAdmissible hasFromOne allPure noLimit

open TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence.Control
  (ImpersonalEminence effectPotency)
open TruthCore.Results.Causality.IntentionalExemplarExtension.ImmanentSelfPresence.Control
  (own)

/-- The standing impersonal profile on one carrier. The #1892 source `true`
(necessary actual root, own being, nonvacuously pure act, constitutively
simple, own exemplar form norming an actual knower, apprehending nothing)
satisfies the exercise-or-potency reading when its own capacity is SET EQUAL to
its actual apprehension (`effectOnly`); that choice makes the exercise-or-potency
conjunct trivial, so the simplicity collapse holds while the source has
neither aptitude nor exercise. The `Has` profile and the #1892 apprehension
relations are separate assignments on the same beings. The bridge conjunct
links them for the impersonal profile: a being has `noesis` in `Has` exactly
when it apprehends some content in `effectOnly`. With that link, the structural
premises other than no-unexplained-absence hold, and the source's absence of
`noesis` is unexplained (case iii).

The last three conjuncts are a `Has`-profile parity check only. A source whose
`Has` profile contains `noesis` but lacks the admissible pure `a` violates the
same premise. It is not a personal variant of the #1892 source: in the #1892
relations conjoined here that source still apprehends nothing, and no
apprehension relation is assigned to the variant. -/
def StandingRival : Prop :=
  ImpersonalEminence ∧
  TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding.SelfCapacityExercisedOrPotent
    own about effectOnly effectOnly effectPotency () ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PureAct effectPotency true ∧
  (∀ c, ¬ effectOnly true c) ∧
  (∀ x, has positive x Determination.noesis ↔ ∃ c, effectOnly x c) ∧
  roots False ∧ purity positive False ∧ extend openProfile ∧
  limits openProfile positive False ∧ rootAdm openProfile positive ∧ pureAdm openProfile ∧
  UnexplainedAbsence openProfile (has positive) true Determination.noesis ∧
  has personal true Determination.noesis ∧
  UnexplainedAbsence openProfile (has personal) true Determination.a ∧
  ¬ noBrute openProfile personal

end Control

end TruthCore.Causality.RootPerfectionExclusion
