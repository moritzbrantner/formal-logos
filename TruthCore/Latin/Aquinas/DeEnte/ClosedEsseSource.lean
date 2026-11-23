module

public import TruthCore.Latin.Aquinas.DeEnte.EsseSource
public import TruthCore.Causality.ConcreteRootAccess

/-!
# Closed-collection rootedness in the fixed actual esse-cause order (#1639)

`esseCauseGraph` is a graph adapter for one q.3 a.4 profile. Its singleton
index is bookkeeping, not a claim that tenseless causes are world-local,
efficient or presently sustaining. Its selected `grounds` field is exactly
`ActualEsseCause`; no identification with an independently supplied grounding
profile is made. Every supplier has the same actual-bearer guard.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.ClosedGroundingRoots

variable {B P R : Type}

/-- A structural embedding, preserving supplier-to-recipient direction and
both actuality guards. `concrete` here selects actual esse bearers only; it
supplies no bridge to an independently given world-relative concrete domain. -/
def esseCauseGraph (p : Profile B P R) :
    TruthCore.Causality.BruteFoundationBoundary.Profile Unit B where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ x => p.InAct x p.esse
    Causes := fun _ _ _ => False }
  concrete := fun x => p.InAct x p.esse
  grounds := fun _ => ActualEsseCause p

/-- OPEN analyst premise: every nonempty collection of actual esse bearers
closed under every distinct actual cause of its members' esse contains a
bearer without such a cause. All collections are tested, including each
bearer's entire cone of finitely reachable predecessors. Such a cone need
not have finitely many members. Infinite paths and rooted cycles are allowed. -/
def ClosedActualEsseCollectionsRooted (p : Profile B P R) : Prop :=
  ClosedGroundingCollectionsRooted (esseCauseGraph p) ()

/-- The population needed by the CCR transfer: one actual esse bearer.
Unlike the older composition, two different bearers are unnecessary. -/
def ActualEssePopulation (p : Profile B P R) : Prop :=
  ∃ x, p.InAct x p.esse

/-! Exact interpretations of the esse dictionary, not metaphysical models. -/

/-- Lift an explicitly supplied relation to an all-actual control profile.
Only `none` has represented esse equal to essence. Other fields not tested
by this slice are fixed false. -/
def controlProfile {A : Type} (edge : Option A → Option A → Prop) :
    Profile (Option A) Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => edge c x
  essenceOf := fun x => match x with | none => true | some _ => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- A root directly supplies an infinite predecessor chain. CCR and the
common-source conclusion hold while unrestricted well-foundedness fails. -/
def RootedInfiniteControl : Prop :=
  ∃ p : Profile (Option Nat) Bool Unit,
    ClosedActualEsseCollectionsRooted p ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ TwoActualBeings p ∧
    CommonEsseIsEssenceSource p ∧ ¬ NoInfiniteActualEsseCauseRegress p

/-- A root supplies two mutually causing dependents. The cycle does not
include the root; CCR and the common-source endpoint hold. -/
def RootedCycleControl : Prop :=
  ∃ p : Profile (Option Bool) Bool Unit,
    ClosedActualEsseCollectionsRooted p ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ TwoActualBeings p ∧
    CommonEsseIsEssenceSource p ∧
    ActualEsseCause p (some false) (some true) ∧
    ActualEsseCause p (some true) (some false)

/-- An isolated identity root beside a rootless chain: whole-roster root
existence, coverage, uniqueness and population do not imply common ancestry. -/
def RosterOnlyControl : Prop :=
  ∃ p : Profile (Option Nat) Bool Unit,
    (∃ n, p.InAct n p.esse ∧ ∀ c, ¬ ActualEsseCause p c n) ∧
    DistinctEsseHasOtherActualCause p ∧ AtMostOneEsseIsEssence p ∧
    TwoActualBeings p ∧ ¬ ClosedActualEsseCollectionsRooted p ∧
    ¬ CommonEsseIsEssenceSource p

/-- One actual bearer suffices for the new population; two need not exist. -/
def SingletonPopulationControl : Prop :=
  ∃ p : Profile Unit Bool Unit, ActualEssePopulation p ∧ ¬ TwoActualBeings p


/-- A two-bearer, same-respect actual-esse-cause circle. Both bearers are
actual and have represented esse distinct from essence; each causes the
other's esse. These are uninterpreted causal assignments, *not* evidence
that mutually productive powers can realize their own bearers. -/
def sourceFreeFiniteCircle : Profile Bool Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c ≠ x
  essenceOf := fun _ => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- Local actual-esse cause coverage and identity uniqueness hold, but no
actual bearer is underived. The finite whole is closed under its suppliers,
so CCR and the common-source endpoint fail. A productive-priority premise
would be new, not implicit in this control. -/
def SourceFreeFiniteCircleControl : Prop :=
  (∀ x, DistinctEsseAt sourceFreeFiniteCircle x) ∧
  DistinctEsseHasOtherActualCause sourceFreeFiniteCircle ∧
  AtMostOneEsseIsEssence sourceFreeFiniteCircle ∧
  ActualEssePopulation sourceFreeFiniteCircle ∧
  (∀ x, ∃ c, ActualEsseCause sourceFreeFiniteCircle c x) ∧
  ActualEsseCause sourceFreeFiniteCircle false true ∧
  ActualEsseCause sourceFreeFiniteCircle true false ∧
  ¬ ClosedActualEsseCollectionsRooted sourceFreeFiniteCircle ∧
  ¬ CommonEsseIsEssenceSource sourceFreeFiniteCircle

/-- Joint controls for strictness, rooted cycles, roster-only failure and
population weakening. Interpretations only, not metaphysical counterexamples. -/
def ClosedEsseControls : Prop :=
  RootedInfiniteControl ∧ RootedCycleControl ∧ RosterOnlyControl ∧
    SingletonPopulationControl

end TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
