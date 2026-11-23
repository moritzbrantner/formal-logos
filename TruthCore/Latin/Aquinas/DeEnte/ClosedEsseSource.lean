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

/-- Local actual-esse cause coverage holds, and identity uniqueness holds
vacuously (no bearer has esse equal to essence), but no actual bearer is
underived. The finite whole is closed under its suppliers, so CCR and the
common-source endpoint fail. A productive-priority premise is not implicit in
this control; the existing `noPerSeCausalLoop` (PER-SE-CAUSAL-LOOP-IMPOSSIBLE)
excludes such finite loops given cause-over-effect priority, transitivity and
irreflexivity, so what is missing is a bridge from `ActualEsseCause` to that
efficient/per se priority reading. -/
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

/-- An assignment of bearers that satisfies an abstract global activation
rule. The assignment is not thereby an actual world or an existential cause. -/
def SupplierStateFixed (rule : (B → Prop) → B → Prop) (state : B → Prop) : Prop :=
  ∀ x, rule state x ↔ state x

/-- Every activation under ANY candidate assignment presupposes an active
bearer connected by the exact same-respect actual-esse-cause relation.
This is a non-spontaneity condition on the rule, not a consequence of
`ActualEsseCause` or proof that the assigned acts really occur. -/
def EntirelyBorrowedRule (p : Profile B P R)
    (rule : (B → Prop) → B → Prop) : Prop :=
  ∀ state x, rule state x → ∃ c, ActualEsseCause p c x ∧ state c

/-- A rule with an unconstrained, seed-labelled activation exception to
supplier borrowing. A seed is not *yet* an independent existent or r-root:
that interpretation requires the separate SeedIsActualEsseRoot bridge.
The direction is necessary, not sufficient: labelling an input as a seed
does not by itself activate a bearer in an assignment. -/
def SeedOrBorrowedRule (p : Profile B P R)
    (seed : B → Prop) (rule : (B → Prop) → B → Prop) : Prop :=
  ∀ state x, rule state x →
    seed x ∨ ∃ c, ActualEsseCause p c x ∧ state c

/-- OPEN applicability bridge: any claimed independent input is an actual,
underived bearer in the same r, not merely an abstract law, totality or
uninstantiated capacity. Neither uniqueness nor the rule proves this. -/
def SeedIsActualEsseRoot (p : Profile B P R) (seed : B → Prop) : Prop :=
  ∀ x, seed x → p.InAct x p.esse ∧ ∀ c, ¬ ActualEsseCause p c x

/-- Joint controls for strictness, rooted cycles, roster-only failure and
population weakening. Interpretations only, not metaphysical counterexamples. -/
def ClosedEsseControls : Prop :=
  RootedInfiniteControl ∧ RootedCycleControl ∧ RosterOnlyControl ∧
    SingletonPopulationControl


/-! State-indexed interpretation test for actual holistic selection (#1724/#1616).
Unlike SupplierStateFixed, these assignments change the profile's InAct guard.
The state changes the extension of actual bearers without changing bearer
identities, the causal dictionary or the represented essence/esse values. -/

/-- The actual-bearer guard changes with a candidate configuration. Its
cause assignments are still structural and mode-unspecified: this does not
model an actual productive exercise, an actual world, or an organizing whole. -/
def circleAtState (state : Bool → Prop) : Profile Bool Bool Unit :=
  { sourceFreeFiniteCircle with InAct := fun x _ => state x }

/-- Every member of a candidate state has an actually admitted incoming
same-respect esse-cause *in that state*. Unlike the old fixed-p rule, both
the supplier's and recipient's actuality guards now vary with the state.
This is a reciprocal-support equation, not a sufficient productive act. -/
def CircleStateFixed (state : Bool → Prop) : Prop :=
  ∀ x : Bool, state x ↔ ∃ c, ActualEsseCause (circleAtState state) c x

/-- The holist's substantive global admission of a populated order.
The nonemptiness conjunct is NOT inferred from the two causal arrows,
their fixed-point equation or productive sufficiency; the holist must
defend it as an ontic law, necessarily obtaining whole or primitive fact. -/
def HolisticCircleAdmissible (state : Bool → Prop) : Prop :=
  CircleStateFixed state ∧ ∃ x, state x

/-- A counterinterpretation to any unconditional inference from unique
populated, globally admissible mutual supply to an r-uncaused bearer. The
empty candidate is itself fixed but excluded by the OPEN global
nonemptiness admission; every admitted state has both bearers active,
and both have an incoming r-cause. It is a structural test with
state-indexed InAct, not a model of real constitutive/productive powers. -/
def StateIndexedHolisticCircleControl : Prop :=
  CircleStateFixed (fun _ : Bool => False) ∧
  HolisticCircleAdmissible (fun _ : Bool => True) ∧
  (∀ state, HolisticCircleAdmissible state → ∀ x, state x) ∧
  (∀ x, ∃ c, ActualEsseCause (circleAtState (fun _ => True)) c x) ∧
  ¬ (∃ n : Bool, ∀ c, ¬ ActualEsseCause (circleAtState (fun _ => True)) c n)

end TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
