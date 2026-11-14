module

public import TruthCore.Latin.Aquinas.DeEnte.EsseSource
public import TruthCore.Causality.ActualRootUniqueness
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Causality.TermSenseForks2

/-!
# De ente: the first source of esse at the root interface, and a per se regress (#1635)

Two bridges from the De ente esse-source reconstruction (#1628,
`EsseSource`) to the rest of the case.

**The root interface.** `CommonEsseIsEssenceSource` lives in the order of
causes of being of the shared q.3 a.4 `Profile` (`InAct`, `CausesIn` at
`esse`, world-free). The root interface `NecessaryRootFork.ActualRoot m w n`
lives in the world-relative grounding order of a
`BruteFoundationBoundary.Profile` over the same carrier of beings. The two
OPEN bridges below say how a being whose esse is its essence sits in the
grounding order:

* `ActualEsseIsEssenceIsActualConcreteAt` (a restricted converse of
  `ExistingInActAt`, with concreteness added): a being in act whose esse is
  its essence is concrete and exists at the selected world `w`;
* `GroundOfEsseIsEssenceBeingCausesItsEsse` (a restricted converse of
  `EsseCauseIsActualConcreteGround`): an actual concrete ground at `w` of a
  being in act whose esse is its essence is a cause of its esse.

Both are restricted to beings whose esse is their essence, the only instances
the route uses; their unrestricted forms are stronger and are not stated.
Neither holds by definition: the encoded predicates admit interpretations in
which such a being does not exist at `w`, and in which it has an actual
concrete ground that does not cause its esse. The controls below exhibit both;
they are not evidence that either case is possible.

**The per se regress.** `NoInfiniteActualEsseCauseRegress` (#1628) is
well-foundedness of every actual cause of being. ST I q.46 a.2 ad 7 (pinned
passage `a34be6a3`) holds, of efficient causes, that an infinite series is
impossible *per se*, "si causae quae per se requiruntur ad aliquem effectum,
multiplicarentur in infinitum", and not impossible *per accidens*, where the
causes "non teneant ordinem nisi unius causae", as with successive hammers, or
with generators who all have "gradum unum in causis efficientibus", since
"accidit huic homini, inquantum generat, quod sit generatus ab alio". The per
se link here is the primitive `AsCaused c x` (sense PER_SE_5): c causes the
esse of x only insofar as c's own esse is caused, so that c's being caused is
not accidental to its causing x's esse. It is an analyst analogue, for causes
of esse of unspecified mode, of the order ad 7 states for efficient causes.
It is constrained only by the premises that use it; nothing defines it from
well-foundedness, time, or efficiency.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)

variable {B P R : Type}

/-! ## The root interface -/

/-- OPEN analyst bridge, attribution deferred: every being in act as to being
whose represented esse equals its essence is concrete and exists at the
selected world `w` (`ActualConcrete m w x`). The q.3 a.4 profile is
world-free; this reads its actuality at `w` for such beings only. -/
def ActualEsseIsEssenceIsActualConcreteAt {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R) : Prop :=
  ∀ x, p.InAct x p.esse → p.esseOf x = p.essenceOf x → ActualConcrete m w x

/-- OPEN analyst bridge, attribution deferred: if y is an actual concrete
ground at `w` of a being x in act whose represented esse equals its essence,
then y causes the esse of x (`CausesIn y x esse`, mode unspecified). For such
an x, a ground of its existence would be a cause of its esse. No substantive
objection is recorded; `NonCausalGroundControl` shows only that the encoded
predicates do not force it. -/
def GroundOfEsseIsEssenceBeingCausesItsEsse {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R) : Prop :=
  ∀ y x, ActualConcreteGround m w y x → p.InAct x p.esse →
    p.esseOf x = p.essenceOf x → p.CausesIn y x p.esse

/-- The De ente first source is an actual concrete root of the selected
grounding relation at `w`: some n is an actual root at `w` (concrete, existing
at `w`, with no actual concrete ground there), is in act as to being, has its
represented esse equal to its essence, has no actual cause of its esse, and
heads a finite chain of actual causes of being (mode unspecified, tenseless)
to every other being in act. Not asserted: that it is the only root, that it
exists necessarily, that it is an efficient cause, or that it is God. -/
def DeEnteFirstSourceIsActualRootAt {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R) : Prop :=
  ∃ n, ActualRoot m w n ∧ p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
    (∀ c, ¬ ActualEsseCause p c n) ∧
    ∀ x, p.InAct x p.esse → x ≠ n → Relation.TransGen (ActualEsseCause p) n x

/-! ## The per se regress -/

/-- c is an actual cause of the esse of x (`ActualEsseCause`) and causes it
per se, as caused (`AsCaused c x`, the primitive per se link). -/
def PerSeActualEsseCause (p : Profile B P R) (AsCaused : B → B → Prop) (c x : B) : Prop :=
  ActualEsseCause p c x ∧ AsCaused c x

/-- OPEN analyst premise, attribution deferred: there is no infinite
descending chain of actual causes of being each of which causes the esse of
the next per se, as caused (well-foundedness of `PerSeActualEsseCause`). It is
an analyst analogue, for causes of esse of unspecified mode, of the per se
regress ST I q.46 a.2 ad 7 denies for efficient causes, and it is weaker than
`NoInfiniteActualEsseCauseRegress`: it says nothing about chains whose links
are accidentally ordered. -/
def NoInfinitePerSeActualEsseCauseRegress (p : Profile B P R) (AsCaused : B → B → Prop) :
    Prop :=
  WellFounded (PerSeActualEsseCause p AsCaused)

/-- OPEN analyst bridge, attribution deferred: an actual cause c of the esse
of x that itself has an actual cause of its esse causes x's esse as caused
(per se). That is, among actual causes of being, a caused cause's being caused
is never accidental to its causing being, unlike ad 7's generator, who
"generat ... inquantum homo, et non inquantum est filius alterius hominis".
The per accidens rival denies it. -/
def CausedEsseCauseCausesAsCaused (p : Profile B P R) (AsCaused : B → B → Prop) : Prop :=
  ∀ c x, ActualEsseCause p c x → (∃ d, ActualEsseCause p d c) → AsCaused c x

/-! ## Controls

Interpretations of the shared vocabulary only. They show which premises the
conclusions need under the encoded predicates, not that a per accidens series
of causes of being, a non-causal ground of a first source, or a first source
absent from the selected world is possible or plausible. -/

/-- A one-world grounding profile over `B` with the given concreteness,
existence at the single world and grounding. The frame is the one-world frame
with trivial accessibility. -/
def oneWorld (concrete exist : B → Prop) (grounds : B → B → Prop) :
    TruthCore.Causality.BruteFoundationBoundary.Profile Unit B where
  ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ x => exist x,
             Causes := fun _ _ _ => False }
  concrete := concrete
  grounds := fun _ => grounds

/-- Per accidens regress: on `Nat`, n+1 causes the esse of n, every being is in
act with distinct esse, and no link is per se (`AsCaused` empty). The #1629
step and the per se regress hold; the per se bridge, the unrestricted regress
and the regress conclusion fail. -/
def PerAccidensRegressControl : Prop :=
  ∃ (p : Profile Nat Bool Unit) (AsCaused : Nat → Nat → Prop),
    DistinctEsseHasOtherActualCause p ∧ NoInfinitePerSeActualEsseCauseRegress p AsCaused ∧
    ¬ CausedEsseCauseCausesAsCaused p AsCaused ∧ ¬ NoInfiniteActualEsseCauseRegress p ∧
    ¬ EveryDistinctEsseHasEsseIsEssenceSource p

/-- Non-causal ground: `true` (esse equal to essence) causes the esse of
`false`, and `false` grounds `true` at the one world without causing its esse.
The first source, existing-in-act, the concreteness bridge and no
self-causation hold; the ground bridge and the conclusion fail. -/
def NonCausalGroundControl : Prop :=
  ∃ (m : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool)
    (p : Profile Bool Bool Unit),
    CommonEsseIsEssenceSource p ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt m.ontic p.InAct p.esse () ∧
    ActualEsseIsEssenceIsActualConcreteAt m () p ∧
    TruthCore.Causality.TermSenseForks.NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ GroundOfEsseIsEssenceBeingCausesItsEsse m () p ∧
    ¬ DeEnteFirstSourceIsActualRootAt m () p

/-- Absent source: the same causes of being, nothing grounds anything, and
`true` does not exist at the one world. Every other input holds; the
concreteness bridge and the conclusion fail. -/
def AbsentSourceControl : Prop :=
  ∃ (m : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool)
    (p : Profile Bool Bool Unit),
    CommonEsseIsEssenceSource p ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt m.ontic p.InAct p.esse () ∧
    GroundOfEsseIsEssenceBeingCausesItsEsse m () p ∧
    TruthCore.Causality.TermSenseForks.NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ ActualEsseIsEssenceIsActualConcreteAt m () p ∧
    ¬ DeEnteFirstSourceIsActualRootAt m () p

/-- Self-ground: `true` grounds itself and causes its own esse. Every other
input holds; no self-causation and the conclusion fail. -/
def SelfGroundControl : Prop :=
  ∃ (m : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool)
    (p : Profile Bool Bool Unit),
    CommonEsseIsEssenceSource p ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt m.ontic p.InAct p.esse () ∧
    ActualEsseIsEssenceIsActualConcreteAt m () p ∧
    GroundOfEsseIsEssenceBeingCausesItsEsse m () p ∧
    ¬ TruthCore.Causality.TermSenseForks.NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ DeEnteFirstSourceIsActualRootAt m () p

/-- Nonvacuity: `true` (esse equal to essence) causes the esse of `false`, which
it grounds; both are concrete and exist; the cause-of-being link is per se.
Every input of the root-interface and per se arguments holds, and so do their
conclusions. -/
def RootInterfaceNonvacuity : Prop :=
  ∃ (m : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool)
    (p : Profile Bool Bool Unit) (AsCaused : Bool → Bool → Prop),
    CommonEsseIsEssenceSource p ∧
    TruthCore.Causality.ExistenceActuality.ExistingInActAt m.ontic p.InAct p.esse () ∧
    ActualEsseIsEssenceIsActualConcreteAt m () p ∧
    GroundOfEsseIsEssenceBeingCausesItsEsse m () p ∧
    TruthCore.Causality.TermSenseForks.NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    DeEnteFirstSourceIsActualRootAt m () p ∧ AtMostOneActualRootAt m () ∧
    TruthCore.Causality.ActualRootUniqueness.UniqueActualRootAt m () ∧
    NoInfinitePerSeActualEsseCauseRegress p AsCaused ∧
    CausedEsseCauseCausesAsCaused p AsCaused ∧ NoInfiniteActualEsseCauseRegress p

/-- All five controls. -/
def RootInterfaceControls : Prop :=
  PerAccidensRegressControl ∧ NonCausalGroundControl ∧ AbsentSourceControl ∧
    SelfGroundControl ∧ RootInterfaceNonvacuity

end TruthCore.Latin.Aquinas.DeEnte
