module

public import TruthCore.Causality.OneDependenceOrder
public import TruthCore.Causality.PriorityInBeing
public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-!
# Sense splits for the one dependence order (#1926 phase 3, continued)

Analyst formulations, attribution deferred. `OneDependenceOrder` (#1942) left two
sense questions, both on root routes:

* **(i) `CausesAsCaused`.** The bridge e8664ab8
  (`PerSeEfficientCausesArePerSeEsseCauses`: every per se efficient-cause link is a
  PER_SE_5 actual cause of being) fails on its bound sense SERIES_OF_CAUSES_3
  (DEF 4a101a4c), because c2880fe0 extends that
  sense to per se mover links (the hand moving the stick causes neither the being
  of the stick nor anything about it beyond its motion).
* **(ii) `PriorSimply`.** The bridge 86efed1a (whatever is PRIOR_1 to another is an
  actual concrete ground of it) meets the same hand-and-stick case on PRIOR_1,
  priority in act in a respect.

This module adds:

* the sense **SERIES_OF_CAUSES_4**, `CausesBeingAsCaused`: here and now `c`
  efficiently causes the *being* of `x` (`EfficientlyCausesIn c x esse`, the
  secunda via's here-and-now efficient causing, DEF-EFFICIENT-CAUSING, at the
  respect of being) and does so per se, as caused (`AsCaused c x`, the per se
  link of PER_SE_5, whose definition glosses it as "c causes the esse of x only
  insofar as c's own esse is caused"). It is defined, not primitive: its
  ingredients are two existing primitives. It is not defined from
  `CausesAsCaused`, from `CausesIn`, from grounding or from priority;
* its no-regress premise, the restated bridge into PER_SE_5, a weaker
  cross-vocabulary bridge that does not mention the per se link, and the open
  inclusion of SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3;
* for PRIOR_4 (`PriorityInBeing.PriorInBeing`, already a sense): a bridge from
  PRIOR_4 among actual concreta to grounding, and the well-foundedness of PRIOR_4
  among actual concreta;
* closed `Bool` and `Nat` interpretations used by the controls of
  `TruthCore.Results.Causality.DependenceOrderSenses`.

Every passage between relations is an OPEN premise. Nothing here identifies
causing, grounding, priority or moving (#1626, #1926 rigor contract 5).

**Why not the shared frame.** `Frame.CausalityFrame` has `PriorSimply`,
`CausesIn` and `esse` but no per se link, no here-and-now efficient causing at a
respect, no `CanBeWithout` and no grounding. The statements take the secunda via
vocabulary (`EfficientlyCausesIn`, `CausesAsCaused`), the q.3 a.4 `Profile` (which
the PER_SE_5 targets bind) and the grounding `Profile` (which AGWF binds), as
`OneDependenceOrder` does. Extending the frame is a coordinator decision.
-/

@[expose] public section

namespace TruthCore.Causality.DependenceOrderSenses

open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.PriorityInBeing (PriorInBeing)
open TruthCore.Latin.Aquinas.DeEnte (ActualEsseCause PerSeActualEsseCause)

/-- The q.3 a.4 profile (beings, principles, respects, `InAct`, `CausesIn`, `esse`). -/
abbrev Q3Profile (B P R : Type) :=
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R

/-- The grounding profile of the necessary-root fork (worlds, `concrete`,
`ontic.ExistsAt`, `grounds`). -/
abbrev GProfile (W B : Type) := TruthCore.Causality.BruteFoundationBoundary.Profile W B

/-! ## (i) The existential sense of the per se efficient-cause link -/

/-- SERIES_OF_CAUSES_4, the existential per se efficient-cause link: here and
now `c` efficiently causes the being of `x` (`EfficientlyCausesIn c x esse`,
DEF-EFFICIENT-CAUSING at the respect of being), and it causes the being of `x`
per se, as caused (`AsCaused c x`, the primitive per se link of PER_SE_5: `c`
causes the esse of `x` only insofar as its own esse is caused). Example (ST I
q.104 a.1, read as an analyst illustration): the sun's present causing of the
light in the air, if the sun's being is itself caused. Non-examples: the hand
moving the stick (a cause of motion, not of the stick's being); a man begetting
a man (a cause of becoming, q.104 a.1). Distinct from SERIES_OF_CAUSES_3
(`CausesAsCaused`, any per se efficient link, including mover links through
c2880fe0). -/
def CausesBeingAsCaused {B R : Type} (EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (AsCaused : B → B → Prop) (c x : B) : Prop :=
  EfficientlyCausesIn c x esse ∧ AsCaused c x

/-- OPEN analyst premise, attribution deferred, the SERIES_OF_CAUSES_4 sibling of
97f5850f: a per se series of efficient causes of being does not go on to
infinity (every being is accessible along `CausesBeingAsCaused`). -/
def NoInfinitePerSeEsseEfficientCauseSeries {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (esse : R) (AsCaused : B → B → Prop) : Prop :=
  ∀ x, Acc (CausesBeingAsCaused EfficientlyCausesIn esse AsCaused) x

/-- OPEN analyst bridge, attribution deferred, e8664ab8 restated on
SERIES_OF_CAUSES_4: every existential per se efficient-cause link is a PER_SE_5
actual cause of being in the q.3 a.4 profile (`c ≠ x`, both in act as to being,
`CausesIn c x esse`, and `AsCaused c x`). The hand-and-stick case does not touch
it: the hand is no existential link. -/
def PerSeEsseLinksArePerSeEsseCauses {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused : B → B → Prop) : Prop :=
  ∀ c x, CausesBeingAsCaused EfficientlyCausesIn p.esse AsCaused c x →
    PerSeActualEsseCause p AsCaused c x

/-- OPEN analyst bridge, attribution deferred, the cross-vocabulary step without
the per se link: a here-and-now efficient cause of the being of something other
than itself is an actual cause of its being in the q.3 a.4 profile (both are in
act as to being and `CausesIn c x esse`). Efficient causing is one mode of the
mode-unspecified `CausesIn`; a present agent of being is in act; an effect whose
being is caused here and now has being. -/
def PresentEfficientEsseCauseIsActualEsseCause {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ c x, c ≠ x → EfficientlyCausesIn c x p.esse → ActualEsseCause p c x

/-- OPEN analyst bridge, attribution deferred, between the two senses: every
SERIES_OF_CAUSES_4 link is a SERIES_OF_CAUSES_3 link (a per se efficient cause
of the being of `x` is a per se link of a series of efficient causes). Not a
definitional fact: `CausesAsCaused` is a primitive. -/
def PerSeEsseLinkIsPerSeCauseLink {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (esse : R) (AsCaused CausesAsCaused : B → B → Prop) : Prop :=
  ∀ c x, CausesBeingAsCaused EfficientlyCausesIn esse AsCaused c x → CausesAsCaused c x

/-- OPEN analyst bridge, attribution deferred: the cause of every
SERIES_OF_CAUSES_4 link is itself, here and now, efficiently caused in some
respect. `AsCaused` says that `c`'s own esse is caused, in a mode it leaves
unspecified; this premise adds that `c` is caused efficiently and now, which is
what the secunda via's per se ordering premise asks of a middle cause. -/
def ExistentialLinkCauseIsEfficientlyCaused {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (esse : R) (AsCaused : B → B → Prop) : Prop :=
  ∀ c x, CausesBeingAsCaused EfficientlyCausesIn esse AsCaused c x →
    ∃ d r, EfficientlyCausesIn d c r

/-! ## (ii) Priority in being and grounding -/

/-- OPEN analyst bridge, attribution deferred, the PRIOR_4 weak sibling of
86efed1a: between two actual concreta at `w`, what is prior in being (PRIOR_4:
`y` can be without `x` and `x` cannot be without `y`) grounds the other at `w`.
It assumes that both relata are actual concreta, so an absent or non-concrete
prior thing (the second falsifier of 86efed1a) does not touch it. -/
def PriorInBeingAmongActualConcretaIsGround {W B : Type} (m : GProfile W B) (w : W)
    (CanBeWithout : B → B → Prop) : Prop :=
  ∀ y x, ActualConcrete m w y → ActualConcrete m w x → PriorInBeing CanBeWithout y x →
    m.grounds w y x

/-- OPEN analyst premise, attribution deferred, the restricted PRIOR_4 sibling of
d85de8e1: priority in being among the actual concreta at `w` is well-founded. -/
def PriorityInBeingWFAmongActualConcreta {W B : Type} (m : GProfile W B) (w : W)
    (CanBeWithout : B → B → Prop) : Prop :=
  WellFounded fun a b : {x // ActualConcrete m w x} => PriorInBeing CanBeWithout a.1 b.1

/-! ## Interpretations for the controls

Interpretations of the shared vocabulary only: they show which premises the
results need under the encoded predicates, not that any configuration is
possible or plausible. -/

namespace Control

open TruthCore.Causality.OneDependenceOrder.Control (edge10)

/-- Here-and-now efficient causing at the one respect, from a relation on beings. -/
def eff {B : Type} (rel : B → B → Prop) : B → B → Unit → Prop := fun c x _ => rel c x

/-- A self-loop at `true`. -/
def loopT (a b : Bool) : Prop := a = true ∧ b = true

/-- Every link is per se, on `Nat`. -/
def allNat (_ _ : Nat) : Prop := True

/-- The upward successor on `Nat`: `y` stands to `x` when `y = x + 1`. -/
def succUp (y x : Nat) : Prop := y = x + 1

/-- Being-without on `Nat` read so that PRIOR_4 is "greater": `y` can be without
`x` when `x < y`. -/
def ltWithout (y x : Nat) : Prop := x < y

/-- Everything can be without everything (PRIOR_4 empty). -/
def allWithout {B : Type} (_ _ : B) : Prop := True

/-- `true` can be without `false` and nothing else (PRIOR_4 is `true → false`). -/
def tfWithout (a b : Bool) : Prop := a = true ∧ b = false

/-- `x` depends for its being on `y` only for `x = false`, `y = true`. -/
def dFT (x y : Bool) : Prop := x = false ∧ y = true

/-- Two respects on `Nat`: being (`true`) and motion (`false`). Efficient
causing of being is the single edge `1 → 0`; efficient causing in motion is the
upward successor. -/
def effTwo (c x : Nat) (r : Bool) : Prop := (r = true ∧ edge10 c x) ∨ (r = false ∧ succUp c x)

/-- The per se efficient links of `effTwo`: the being edge and the motion series. -/
def caaTwo (c x : Nat) : Prop := edge10 c x ∨ succUp c x

/-- A q.3 a.4 profile on `Nat` with two respects: everything in act; the cause
of being is the edge `1 → 0` at the respect of being (`true`). -/
def q3Two : Q3Profile Nat Unit Bool where
  InAct := fun _ _ => True
  CausesIn := fun c x r => r = true ∧ edge10 c x
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := true

/-- Everything concrete and existing on `Nat`; grounding is `ltWithout`. -/
abbrev mLt : GProfile Unit Nat :=
  TruthCore.Causality.OneDependenceOrder.Control.world (fun _ => True) (fun _ => True) ltWithout

/-- Everything concrete and existing on `Nat`; nothing grounds anything. -/
abbrev mNoneNat : GProfile Unit Nat :=
  TruthCore.Causality.OneDependenceOrder.Control.world (fun _ => True) (fun _ => True)
    TruthCore.Causality.OneDependenceOrder.Control.noRel

end Control

/-! ## Control statements -/

open TruthCore.Causality.OneDependenceOrder
  (PerSeEfficientCausesArePerSeEsseCauses ActualEsseCauseIsActualGround)
open TruthCore.Causality.OneDependenceOrder.Control
open Control
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Latin.Aquinas.DeEnte
  (NoInfiniteActualEsseCauseRegress NoInfinitePerSeActualEsseCauseRegress)
open TruthCore.Causality.NecessaryConcreteRouteBridge (SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.Round5Worklist (SimplePriorityWellFounded HistoryEdgesAreEfficientCausings)
open TruthCore.Causality.FiniteBranching (WellFoundedPredecessors)
open TruthCore.Causality.PriorityInBeing (PriorityInBeingRequiresNonmutualDependence)
open TruthCore.Causality.ReflexiveDependenceScope (ActualDistinctDependenceIsGrounding)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NothingPriorToItselfReading NoInfinitePerSeEfficientCauseSeriesReading
   NothingIsEfficientCauseOfItselfReading EfficientCauseIsPriorToEffectReading
   NoInfinitePerSeMoverSeriesReading SecondEfficientCausesCauseOnlyAsCausedReading
   PerSeMoverLinkIsPerSeCauseLinkReading)

/-- Omissions and nonvacuity for the existential series from the PER_SE_5
regress: dropping the regress (causes of being form a two-cycle), dropping the
restated bridge (no causes of being, existential links a two-cycle), and a
nonvacuous interpretation with one existential link. -/
def PerSeEsseSeriesControls : Prop :=
  (¬ NoInfinitePerSeActualEsseCauseRegress pCyc allLinks ∧
    PerSeEsseLinksArePerSeEsseCauses pCyc (eff cyc) allLinks ∧
    ¬ NoInfinitePerSeEsseEfficientCauseSeries (eff cyc) pCyc.esse allLinks) ∧
  (NoInfinitePerSeActualEsseCauseRegress pNone allLinks ∧
    ¬ PerSeEsseLinksArePerSeEsseCauses pNone (eff cyc) allLinks ∧
    ¬ NoInfinitePerSeEsseEfficientCauseSeries (eff cyc) pNone.esse allLinks) ∧
  (NoInfinitePerSeActualEsseCauseRegress pEdge allLinks ∧
    PerSeEsseLinksArePerSeEsseCauses pEdge (eff edgeTF) allLinks ∧
    NoInfinitePerSeEsseEfficientCauseSeries (eff edgeTF) pEdge.esse allLinks ∧
    CausesBeingAsCaused (eff edgeTF) pEdge.esse allLinks true false)

/-- Omissions and nonvacuity for the restated bridge from no self-causation and
the cross-vocabulary bridge: a self-loop of efficient causing, a two-cycle of
efficient causing with no cause of being in the q.3 a.4 profile, and a
nonvacuous interpretation. -/
def PresentCauseControls : Prop :=
  (¬ NothingIsEfficientCauseOfItselfReading (eff loopT) ∧
    PresentEfficientEsseCauseIsActualEsseCause pNone (eff loopT) ∧
    ¬ PerSeEsseLinksArePerSeEsseCauses pNone (eff loopT) allLinks) ∧
  (NothingIsEfficientCauseOfItselfReading (eff cyc) ∧
    ¬ PresentEfficientEsseCauseIsActualEsseCause pNone (eff cyc) ∧
    ¬ PerSeEsseLinksArePerSeEsseCauses pNone (eff cyc) allLinks) ∧
  (NothingIsEfficientCauseOfItselfReading (eff edgeTF) ∧
    PresentEfficientEsseCauseIsActualEsseCause pEdge (eff edgeTF) ∧
    PerSeEsseLinksArePerSeEsseCauses pEdge (eff edgeTF) allLinks ∧
    CausesBeingAsCaused (eff edgeTF) pEdge.esse allLinks true false)

/-- Omissions and nonvacuity for the existential series from 97f5850f and the
inclusion of SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3. The second conjunct is
also the independence of the senses in one direction: an existential link that
is no `CausesAsCaused` link, with 97f5850f holding and the existential series
having a two-cycle. -/
def SenseInclusionControls : Prop :=
  (¬ NoInfinitePerSeEfficientCauseSeriesReading cyc ∧
    PerSeEsseLinkIsPerSeCauseLink (eff cyc) () allLinks cyc ∧
    ¬ NoInfinitePerSeEsseEfficientCauseSeries (eff cyc) () allLinks) ∧
  (NoInfinitePerSeEfficientCauseSeriesReading (noRel : Bool → Bool → Prop) ∧
    ¬ PerSeEsseLinkIsPerSeCauseLink (eff cyc) () allLinks noRel ∧
    ¬ NoInfinitePerSeEsseEfficientCauseSeries (eff cyc) () allLinks) ∧
  (NoInfinitePerSeEfficientCauseSeriesReading edgeTF ∧
    PerSeEsseLinkIsPerSeCauseLink (eff edgeTF) () allLinks edgeTF ∧
    NoInfinitePerSeEsseEfficientCauseSeries (eff edgeTF) () allLinks ∧
    CausesBeingAsCaused (eff edgeTF) () allLinks true false)

/-- Omissions and nonvacuity for the inclusion of SERIES_OF_CAUSES_4 into
SERIES_OF_CAUSES_3 from the secunda via's per se ordering premise (8a22ae75),
no self-causation (8b2561cd) and the premise that an existential link's cause is
itself efficiently caused: dropping each in turn (a two-cycle of efficient
causing with no per se link; an efficient self-loop; one existential link whose
cause nothing causes), and a nonvacuous interpretation. -/
def InclusionSupportControls : Prop :=
  (¬ SecondEfficientCausesCauseOnlyAsCausedReading (eff cyc) (noRel : Bool → Bool → Prop) ∧
    NothingIsEfficientCauseOfItselfReading (eff cyc) ∧
    ExistentialLinkCauseIsEfficientlyCaused (eff cyc) () allLinks ∧
    ¬ PerSeEsseLinkIsPerSeCauseLink (eff cyc) () allLinks noRel) ∧
  (SecondEfficientCausesCauseOnlyAsCausedReading (eff loopT) (noRel : Bool → Bool → Prop) ∧
    ¬ NothingIsEfficientCauseOfItselfReading (eff loopT) ∧
    ExistentialLinkCauseIsEfficientlyCaused (eff loopT) () allLinks ∧
    ¬ PerSeEsseLinkIsPerSeCauseLink (eff loopT) () allLinks noRel) ∧
  (SecondEfficientCausesCauseOnlyAsCausedReading (eff edgeTF) (noRel : Bool → Bool → Prop) ∧
    NothingIsEfficientCauseOfItselfReading (eff edgeTF) ∧
    ¬ ExistentialLinkCauseIsEfficientlyCaused (eff edgeTF) () allLinks ∧
    ¬ PerSeEsseLinkIsPerSeCauseLink (eff edgeTF) () allLinks noRel) ∧
  (SecondEfficientCausesCauseOnlyAsCausedReading (eff cyc) cyc ∧
    NothingIsEfficientCauseOfItselfReading (eff cyc) ∧
    ExistentialLinkCauseIsEfficientlyCaused (eff cyc) () allLinks ∧
    PerSeEsseLinkIsPerSeCauseLink (eff cyc) () allLinks cyc ∧
    CausesBeingAsCaused (eff cyc) () allLinks true false)

/-- Omissions and nonvacuity for the restated bridge from e8664ab8 and the
inclusion. -/
def OldBridgeControls : Prop :=
  (¬ PerSeEfficientCausesArePerSeEsseCauses pNone allLinks cyc ∧
    PerSeEsseLinkIsPerSeCauseLink (eff cyc) () allLinks cyc ∧
    ¬ PerSeEsseLinksArePerSeEsseCauses pNone (eff cyc) allLinks) ∧
  (PerSeEfficientCausesArePerSeEsseCauses pNone allLinks noRel ∧
    ¬ PerSeEsseLinkIsPerSeCauseLink (eff cyc) () allLinks noRel ∧
    ¬ PerSeEsseLinksArePerSeEsseCauses pNone (eff cyc) allLinks) ∧
  (PerSeEfficientCausesArePerSeEsseCauses pEdge allLinks edgeTF ∧
    PerSeEsseLinkIsPerSeCauseLink (eff edgeTF) () allLinks edgeTF ∧
    PerSeEsseLinksArePerSeEsseCauses pEdge (eff edgeTF) allLinks ∧
    CausesBeingAsCaused (eff edgeTF) pEdge.esse allLinks true false)

/-- The split limit, on `Nat` with two respects, being and motion (`q3Two`,
`effTwo`, `caaTwo`). The whole existential part of the one order holds
nonvacuously: actual grounding well-founded, the weak esse-ground bridge, the
two actuality calibrations, the esse regress and its per se version, the
restated bridge, the inclusion of SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3 and
the existential no-regress premise, with the single existential link `1 → 0`.
Efficient causing in the motion respect is the upward successor, each such link
is a per se efficient link (the secunda via's per se ordering premise 8a22ae75
holds), and the per se mover links are those motion links (c2880fe0 holds).
Yet the per se efficient series (97f5850f) and the per se mover series descend
for ever and e8664ab8 fails. -/
def SecundaSplitLimit : Prop :=
  ActualGroundingWF mNat () ∧
    ActualEsseCauseIsActualGround mNat () q3Two.CausesIn q3Two.esse ∧
    ActOfEsseSufficesForExistenceAt mNat.ontic q3Two.InAct q3Two.esse () ∧
    EsseInReIsConcrete mNat q3Two.InAct q3Two.esse ∧
    NoInfiniteActualEsseCauseRegress q3Two ∧
    NoInfinitePerSeActualEsseCauseRegress q3Two allNat ∧
    PerSeEsseLinksArePerSeEsseCauses q3Two effTwo allNat ∧
    PerSeEsseLinkIsPerSeCauseLink effTwo q3Two.esse allNat caaTwo ∧
    NoInfinitePerSeEsseEfficientCauseSeries effTwo q3Two.esse allNat ∧
    CausesBeingAsCaused effTwo q3Two.esse allNat 1 0 ∧
    SecondEfficientCausesCauseOnlyAsCausedReading effTwo caaTwo ∧
    PerSeMoverLinkIsPerSeCauseLinkReading succUp caaTwo ∧
    effTwo 2 1 false ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading caaTwo ∧
    ¬ NoInfinitePerSeMoverSeriesReading succUp ∧
    ¬ PerSeEfficientCausesArePerSeEsseCauses q3Two allNat caaTwo

/-- Omissions and nonvacuity for PRIOR_4 well-founded among actual concreta from
actual grounding. PRIOR_4 is asymmetric by definition, so the omissions use an
infinite ascent on `Nat` (`y` prior in being to `x` when `x < y`). -/
def PriorityInBeingControls : Prop :=
  (¬ ActualGroundingWF mLt () ∧ PriorInBeingAmongActualConcretaIsGround mLt () ltWithout ∧
    ¬ PriorityInBeingWFAmongActualConcreta mLt () ltWithout) ∧
  (ActualGroundingWF mNoneNat () ∧
    ¬ PriorInBeingAmongActualConcretaIsGround mNoneNat () ltWithout ∧
    ¬ PriorityInBeingWFAmongActualConcreta mNoneNat () ltWithout) ∧
  (ActualGroundingWF mEdge () ∧ PriorInBeingAmongActualConcretaIsGround mEdge () tfWithout ∧
    PriorityInBeingWFAmongActualConcreta mEdge () tfWithout ∧ PriorInBeing tfWithout true false)

/-- Omissions and nonvacuity for the PRIOR_4 bridge among actual concreta from
c4bb0481 (PRIOR_4 requires nonmutual dependence for being) and a8298fbd (an
actual concretum's distinct actual dependee grounds it). -/
def PriorityBridgeControls : Prop :=
  (¬ PriorityInBeingRequiresNonmutualDependence tfWithout (noRel : Bool → Bool → Prop) ∧
    ActualDistinctDependenceIsGrounding mNone () noRel ∧
    ¬ PriorInBeingAmongActualConcretaIsGround mNone () tfWithout) ∧
  (PriorityInBeingRequiresNonmutualDependence tfWithout dFT ∧
    ¬ ActualDistinctDependenceIsGrounding mNone () dFT ∧
    ¬ PriorInBeingAmongActualConcretaIsGround mNone () tfWithout) ∧
  (PriorityInBeingRequiresNonmutualDependence tfWithout dFT ∧
    ActualDistinctDependenceIsGrounding mEdge () dFT ∧
    PriorInBeingAmongActualConcretaIsGround mEdge () tfWithout ∧ PriorInBeing tfWithout true false)

/-- The priority limit, on `Bool`. The PRIOR_4 member of the order holds
nonvacuously (actual grounding well-founded with the edge `true → false`, the
PRIOR_4 bridge, PRIOR_4 well-founded among actual concreta and on the whole
carrier, with the PRIOR_4 pair `true → false`), and the inputs of the prima via
chain e229bb2c hold (every history edge is efficient causing, every efficient
cause is PRIOR_1 to its effect, e078f07b, nothing is prior to itself), while
PRIOR_1 (d85de8e1) and the causal predecessors (42890b45) are not well-founded,
86efed1a fails, and the PRIOR_4 reading of e078f07b's shape fails. So the PRIOR_4
member does not entail d85de8e1, 42890b45 or that reading. The PRIOR_1 pair
`false → true` is not PRIOR_4; the last conjunct, a second interpretation, has a
PRIOR_4 pair that is not PRIOR_1. Interpretation facts only. -/
def PriorityConsumerLimit : Prop :=
  (ActualGroundingWF mEdge () ∧ PriorInBeingAmongActualConcretaIsGround mEdge () tfWithout ∧
    PriorityInBeingWFAmongActualConcreta mEdge () tfWithout ∧
    WellFounded (PriorInBeing tfWithout) ∧ PriorInBeing tfWithout true false ∧
    HistoryEdgesAreEfficientCausings cyc (eff cyc) ∧
    EfficientCauseIsPriorToEffectReading (eff cyc) cyc ∧ NothingPriorToItselfReading cyc ∧
    ¬ SimplePriorityWellFounded cyc ∧ ¬ WellFoundedPredecessors cyc ∧
    ¬ SimplyPriorIsActualConcreteGround mEdge () cyc ∧
    ¬ EfficientCauseIsPriorToEffectReading (eff cyc) (PriorInBeing tfWithout) ∧
    cyc false true ∧ ¬ PriorInBeing tfWithout false true) ∧
  (PriorInBeing tfWithout true false ∧ ¬ (noRel : Bool → Bool → Prop) true false)

end TruthCore.Causality.DependenceOrderSenses
