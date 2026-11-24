module

public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.CreatureSenses
public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
public import TruthCore.Causality.ActPriorityAtFirst
public import TruthCore.Causality.ComponentFirstness
public import TruthCore.Causality.ConcurrentCessation

/-! Esse-cause priority through actual grounding, without modal separability (#1604)

Analyst formulations, attribution deferred. The root route's only registered
derivation of `STMT-EFFICIENT-CAUSE-IS-PRIOR-TO-EFFECT` runs through
`STMT-NONMUTUAL-DEPENDENCE-SUFFICES-FOR-PRIORITY`, whose only derivation takes
the modal separability premise `STMT-INDEPENDENCE-ALLOWS-BEING-WITHOUT`
(see `docs/notes/god-existence-support-formula.md`). This module gives a
sibling path to priority for a **distinct cause of esse**, through the profile's
selected grounding relation, using neither `DependsForBeing` nor any
possible-separation premise:

* `ActualEsseCausePriority`: a distinct cause of the esse of an actual
  concretum at `w` is simply prior to it. It is the composition of the two
  existing OPEN bridges `EsseCauseIsActualConcreteGround` (causing the esse of
  an actual concretum is being its actual concrete ground) and
  `ActualGroundingIsSimplePriority` (actual grounding is simple priority).
* `DistinctEsseCausePriority`: the same with no actuality antecedent. The
  existing consumers of efficient-cause priority on the stage-two routes
  (`noComponentFirst`, `firstBeingNoPotencyOfComposition` and their weak
  versions) apply it only to a distinct cause of the esse of a supposed first
  being, with no profile and no actuality hypothesis. Three existing OPEN
  statements supply that antecedent: a caused esse is had
  (`CreatureSenses.CausedEsseIsHad`), what is in act of esse exists at `w`
  (`Round2ExistenceAct.ActOfEsseSufficesForExistenceAt`) and what has esse in
  re is concrete in the profile (`CauseOfBeingHasBeing.EsseInReIsConcrete`).

`CausesIn` is the one shared cause-of-perfection relation (DEF-CAUSE-OF-
PERFECTION) at `esse`, the relation of the q.3 a.7 cause premise; no premise
passes to efficient causing. `PriorSimply` is the primitive SIMPLY_PRIOR_1.
`DistinctEsseCausePriority` is strictly weaker than
`EfficientCauseIsPriorToEffectReading` read on the same relation: it says
nothing about self-causes or about respects other than esse
(`Control.NotEfficientPriority`). It therefore cannot serve the consumers that
need those instances (no self-cause, causal well-foundedness, the secunda via).
-/

@[expose] public section

namespace TruthCore.Causality.EsseCausePriority

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)

variable {W B R : Type}

/-- A distinct cause of the esse of an actual concretum at `w` is simply prior
to it. Scoped to actual concreta at one world and to the respect `esse`. -/
def ActualEsseCausePriority (m : Profile W B) (w : W) (CausesIn : B → B → R → Prop)
    (esse : R) (PriorSimply : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → ActualConcrete m w x → CausesIn c x esse → PriorSimply c x

/-- A distinct cause of a thing's esse is simply prior to it. No self-cause and
no respect other than esse is covered. -/
def DistinctEsseCausePriority (CausesIn : B → B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse → PriorSimply c x

/-! ## Controls

Finite interpretations with `Bool` worlds, beings and respects (the reading
world and `esse` are `true`), built with `Round2Grounding.Control.mk`.
Satisfiability and omission only; no model is claimed to describe reality. -/

namespace Control

open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority)
open TruthCore.Causality.CreatureSenses (CausedEsseIsHad)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Latin.Aquinas.SummaTheologiae (EfficientCauseIsPriorToEffectReading)

/-- Everything exists everywhere and is concrete; nothing is grounded. -/
abbrev bare : Profile Bool Bool :=
  Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => True) (fun _ => True)
    (fun _ _ _ => False) (fun _ _ _ => False)
/-- As `bare`, but `true` grounds `false` at `true`. -/
abbrev grounded : Profile Bool Bool :=
  Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => True) (fun _ => True)
    (fun _ _ _ => False) (fun w g x => w = true ∧ g = true ∧ x = false)
/-- `true` causes the esse of `false`. -/
abbrev causes (c x r : Bool) : Prop := c = true ∧ x = false ∧ r = true
/-- `true` is simply prior to `false`. -/
abbrev prior (y x : Bool) : Prop := y = true ∧ x = false
/-- Nothing is simply prior to anything. -/
abbrev noPrior (_ _ : Bool) : Prop := False
/-- Everything is in act in every respect. -/
abbrev allAct (_ _ : Bool) : Prop := True

/-- Joint witness: both bridges hold with a nonvacuous instance (an actual
concretum `false` whose esse `true` causes), and the conclusion's instance holds. -/
def Witness : Prop :=
  EsseCauseIsActualConcreteGround grounded true causes true ∧
  ActualGroundingIsSimplePriority grounded true prior ∧
  ActualConcrete grounded true false ∧ causes true false true ∧ prior true false

/-- Omitting the esse-cause bridge: actual grounding is simple priority (vacuously:
nothing grounds), an actual concretum has a distinct esse cause, and the
scoped priority fails. -/
def OmitEsseGround : Prop :=
  ActualGroundingIsSimplePriority bare true noPrior ∧
  ¬ ActualEsseCausePriority bare true causes true noPrior

/-- Omitting the grounding-to-priority bridge: the esse cause grounds its actual
effect, nothing is simply prior, and the scoped priority fails. -/
def OmitGroundingPriority : Prop :=
  EsseCauseIsActualConcreteGround grounded true causes true ∧
  ¬ ActualEsseCausePriority grounded true causes true noPrior

/-- The three antecedent-supplying bridges and both priority bridges hold jointly
for the relation `causes`, under which `true` causes the esse of `false` (this
proposition does not itself state that instance). -/
def ScopeWitness : Prop :=
  CausedEsseIsHad causes allAct true ∧
  ActOfEsseSufficesForExistenceAt grounded.ontic allAct true true ∧
  EsseInReIsConcrete grounded allAct true ∧
  EsseCauseIsActualConcreteGround grounded true causes true ∧
  ActualGroundingIsSimplePriority grounded true prior

/-- Omitting `CausedEsseIsHad`: nothing is in act, nothing exists, so the scoped
priority holds vacuously, the other two scope bridges hold, a distinct esse cause
exists, and the unscoped priority fails. -/
def OmitCausedEsseIsHad : Prop :=
  ActualEsseCausePriority
    (Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ => False) (fun _ _ _ => False)) true causes true noPrior ∧
  ActOfEsseSufficesForExistenceAt
    (Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ => False) (fun _ _ _ => False)).ontic (fun _ _ => False) true true ∧
  EsseInReIsConcrete
    (Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ => False) (fun _ _ _ => False)) (fun _ _ => False) true ∧
  ¬ DistinctEsseCausePriority causes true noPrior

/-- The distinct-esse-cause version does not give efficient-cause priority on
the same relation: `true` causes its own esse and is not prior to itself, while
the distinct-cause version holds vacuously. -/
def NotEfficientPriority : Prop :=
  DistinctEsseCausePriority (fun c x r => c = true ∧ x = true ∧ r = true) true noPrior ∧
  ¬ EfficientCauseIsPriorToEffectReading (fun c x r => c = true ∧ x = true ∧ r = true) noPrior

/-- The controls of this module. -/
def Certificate : Prop :=
  Witness ∧ OmitEsseGround ∧ OmitGroundingPriority ∧ ScopeWitness ∧
  OmitCausedEsseIsHad ∧ NotEfficientPriority

end Control


/-!
## C3 omission against the complete #1614 source-premise bundle

This continues #1616 and #1801 *without introducing a separate causality
ontology*. The temporally originating `GivesAt` and primitive `CausesIn`
reuse the C3ActualWorld control. The new feature is that the originator is
**de re necessary** while the rigid effect is contingent and persists without
concurrent giving. The selected actual ground/priority edges are alternatively
interpreted as historical ancestry or withheld as present-existential ground.

`SourcePremises` is only a convenience grouping of the ten existing OPEN
source-level premises used in PR #1614's five-argument esse-priority cluster.
The two intermediate premises `ActualEsseCausePriority` and
`FirstBeingActPriority` are *conclusions*, not silently supplied inputs.
This is a structural joint-interpretation test, not proof of metaphysical
applicability. On the ancestry reading, `ActualConcreteGround` does not imply
productive `GivesAt`. On the strict present-ground reading, an inertialist
rejects the bridge rather than the other source premises.

**What the strict branch withholds.** The strict branch (`withoutGround`
with `strictFrame`) withholds BOTH the grounding edge and the priority edge
(`PriorSimply := Control.noPrior`, empty). Among the ten source premises plus
`cb1cdea9`, `cb1cdea9` is the only premise that forces any priority edge
(through `ActualGroundingIsSimplePriority`, whose grounding clause is then
vacuous). The priority and first-being/component failures in
`FullSourceOmission` are produced by the separate choice of an empty
`PriorSimply`, not by denying `cb1cdea9`: `PriorityWithoutGroundEdge` keeps
the same `withoutGround` profile with `Control.prior`, and there the ten
premises and all priority conclusions hold. Under an empty priority every
being is vacuously first, so the first-being failures are witnessed at the
caused, composite, contingent effect `false`. Denying origin priority is an
extra interpretive commitment; DEF-SIMPLE-PRIORITY's "not in time" does not
settle it.

**Inherited component relation.** `component` reuses
`ComponentFirstness.Control.comp` (`p = false ∧ x = true`): the received
effect `false` counts as a component of its own necessary originator `true`,
while `composite` holds only of `false`. With two Boolean beings, only a third
being would avoid this assignment; it is a structural artifact, not a claim
that the originator is composed of its effect.

**Equivocation guard.** In `withoutGround`, `EveryContingentGroundedAt` fails:
`false` is a contingent actual root with no ground. The ancestry profile alone
satisfies the root premises. Using ancestry `grounds` for the root premises
and strict `grounds` for `cb1cdea9` would equivocate.
-/

namespace InertialNecessaryOrigin

open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteRouteBridge (NecessaryActualRootAt
  EsseCauseIsActualConcreteGround)
open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.ConcurrentCessation
open TruthCore.Causality.ConcurrentCessation.C3ActualWorld
open TruthCore.Causality.SustainingCausation (OriginatesBeing GiverPresentWhenGiving)
open TruthCore.Causality.ConcurrentActualization
  (ConcurrentlyActualized CausingAnothersBeingIsSustaining)
open TruthCore.Causality.ActPriorityAtFirst
  (FirstBeingIsInSomeAct ActAndPotencyMakeComposite FirstBeingActPriority)
open TruthCore.Causality.ComponentFirstness (ComponentIsPotentialOrParticipated)
open TruthCore.Causality.Round2Grounding
  (ActualGroundingIsSimplePriority ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.CreatureSenses (CausedEsseIsHad)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (CompositeHasAUnitingCauseReading NotActAndPotencyInSameRespectReading
   FirstBeingIsInNoWayInPotencyReading NoComponentIsFirstBeingReading)

/-- The originating bearer is present in both accessible worlds. Its effect
is present only at the selected world and only from t=1 onward. World
existence agrees with temporal presence at now=2 in *both* worlds. -/
def history : History Bool Bool Nat :=
  { C3ActualWorld.history with
    ontic := { C3ActualWorld.history.ontic with
      ExistsAt := fun v x => x = true ∨ v = true }
    IsAt := fun v x t => x = true ∨ (v = true ∧ x = false ∧ 1 ≤ t) }

/-- Reuse the old actual `grounds` edge as historical causal ancestry:
the necessary originator is an actual ground of the contingent recipient,
even though it does not give at t=2. This is not a productive-ground reading. -/
def ancestral : Profile Bool Bool :=
  { C3ActualWorld.withGround with ontic := history.ontic }

/-- Same ontology and actual causal history, with the selected *present*
existential-ground edge absent. An origin can still explain the history. -/
def withoutGround : Profile Bool Bool :=
  { ancestral with grounds := fun _ _ _ => False }

/-- Reuse the same `CausesIn c x esse` relation; only add a second (heat)
respect to make compositional potency nonvacuously distinct from actuality
as to esse. `CausesIn` itself remains tenseless and mode-unspecified. -/
def causes (c x r : Bool) : Prop :=
  r = true ∧ C3ActualWorld.originFrame.CausesIn c x
    C3ActualWorld.originFrame.esse

/-- The same shared causal frame. `PriorSimply` is a chosen metaphysical
order; it is not automatically the time order or an originator relation. -/
def frame (priority : Bool → Bool → Prop) : CausalityFrame Bool Bool Nat Bool where
  history := history
  GivesAt := C3ActualWorld.originGiving.GivesAt
  CausesIn := causes
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun _ _ => False
  PriorSimply := priority
  esse := true

def ancestralFrame : CausalityFrame Bool Bool Nat Bool :=
  frame Control.prior
def strictFrame : CausalityFrame Bool Bool Nat Bool :=
  frame Control.noPrior

-- Reuse the existing two-respect act/potency and component witnesses.
abbrev act : Bool → Bool → Prop := ActPriorityAtFirst.Control.esseAct
abbrev potency : Bool → Bool → Prop := ActPriorityAtFirst.Control.stonePotency
abbrev composite : Bool → Prop := ActPriorityAtFirst.Control.stoneComposite
abbrev component : Bool → Bool → Prop := ComponentFirstness.Control.comp
abbrev participated : Bool → Prop := ComponentFirstness.Control.isFalse

/-- Exactly the ten other source premises of PR #1614's esse-priority
cluster, each with its existing type and same respect/being dictionaries.
The statements are OPEN: their joint satisfiability does not establish them.
`FirstBeingActPriority`, `ActualEsseCausePriority` and
`DistinctEsseCausePriority` are derived nodes, not included in this list. -/
def SourcePremises (m : Profile Bool Bool)
    (F : CausalityFrame Bool Bool Nat Bool) : Prop :=
  ActualGroundingIsSimplePriority m true F.PriorSimply ∧
  CausedEsseIsHad F.CausesIn act F.esse ∧
  ActOfEsseSufficesForExistenceAt m.ontic act F.esse true ∧
  EsseInReIsConcrete m act F.esse ∧
  FirstBeingIsInSomeAct act F.PriorSimply ∧
  ActAndPotencyMakeComposite act potency composite ∧
  CompositeHasAUnitingCauseReading composite F.CausesIn F.esse ∧
  ComponentIsPotentialOrParticipated component potency participated ∧
  NotActAndPotencyInSameRespectReading act potency ∧
  ParticipatedEsseHasDistinctCause participated F.CausesIn F.esse

/-- A necessary, actually ungrounded source, a contingent effect grounded in
the source on the ancestry reading, and explicit origin-only persistence.
This combines the #1885 same-bearer model with the existing necessary-root
consumer; it is not a modal source-selection or metaphysical truth theorem. -/
def NecessaryOriginWithoutConservation : Prop :=
  CoherentAtNow history ∧
  C3ActualWorld.StepPersistence history ∧
  NecessaryActualRootAt ancestral true ∧
  EveryContingentGroundedAt ancestral true ∧
  ContingentAt history.ontic true false ∧
  OriginatesBeing history C3ActualWorld.originGiving true true false ∧
  GiverPresentWhenGiving history C3ActualWorld.originGiving ∧
  ¬ ConcurrentlyActualized history C3ActualWorld.originGiving
    ConcurrentActualization.Control.falseReceived ∧
  ¬ CausingAnothersBeingIsSustaining history C3ActualWorld.originGiving
    ancestralFrame.CausesIn ancestralFrame.esse

/-- All ten remaining #1614 source premises hold for an actual, temporally
persistent, modally contingent effect and a necessary originator; the
grounding clause `ActualGroundingIsSimplePriority` holds VACUOUSLY because
there is no grounding edge. The strict branch withholds both the grounding
edge (so `cb1cdea9` fails at cause `true`, effect `false`) and the priority
edge (`PriorSimply` empty). The two priority conclusions fail at the pair
`true`, `false`; the first-being act-priority and no-potency failures are
witnessed at `false`, and no-component-first at component `false` of `true`,
only because nothing is prior to anything, so every being, including the
caused composite contingent `false`, is vacuously first. These failures come
from the empty `PriorSimply`, not from denying `cb1cdea9`: see
`PriorityWithoutGroundEdge`. Derived premises are not assumed. -/
def FullSourceOmission : Prop :=
  SourcePremises withoutGround strictFrame ∧
  ¬ EsseCauseIsActualConcreteGround withoutGround true
    strictFrame.CausesIn strictFrame.esse ∧
  ¬ ActualEsseCausePriority withoutGround true strictFrame.CausesIn
    strictFrame.esse strictFrame.PriorSimply ∧
  ¬ DistinctEsseCausePriority strictFrame.CausesIn
    strictFrame.esse strictFrame.PriorSimply ∧
  ¬ FirstBeingActPriority act potency strictFrame.PriorSimply ∧
  ¬ FirstBeingIsInNoWayInPotencyReading potency strictFrame.PriorSimply ∧
  ¬ NoComponentIsFirstBeingReading component strictFrame.PriorSimply

/-- Attribution control for `FullSourceOmission`: the SAME `withoutGround`
profile (no grounding edge, `cb1cdea9` false) but with the ancestry priority
`Control.prior` retained. The ten source premises still hold (the grounding
clause vacuously; the other nine never mention priority), and both priority
conclusions and all first-being/component consequences HOLD. Denying
`cb1cdea9` alone therefore removes none of them; their failure in the strict
branch is due to the separate choice `PriorSimply := ∅`. -/
def PriorityWithoutGroundEdge : Prop :=
  SourcePremises withoutGround ancestralFrame ∧
  ¬ EsseCauseIsActualConcreteGround withoutGround true
    ancestralFrame.CausesIn ancestralFrame.esse ∧
  ActualEsseCausePriority withoutGround true ancestralFrame.CausesIn
    ancestralFrame.esse ancestralFrame.PriorSimply ∧
  DistinctEsseCausePriority ancestralFrame.CausesIn
    ancestralFrame.esse ancestralFrame.PriorSimply ∧
  FirstBeingActPriority act potency ancestralFrame.PriorSimply ∧
  FirstBeingIsInNoWayInPotencyReading potency ancestralFrame.PriorSimply ∧
  NoComponentIsFirstBeingReading component ancestralFrame.PriorSimply

/-- On the *different*, historical-ancestry interpretation of the selected
ground/priority relations, the entire source bundle including `cb1cdea9`
and both priority conclusions can hold, but C3 still fails. This is not
a productive simultaneous grounding interpretation. -/
def AncestorRouteWithoutConservation : Prop :=
  SourcePremises ancestral ancestralFrame ∧
  EsseCauseIsActualConcreteGround ancestral true
    ancestralFrame.CausesIn ancestralFrame.esse ∧
  ActualEsseCausePriority ancestral true ancestralFrame.CausesIn
    ancestralFrame.esse ancestralFrame.PriorSimply ∧
  DistinctEsseCausePriority ancestralFrame.CausesIn
    ancestralFrame.esse ancestralFrame.PriorSimply ∧
  FirstBeingIsInNoWayInPotencyReading potency ancestralFrame.PriorSimply ∧
  NoComponentIsFirstBeingReading component ancestralFrame.PriorSimply ∧
  ¬ ConcurrentlyActualized history C3ActualWorld.originGiving
    ConcurrentActualization.Control.falseReceived

end InertialNecessaryOrigin

end TruthCore.Causality.EsseCausePriority
