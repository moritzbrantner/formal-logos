module

public import TruthCore.Causality.Frame
public import TruthCore.Causality.AxiarchicGuidance
public import TruthCore.Causality.PossibiliaContent
public import TruthCore.Explanation.PriorityOmission
public import TruthCore.Explanation.TruthmakerTheories

/-!
# Can effect-grounded modes explain the production of their own grounds?

Analyst formulations, attribution deferred. This is a diagnostic for the
source-of-differences premise in `AxiarchicFoundation`, not a derivation of its
containment-recognition premise. It separates three relations already present
in the corpus: the shared causality frame's exercise of giving being, the PSR
arena's fact-to-fact explanation, and bearer-to-fact truthmaking.

`Arena.explains` means an admitted reason why, without structural laws. The
first test explicitly restricts an interpretation of it to strict explanatory
priority at one world by adding asymmetry and transitivity. A mode/ranking fact
is relevant to the source's productive exercise; that exercise gives an effect
being; and the named OPEN bridge `GivingExercisePriorityAt` admits the exercise
fact as prior to that effect's existence fact. The effect's existence cannot
then explain the original mode/ranking fact in that SAME priority relation.
Neither efficient production alone nor a merely extensional relational
description supplies the bridge. Asymmetry of two distinct relations does not
imply asymmetry or acyclicity of their union.

The existing `PriorityOmission` theorem handles the same-relation cycle. The
new application retains the bridge from productive giving to fact priority.
It does not identify a produced stand-in item with a fact grounded in an
effect: relating this diagnostic to `NoMerelyProducedStandIn` requires that
further application. Ideas whose relevant content is effect-grounded face the
same conditional test as unapprehended modes. No apprehension predicate occurs
in the test.

The second test reuses `MakerNecessitation`, `WorldImmanent`, and fact/being
contingency: every world-immanent necessitating maker of a contingent fact is
itself contingent. The converse does not follow. A necessary fact can meet
these necessary conditions for truthmaking with either a necessary or a
contingent bearer; `RootClosure.necessaryFactAnyMaker` already
establishes that limit. None of these modal conditions supplies substantive
relevance or a productive realization of a possibility.

No principle says that every extrinsic distinction is grounded in actual
effects. Possibility, essence, and possible-recipient conditions can be prior
to actual products in an interpretation. Whether such a basis actually
individuates the relevant modes, ranks them, and contributes to productive
exercise remains an OPEN metaphysical application. The controls are finite
structural surrogates, not demonstrations of metaphysical coherence.
-/

@[expose] public section

namespace TruthCore.Causality.ImitabilityGrounding

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Explanation.TruthmakerTheories (Making)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

variable {W B T R F : Type}

/-- OPEN structural constraint for the selected fact-explanation relation at
`w`: an admitted strict explanatory priority never reverses. This is not
asserted of every explanation, efficient cause, or relation of reference. -/
def FactPriorityAsymmetricAt (A : Arena W B F) (w : W) : Prop :=
  ∀ p q, A.explains w p q → ¬ A.explains w q p

/-- OPEN composition in the SAME interpreted fact-explanation relation and
world. This is not a composition law for a union of causal and grounding
relations. -/
def FactPriorityTransitiveAt (A : Arena W B F) (w : W) : Prop :=
  ∀ p q r, A.explains w p q → A.explains w q r → A.explains w p r

/-- OPEN relevance of a selected mode/ranking fact to the selected productive
exercise fact. The mode's mathematical label, nonidentity, or relational
reference to an effect does not establish this explanatory edge. -/
def ModeExplainsProductionAt (A : Arena W B F) (w : W) (mode production : F) : Prop :=
  A.explains w mode production

/-- OPEN cross-vocabulary bridge: whenever this source gives an effect being
at `w,t`, the selected fact of its productive exercise is an admitted prior
explanation of that SAME effect's existence fact. `GivesAt` keeps the shared
frame's strict esse-giving meaning. A transitive action's having its terminus
in an effect does not itself prove this fact-priority bridge. No relationship
between the frame's other fields and the arena is added. -/
def GivingExercisePriorityAt (K : CausalityFrame W B T R) (A : Arena W B F)
    (w : W) (source : B) (production : F) (t : T) : Prop :=
  ∀ effect, K.GivesAt w source effect t → A.explains w production (A.exist effect)

/-- None of this source's effects of giving being at `w,t` has an existence
fact admitted as prior to the selected mode/ranking fact in the SAME
fact-explanation relation. This excludes that specific direction of grounding;
it does not exclude extrinsic distinctions or imply apprehension. -/
def NoEffectGroundedGivingAt (K : CausalityFrame W B T R) (A : Arena W B F)
    (w : W) (source : B) (mode : F) (t : T) : Prop :=
  ∀ effect, K.GivesAt w source effect t → ¬ A.explains w (A.exist effect) mode

/-- Every maker of this selected fact at `w` actually exists there and fails
to exist at some accessible world. This is individual `ContingentAt`, distinct
from the fact-level `PSRStrength.Contingent`. It does not assert that there is
a maker, and no particular actual effect is identified as the maker. -/
def EveryMakerContingentAt (A : Arena W B F) (M : Making W B F) (w : W) (fact : F) : Prop :=
  ∀ b, M w b fact → ContingentAt A.ontic w b

/-! ## A populated possibility-basis control

The two possible recipients have rigid identity in both worlds. At `false`
neither is actual; at the accessible world `true` both are actual. The same
source exists in both. Mode-specification facts and the base ranking are true
in both worlds and are explained by an explicit possibility-basis fact.
That fact is not an existence fact of either effect. It can be interpreted as
an essence condition or a condition on possible recipients; the model does
not decide its substantive relevance or whether it needs a bearer.

At `true` the ranking contributes to a productive-exercise fact, and the
exercise explains both actual effects. At `false` no productive exercise is
asserted. Thus prior ranking does not by itself produce anything. The
different reason-variation scenarios of `AxiarchicGuidance` are retained as
analytical scenarios, not silently identified with the two modal worlds.

The mode tokens are fact specifications, not asserted real constituents of
the source. `PossibiliaContent` already distinguishes a real plurality of
parts from the non-real plurality required by its simplicity argument; this
control does not supply a new account of non-real being.
-/
namespace AvailabilityControl

open TruthCore.Causality.AxiarchicGuidance
open TruthCore.Causality.AxiarchicGuidance.Control
  (Cand Scen w good goodTracking noCtrl)
open TruthCore.Explanation.PSRStrength (Access Coherent Factive Contingent Necessitating)
open TruthCore.Explanation.StoppingPoints (NecessaryFact)

/-- Beings: `0` is the source; `1,2` are the two candidate recipients. -/
abbrev Being := Fin 3

/-- Facts: `0` source existence, `1` possibility basis, `2,3` mode
specifications, `4` the base ranking c over d, `5` productive exercise,
`6,7` existence of the two effects. Fact identity is rigid across worlds. -/
abbrev Fact := Fin 8

def candidate : Cand → Being
  | .c => 1
  | .d => 2

def mode : Cand → Fact
  | .c => 2
  | .d => 3

def basis : Fact := 1
def ranking : Fact := 4
def production : Fact := 5

/-- The source persists; both effects exist exactly at the produced world. -/
def existsAt (v : Bool) (b : Being) : Prop := b = 0 ∨ v = true

/-- Giving is populated at `true`; it is absent at `false`. The frame's other
causal fields keep their own meanings and are not used to infer fact priority. -/
def frame : CausalityFrame Bool Being Unit Unit where
  history := {
    ontic := {
      frame := ⟨fun _ _ => True⟩
      ExistsAt := existsAt
      Causes := fun v c e => c = 0 ∧ e ≠ 0 ∧ v = true }
    IsAt := fun v b _ => existsAt v b
    now := () }
  GivesAt := fun v c e _ => c = 0 ∧ e ≠ 0 ∧ v = true
  CausesIn := fun c e _ => c = 0 ∧ e ≠ 0
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun e c => e ≠ 0 ∧ c = 0
  PriorSimply := fun c e => c = 0 ∧ e ≠ 0
  esse := ()

/-- Partial explanatory contributions, with their transitive consequences.
The possibility basis explains the modes and ranking before actual effects.
Only at the produced world do ranking and exercise explain effect-existence. -/
def priority (v : Bool) (p q : Fact) : Prop :=
  (p = basis ∧ (q = mode .c ∨ q = mode .d ∨ q = ranking)) ∨
  (v = true ∧ (p = basis ∨ p = ranking) ∧
    (q = production ∨ q = 6 ∨ q = 7)) ∨
  (v = true ∧ p = production ∧ (q = 6 ∨ q = 7))

def arena : Arena Bool Being Fact where
  ontic := frame.history.ontic
  holds := fun v f => f.val < 5 ∨ v = true
  exist := fun b => if b = 0 then 0 else if b = 1 then 6 else 7
  explains := priority
  conjunct := Eq

/-- The existing two-candidate favouring is realized on mode-specification
tokens. This adds no existence, grounding, or apprehension claim. -/
def modeRelation (s : Scen) (p q : Fact) : Prop :=
  ∃ x y, mode x = p ∧ mode y = q ∧ good s x y

/-- The same two modes and a determinate base ranking are available while
neither possible recipient is actual. The scenario-level guidance test is
reused unchanged. At the produced world the actual giving and all four
cycle-exclusion premises are jointly satisfied. Positive explanatory edges
are present even at the effect-absent world, so the absence control does not
work by emptying every relation. -/
def Certificate : Prop :=
  Coherent arena ∧ Factive arena ∧
  (∀ v, arena.ontic.ExistsAt v 0) ∧
  (∀ x, ¬ arena.ontic.ExistsAt false (candidate x)) ∧
  (∀ x, arena.ontic.ExistsAt true (candidate x)) ∧ Access arena false true ∧
  (∀ v x, arena.holds v (mode x)) ∧
  (∀ v, arena.holds v ranking ∧ NecessaryFact arena v ranking) ∧
  (∀ v x, arena.explains v basis (mode x)) ∧
  (∀ v, arena.explains v basis ranking) ∧
  Contingent arena true production ∧
  (∀ x, Contingent arena true (arena.exist (candidate x))) ∧
  ¬ Necessitating arena ∧
  mode .c ≠ mode .d ∧ good .base .c .d ∧
  (∀ s x y, good s x y ↔ InvImage (modeRelation s) mode x y) ∧
  (∀ s x, ¬ good s x x) ∧
  GuidedByOutweighed w good noCtrl goodTracking .base .fit .c .d ∧
  (∀ x, frame.GivesAt true 0 (candidate x) ()) ∧
  FactPriorityAsymmetricAt arena true ∧ FactPriorityTransitiveAt arena true ∧
  ModeExplainsProductionAt arena true ranking production ∧
  GivingExercisePriorityAt frame arena true 0 production () ∧
  NoEffectGroundedGivingAt frame arena true 0 ranking ()

end AvailabilityControl

/-! ## Populated omission controls for the mixed cycle

The finder was attempted on the frozen core Challenge and reported the
unsupported structure field `K.history.now : T`. These explicit finite
interpretations retain two distinct actual beings, a source giving an effect
being, and four true fact tokens. Each row omits exactly one of the four
advertised hypotheses and falsifies the conclusion. They do not claim the
omitted property is philosophically false or that its alternatives are
metaphysically possible.
-/
namespace CycleControl

open TruthCore.Explanation.PSRStrength (Coherent Factive)

/-- `0` source existence, `1` mode/ranking, `2` productive exercise,
`3` effect existence. -/
abbrev Fact := Fin 4

def mode : Fact := 1
def production : Fact := 2
def effect : Fact := 3

def frame : CausalityFrame Unit Bool Unit Unit where
  history := {
    ontic := {
      frame := ⟨fun _ _ => True⟩
      ExistsAt := fun _ _ => True
      Causes := fun _ c e => c = true ∧ e = false }
    IsAt := fun _ _ _ => True
    now := () }
  GivesAt := fun _ c e _ => c = true ∧ e = false
  CausesIn := fun c e _ => c = true ∧ e = false
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun e c => e = false ∧ c = true
  PriorSimply := fun c e => c = true ∧ e = false
  esse := ()

def arena (rel : Fact → Fact → Prop) : Arena Unit Bool Fact where
  ontic := frame.history.ontic
  holds := fun _ _ => True
  exist := fun b => if b then 0 else effect
  explains := fun _ => rel
  conjunct := Eq

/-- Transitive, but not asymmetric: every fact explains every fact. -/
def allPriority (_ _ : Fact) : Prop := True

/-- Asymmetric but nontransitive: mode → exercise → effect → mode. -/
def cycle (p q : Fact) : Prop :=
  (p = mode ∧ q = production) ∨ (p = production ∧ q = effect) ∨
    (p = effect ∧ q = mode)

/-- Exercise → effect → mode, including the transitive consequence.
The mode has no priority to the productive exercise. -/
def posteriorMode (p q : Fact) : Prop :=
  (p = production ∧ q = effect) ∨ (p = effect ∧ q = mode) ∨
    (p = production ∧ q = mode)

/-- Effect → mode → exercise, including the transitive consequence.
Giving being is still populated, but it does not supply exercise → effect
in this fact relation. This is the mixed-relation bridge omission. -/
def missingGivingBridge (p q : Fact) : Prop :=
  (p = effect ∧ q = mode) ∨ (p = mode ∧ q = production) ∨
    (p = effect ∧ q = production)

def OmitAsymmetry : Prop :=
  ¬ FactPriorityAsymmetricAt (arena allPriority) () ∧
  FactPriorityTransitiveAt (arena allPriority) () ∧
  ModeExplainsProductionAt (arena allPriority) () mode production ∧
  GivingExercisePriorityAt frame (arena allPriority) () true production () ∧
  ¬ NoEffectGroundedGivingAt frame (arena allPriority) () true mode ()

def OmitTransitivity : Prop :=
  FactPriorityAsymmetricAt (arena cycle) () ∧
  ¬ FactPriorityTransitiveAt (arena cycle) () ∧
  ModeExplainsProductionAt (arena cycle) () mode production ∧
  GivingExercisePriorityAt frame (arena cycle) () true production () ∧
  ¬ NoEffectGroundedGivingAt frame (arena cycle) () true mode ()

def OmitModeRelevance : Prop :=
  FactPriorityAsymmetricAt (arena posteriorMode) () ∧
  FactPriorityTransitiveAt (arena posteriorMode) () ∧
  ¬ ModeExplainsProductionAt (arena posteriorMode) () mode production ∧
  GivingExercisePriorityAt frame (arena posteriorMode) () true production () ∧
  ¬ NoEffectGroundedGivingAt frame (arena posteriorMode) () true mode ()

def OmitGivingBridge : Prop :=
  FactPriorityAsymmetricAt (arena missingGivingBridge) () ∧
  FactPriorityTransitiveAt (arena missingGivingBridge) () ∧
  ModeExplainsProductionAt (arena missingGivingBridge) () mode production ∧
  ¬ GivingExercisePriorityAt frame (arena missingGivingBridge) () true production () ∧
  ¬ NoEffectGroundedGivingAt frame (arena missingGivingBridge) () true mode ()

/-- Every omission retains actual giving, a coherent existence-fact map, and
factive fact explanations. Together with the separate availability control,
these certify nonvacuity and indispensability of the displayed four inputs
within this encoding, not a uniquely weakest metaphysical premise bundle. -/
def Certificate : Prop :=
  frame.GivesAt () true false () ∧
  (∀ rel, Coherent (arena rel) ∧ Factive (arena rel)) ∧
  OmitAsymmetry ∧ OmitTransitivity ∧ OmitModeRelevance ∧ OmitGivingBridge

end CycleControl

/-! ## Truthmaker necessity, contingency, and omitted premises

The finder was attempted on the frozen modal Challenge and reported the
unsupported structure field `A.exist : B → F`. These explicit controls keep
one source present in every world. A second bearer is the candidate maker;
its existence and the selected ranking/relational fact can vary separately.
In the immanence omission the nominated maker is absent everywhere, so its
necessitation condition holds vacuously; that artifact is the point of the
omission, not a proposed truthmaking theory. The positive row has an actual
contingent maker and a true contingent fact.

The final comparison uses the SAME necessary fact and arena for two making
policies. A contingent effect and the necessary source both meet soundness
and maker necessitation. This reuses `RootClosure.necessaryFactAnyMaker`:
modal necessitation does not select a relevant ground of a necessary fact.
-/
namespace MakerControl

open TruthCore.Explanation.PSRStrength (Access Coherent Contingent)
open TruthCore.Explanation.TruthmakerTheories
  (Sound WorldImmanent MakerNecessitation NeedsMakerAt)
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- `0` source existence, `1` selected mode/ranking or relational fact,
`2` existence of the second bearer. -/
abbrev Fact := Fin 3

def selected : Fact := 1

/-- The source `true` exists everywhere. `present` controls the second
bearer's existence; `rankTrue` controls the selected fact. Actual causal edges
from the source to the second bearer are populated where it exists, but are
not inferred from making and are unused by the modal theorem. -/
def mk (present rankTrue : Bool → Prop) : Arena Bool Bool Fact where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun v b => b = true ∨ (b = false ∧ present v)
    Causes := fun v c e => c = true ∧ e = false ∧ present v }
  holds := fun v f => if f = 0 then True else if f = selected then rankTrue v else present v
  exist := fun b => if b then 0 else 2
  explains := fun _ _ _ => False
  conjunct := Eq

def contingentArena : Arena Bool Bool Fact :=
  mk (fun v => v = true) (fun v => v = true)

def absentMakerArena : Arena Bool Bool Fact :=
  mk (fun _ => False) (fun v => v = true)

def necessaryBearerArena : Arena Bool Bool Fact :=
  mk (fun _ => True) (fun v => v = true)

def everywhereArena : Arena Bool Bool Fact :=
  mk (fun _ => True) (fun _ => True)

def necessaryTruthArena : Arena Bool Bool Fact :=
  mk (fun v => v = true) (fun _ => True)

/-- The second bearer is the selected fact's nominated maker at `true`. -/
def making : Making Bool Bool Fact :=
  fun v b f => v = true ∧ b = false ∧ f = selected

/-- The source is the same fact's nominated maker at `true`. -/
def sourceMaking : Making Bool Bool Fact :=
  fun v b f => v = true ∧ b = true ∧ f = selected

def Positive : Prop :=
  WorldImmanent contingentArena making ∧ MakerNecessitation contingentArena making ∧
  Contingent contingentArena true selected ∧ making true false selected ∧
  EveryMakerContingentAt contingentArena making true selected

def OmitImmanence : Prop :=
  ¬ WorldImmanent absentMakerArena making ∧ MakerNecessitation absentMakerArena making ∧
  Contingent absentMakerArena true selected ∧
  ¬ EveryMakerContingentAt absentMakerArena making true selected

def OmitNecessitation : Prop :=
  WorldImmanent necessaryBearerArena making ∧
  ¬ MakerNecessitation necessaryBearerArena making ∧
  Contingent necessaryBearerArena true selected ∧
  ¬ EveryMakerContingentAt necessaryBearerArena making true selected

def OmitFactContingency : Prop :=
  WorldImmanent everywhereArena making ∧ MakerNecessitation everywhereArena making ∧
  ¬ Contingent everywhereArena true selected ∧
  ¬ EveryMakerContingentAt everywhereArena making true selected

/-- Same necessary fact and modal arena, one contingent and one necessary
candidate maker; both making policies meet these necessary modal constraints.
The policies' substantive relevance is not established. -/
def NecessaryFactAlternatives : Prop :=
  NecessaryFact necessaryTruthArena true selected ∧
  ContingentAt necessaryTruthArena.ontic true false ∧
  NecessaryAt necessaryTruthArena.ontic true true ∧
  (Sound necessaryTruthArena making ∧
    NeedsMakerAt necessaryTruthArena making true selected ∧
    MakerNecessitation necessaryTruthArena making) ∧
  (Sound necessaryTruthArena sourceMaking ∧
    NeedsMakerAt necessaryTruthArena sourceMaking true selected ∧
    MakerNecessitation necessaryTruthArena sourceMaking)

def Certificate : Prop :=
  (∀ present rankTrue, Coherent (mk present rankTrue) ∧
    ∀ v, (mk present rankTrue).ontic.ExistsAt v true) ∧
  Positive ∧ OmitImmanence ∧ OmitNecessitation ∧ OmitFactContingency ∧ NecessaryFactAlternatives

end MakerControl

end TruthCore.Causality.ImitabilityGrounding
