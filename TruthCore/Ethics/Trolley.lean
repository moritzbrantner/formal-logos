module

public import Mathlib.Logic.Relation

/-! Typed trolley case frame (analyst formulation; attribution deferred).

Four scenarios (switch, footbridge, transplant and Thomson's loop) are each
described by a finite causal graph over five event kinds, the death counts of
intervening and refraining, the events the agent's plan includes, and a supplied
classification of the chosen act's object. Rival principles are definitions over
that description, so every verdict below is computed from the case structure and
could fail on a different description. Nothing here asserts that any principle is
true, that the descriptions are psychologically or causally realistic, or that a
verdict is correct. `Relation.ReflTransGen` (Mathlib) supplies causal paths.

Senses (see the corpus disambiguations):
* KILLS_1 `KillsCausally`: the intervention starts a causal path to the one's
  lethal harm; diverting counts as killing, as in ordinary use. KILLS_2
  `KillsByNewThreat` is a stipulated technical relation, not ordinary killing:
  that path does not run through the redirection of the threat already facing
  the five (the agent introduces a new threat).
* MEANS_1 `HarmIsCausalMeans`: every causal path from the intervention to the
  saving of the five passes through the one's harm. MEANS_2
  `HarmIsPlannedMeans`: the plan includes the harm and some causal path leads
  from the harm to the saving. MEANS_2 does not entail MEANS_1.
* INTENDS_1 `PlansHarm`: the agent's plan includes the harm (as end or means).
  The plan is a supplied case fact, not derived from the graph. INTENDS_2
  `IntendsHarmAsKnownMeans`: whatever is known to be a necessary causal means to
  the chosen end is intended; on this reading it coincides with MEANS_1.
Permissibility is a supplied assignment `P : Scenario → Prop` for intervening;
a principle governs it when it fixes `P` scenario by scenario.

Condition 1 of double effect (`objectNotEvil`) is a supplied classification, true
in all four scenario descriptions; only control (11) varies it. The frame does
not separate footbridge from transplant (the same `Case`), and has no separate
impact and death events, so plan inclusion of the harm is a stipulation.
-/

@[expose] public section

namespace TruthCore.Ethics.Trolley

inductive Scenario | switch | footbridge | transplant | loop
  deriving DecidableEq

/-- Event kinds: the agent's intervention, the redirection of the threat away
from the five, the one's lethal harm, the ending of the threat to the five, and
the survival of the five. -/
inductive Event | act | redirect | harmOne | stopThreat | saveFive
  deriving DecidableEq

/-- What happens if the agent intervenes (causal links), the death counts of
intervening and of refraining, the events the agent's plan includes, and the
supplied classification that the chosen act is not evil by its object
(condition 1 of double effect; not derived here). -/
structure Case where
  edge : Event → Event → Bool
  deathsIfIntervene : Nat
  deathsIfRefrain : Nat
  plan : Event → Bool
  objectNotEvil : Bool

/-- A direct causal link in the intervention scenario. -/
def Step (c : Case) (x y : Event) : Prop := c.edge x y = true

/-- A direct causal link whose effect is not the avoided event. -/
def StepAvoiding (c : Case) (h x y : Event) : Prop := c.edge x y = true ∧ y ≠ h

/-- A causal path (possibly empty). -/
def Reach (c : Case) (a b : Event) : Prop := Relation.ReflTransGen (Step c) a b

/-- A causal path that never enters the avoided event. -/
def ReachAvoiding (c : Case) (h a b : Event) : Prop :=
  Relation.ReflTransGen (StepAvoiding c h) a b

/-- KILLS_1: the intervention causally leads to the one's lethal harm. -/
def KillsCausally (c : Case) : Prop := Reach c .act .harmOne

/-- KILLS_2: the intervention leads to the one's harm by a path that does not
pass through the redirection of the existing threat (a new threat is created). -/
def KillsByNewThreat (c : Case) : Prop := ReachAvoiding c .redirect .act .harmOne

/-- MEANS_1: the intervention saves the five, and only through the one's harm. -/
def HarmIsCausalMeans (c : Case) : Prop :=
  Reach c .act .saveFive ∧ ¬ ReachAvoiding c .harmOne .act .saveFive

/-- INTENDS_1: the agent's plan includes the one's harm. -/
def PlansHarm (c : Case) : Prop := c.plan .harmOne = true

/-- INTENDS_2 (known-necessary-means reading): an agent who chooses the act for
the saving intends whatever it knows to be a necessary causal means to it, so the
harm counts as intended exactly when it is a MEANS_1. The identification is this
sense's explicit content, not a theorem about intention. -/
def IntendsHarmAsKnownMeans (c : Case) : Prop := HarmIsCausalMeans c

/-- MEANS_2: the harm is planned and contributes causally to the saving. -/
def HarmIsPlannedMeans (c : Case) : Prop := PlansHarm c ∧ Reach c .harmOne .saveFive

/-- Proportionality: intervening costs strictly fewer lives than refraining. -/
def Proportionate (c : Case) : Prop := c.deathsIfIntervene < c.deathsIfRefrain

instance (c : Case) : Decidable (PlansHarm c) := inferInstanceAs (Decidable (_ = _))
instance (c : Case) : Decidable (Proportionate c) := inferInstanceAs (Decidable (_ < _))

/-! ### Principles: when is intervening permissible? -/

/-- Lives-only act consequentialism: intervening is permissible iff it costs no more
lives than refraining. -/
def ActConsequentialist (c : Case) : Prop := c.deathsIfIntervene ≤ c.deathsIfRefrain

instance (c : Case) : Decidable (ActConsequentialist c) := inferInstanceAs (Decidable (_ ≤ _))

/-- Absolute no-killing deontology with KILLS_1. -/
def CausalNoKilling (c : Case) : Prop := ¬ KillsCausally c

/-- Double effect, causal reading of condition 3: object not evil; harm not
intended (INTENDS_1); harm not a means in MEANS_1; proportionate reason. Neither
this nor the intention reading below is privileged as "the" classical doctrine. -/
def DoubleEffect (c : Case) : Prop :=
  c.objectNotEvil = true ∧ ¬ PlansHarm c ∧ ¬ HarmIsCausalMeans c ∧ Proportionate c

/-- Double effect, intention reading of condition 3: the harm is not a planned
means (MEANS_2). On this reading condition 3 is implied by condition 2. -/
def IntentionDoubleEffect (c : Case) : Prop :=
  c.objectNotEvil = true ∧ ¬ PlansHarm c ∧ ¬ HarmIsPlannedMeans c ∧ Proportionate c

/-- Causal means principle, one Kantian-inspired reading: no harm as a MEANS_1,
and the rescue is proportionate. It omits the formula of humanity's reference to
maxims, using someone merely as a means, and consent. -/
def MeansPrinciple (c : Case) : Prop := ¬ HarmIsCausalMeans c ∧ Proportionate c

/-- Thomson-style redirection principle: the harm may come only downstream of
redirecting the existing threat (no KILLS_2), and the rescue is proportionate.
Kamm's Principle of Permissible Harm is a different, more detailed principle. -/
def Redirection (c : Case) : Prop := ¬ KillsByNewThreat c ∧ Proportionate c

/-! ### Concrete case descriptions -/

def switchCase : Case where
  edge
    | .act, .redirect => true
    | .redirect, .harmOne => true
    | .redirect, .saveFive => true
    | _, _ => false
  deathsIfIntervene := 1
  deathsIfRefrain := 5
  plan
    | .harmOne => false
    | .stopThreat => false
    | _ => true
  objectNotEvil := true

/-- Pushing: the push puts the bystander in the trolley's path, his lethal impact
stops the trolley, which saves the five. -/
def footbridgeCase : Case where
  edge
    | .act, .harmOne => true
    | .harmOne, .stopThreat => true
    | .stopThreat, .saveFive => true
    | _, _ => false
  deathsIfIntervene := 1
  deathsIfRefrain := 5
  plan
    | .redirect => false
    | _ => true
  objectNotEvil := true

/-- Harvesting: the lethal removal of the organs supplies the transplants that end
the five's organ failure. There is no threat to redirect. -/
def transplantCase : Case where
  edge
    | .act, .harmOne => true
    | .harmOne, .stopThreat => true
    | .stopThreat, .saveFive => true
    | _, _ => false
  deathsIfIntervene := 1
  deathsIfRefrain := 5
  plan
    | .redirect => false
    | _ => true
  objectNotEvil := true

/-- Thomson's loop: the side track rejoins the main line; the diverted trolley is
stopped only by hitting the one, so redirection alone does not save the five. The
plan (Kamm's "because of", not "in order to") includes redirection and the
stopping but not the harm. -/
def loopCase : Case where
  edge
    | .act, .redirect => true
    | .redirect, .harmOne => true
    | .harmOne, .stopThreat => true
    | .stopThreat, .saveFive => true
    | _, _ => false
  deathsIfIntervene := 1
  deathsIfRefrain := 5
  plan
    | .harmOne => false
    | _ => true
  objectNotEvil := true

/-! ### Variants used only by the controls -/

/-- Footbridge structure with a plan that omits the harm. This models the
closeness problem: the agent is said to intend only the impact, and the frame,
having no separate impact event, then leaves `harmOne` out of the plan. -/
def footbridgeNarrowPlan : Case := { footbridgeCase with plan := fun e => e != .harmOne && e != .redirect }

/-- Side-effect footbridge: a dropped weight stops the trolley and its fall also
knocks the bystander lethally; his harm is not on the rescue path. -/
def sideEffectFootbridge : Case where
  edge
    | .act, .stopThreat => true
    | .act, .harmOne => true
    | .stopThreat, .saveFive => true
    | _, _ => false
  deathsIfIntervene := 1
  deathsIfRefrain := 5
  plan
    | .harmOne => false
    | .redirect => false
    | _ => true
  objectNotEvil := true

/-- Switch structure with a malicious plan that wants the one dead. -/
def plannedSideEffect : Case := { switchCase with plan := fun _ => true }

/-- Switch structure with an act classified as evil by its object. -/
def switchEvilObject : Case := { switchCase with objectNotEvil := false }

/-- Switch structure with five on the side track and one ahead. -/
def switchReversed : Case := { switchCase with deathsIfIntervene := 5, deathsIfRefrain := 1 }

/-- Loop structure with a plan that includes the harm. -/
def loopPlanned : Case := { loopCase with plan := fun _ => true }

/-! ### Case facts, governing principles and verdicts (statement vocabulary) -/

def SwitchFacts (F : Scenario → Case) : Prop := F .switch = switchCase
def FootbridgeFacts (F : Scenario → Case) : Prop := F .footbridge = footbridgeCase
def TransplantFacts (F : Scenario → Case) : Prop := F .transplant = transplantCase
def LoopFacts (F : Scenario → Case) : Prop := F .loop = loopCase

/-- `X` governs the permissibility assignment `P` on the cases `F`. -/
def Governs (X : Case → Prop) (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  ∀ k, P k ↔ X (F k)

def ActConsequentialismGoverns (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  Governs ActConsequentialist F P
def CausalNoKillingGoverns (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  Governs CausalNoKilling F P
def DoubleEffectGoverns (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  Governs DoubleEffect F P
def IntentionDoubleEffectGoverns (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  Governs IntentionDoubleEffect F P
def MeansPrincipleGoverns (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  Governs MeansPrinciple F P
def RedirectionGoverns (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  Governs Redirection F P

def ActConsequentialismFails (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  ¬ ActConsequentialismGoverns F P
def CausalNoKillingFails (F : Scenario → Case) (P : Scenario → Prop) : Prop :=
  ¬ CausalNoKillingGoverns F P

def SwitchPermissible (P : Scenario → Prop) : Prop := P .switch
def SwitchImpermissible (P : Scenario → Prop) : Prop := ¬ P .switch
def FootbridgeImpermissible (P : Scenario → Prop) : Prop := ¬ P .footbridge
def FootbridgePermissible (P : Scenario → Prop) : Prop := P .footbridge
def TransplantImpermissible (P : Scenario → Prop) : Prop := ¬ P .transplant
def TransplantPermissible (P : Scenario → Prop) : Prop := P .transplant
def LoopPermissible (P : Scenario → Prop) : Prop := P .loop
def LoopImpermissible (P : Scenario → Prop) : Prop := ¬ P .loop

/-- The common triad verdicts: switch yes, footbridge no, transplant no. -/
def CommonTriadVerdicts (P : Scenario → Prop) : Prop :=
  SwitchPermissible P ∧ FootbridgeImpermissible P ∧ TransplantImpermissible P

/-- The intended case facts as one assignment. -/
def actualCases : Scenario → Case
  | .switch => switchCase
  | .footbridge => footbridgeCase
  | .transplant => transplantCase
  | .loop => loopCase

/-- Joint models: each listed principle governs a permissibility assignment that
satisfies all four case facts and the common triad verdicts, with the stated loop
verdict. Classical double effect and the means principle forbid the loop;
intention-only double effect and redirection permit it. -/
def TriadJointModels : Prop :=
  (∃ F P, DoubleEffectGoverns F P ∧ SwitchFacts F ∧ FootbridgeFacts F ∧
      TransplantFacts F ∧ LoopFacts F ∧ CommonTriadVerdicts P ∧ LoopImpermissible P) ∧
  (∃ F P, MeansPrincipleGoverns F P ∧ SwitchFacts F ∧ FootbridgeFacts F ∧
      TransplantFacts F ∧ LoopFacts F ∧ CommonTriadVerdicts P ∧ LoopImpermissible P) ∧
  (∃ F P, IntentionDoubleEffectGoverns F P ∧ SwitchFacts F ∧ FootbridgeFacts F ∧
      TransplantFacts F ∧ LoopFacts F ∧ CommonTriadVerdicts P ∧ LoopPermissible P) ∧
  (∃ F P, RedirectionGoverns F P ∧ SwitchFacts F ∧ FootbridgeFacts F ∧
      TransplantFacts F ∧ LoopFacts F ∧ CommonTriadVerdicts P ∧ LoopPermissible P)

/-- Which case fact each verdict depends on (single-feature variants). -/
def TrolleyControls : Prop :=
  -- (1) causal path only: the side-effect footbridge and the narrow-plan footbridge
  -- have the same plan, death counts and object; the harm is off the rescue path in
  -- the first and on it in the second. This flips the causal reading of double
  -- effect and the means principle, not the intention reading or consequentialism.
  (sideEffectFootbridge.plan = footbridgeNarrowPlan.plan ∧
    DoubleEffect sideEffectFootbridge ∧ ¬ DoubleEffect footbridgeNarrowPlan ∧
    MeansPrinciple sideEffectFootbridge ∧ ¬ MeansPrinciple footbridgeNarrowPlan ∧
    IntentionDoubleEffect sideEffectFootbridge ∧ IntentionDoubleEffect footbridgeNarrowPlan ∧
    ActConsequentialist sideEffectFootbridge ∧ ActConsequentialist footbridgeNarrowPlan) ∧
  -- (2) closeness: footbridge with the harm left out of the plan; the causal
  -- reading still forbids (condition 3), the intention reading permits, and the
  -- redirection principle forbids (KILLS_2).
  (¬ DoubleEffect footbridgeNarrowPlan ∧ IntentionDoubleEffect footbridgeNarrowPlan ∧
    ¬ Redirection footbridgeNarrowPlan) ∧
  -- (3) intention: switch structure with a malicious plan; double effect forbids,
  -- the means and redirection principles permit.
  (¬ DoubleEffect plannedSideEffect ∧ ¬ IntentionDoubleEffect plannedSideEffect ∧
    MeansPrinciple plannedSideEffect ∧ Redirection plannedSideEffect) ∧
  -- (4) proportionality: reversed numbers on the switch structure.
  (¬ DoubleEffect switchReversed ∧ ¬ MeansPrinciple switchReversed ∧
    ¬ Redirection switchReversed ∧ ¬ ActConsequentialist switchReversed) ∧
  -- (5) sense fork for KILLS: the switch kills in KILLS_1, not in KILLS_2;
  -- footbridge and transplant kill in both.
  (KillsCausally switchCase ∧ ¬ KillsByNewThreat switchCase ∧
    KillsByNewThreat footbridgeCase ∧ KillsByNewThreat transplantCase) ∧
  -- (6) loop divergence and its dependence on the plan fact.
  (¬ DoubleEffect loopCase ∧ ¬ MeansPrinciple loopCase ∧
    IntentionDoubleEffect loopCase ∧ Redirection loopCase ∧
    HarmIsCausalMeans loopCase ∧ ¬ PlansHarm loopCase ∧
    ¬ IntentionDoubleEffect loopPlanned ∧ Redirection loopPlanned) ∧
  -- (7) on the intention reading, condition 3 collapses into condition 2.
  (∀ c, HarmIsPlannedMeans c → PlansHarm c) ∧
  -- (8) the frame does not separate footbridge from transplant.
  (footbridgeCase.edge = transplantCase.edge ∧ footbridgeCase.plan = transplantCase.plan) ∧
  -- (9) the governing principle is needed: the case facts alone do not entail
  -- the common triad (witnessed trivially by the empty assignment).
  (∃ F P, SwitchFacts F ∧ FootbridgeFacts F ∧ TransplantFacts F ∧ LoopFacts F ∧
    ¬ CommonTriadVerdicts P) ∧
  -- (10) the INTENDS senses split on the loop and agree on the other three cases.
  (IntendsHarmAsKnownMeans loopCase ∧ ¬ PlansHarm loopCase ∧
    ¬ IntendsHarmAsKnownMeans switchCase ∧ ¬ PlansHarm switchCase ∧
    IntendsHarmAsKnownMeans footbridgeCase ∧ PlansHarm footbridgeCase ∧
    IntendsHarmAsKnownMeans transplantCase ∧ PlansHarm transplantCase) ∧
  -- (11) condition 1: an evil object on the switch structure defeats both readings
  -- of double effect, not the means or redirection principles.
  (¬ DoubleEffect switchEvilObject ∧ ¬ IntentionDoubleEffect switchEvilObject ∧
    MeansPrinciple switchEvilObject ∧ Redirection switchEvilObject)

end TruthCore.Ethics.Trolley
