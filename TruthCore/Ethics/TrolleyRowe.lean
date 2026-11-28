module

public import TruthCore.Ethics.Trolley
public import TruthCore.English.Rowe.EvidentialEvil
public import TruthCore.Case.Catholicism.DivineLoveBridge

/-! Senses of Rowe's `WhollyGood` built from the trolley principles (analyst
formulation; attribution deferred). The question is which sense of "wholly good"
makes Rowe's permission constraint (`PermissionConstraintReading`) follow.

Reused: Rowe's signature `Sig`, `BlockingCost` and `PermissionConstraintReading`
(`TruthCore.English.Rowe`), the trolley case vocabulary
(`TruthCore.Ethics.Trolley`), and the stage-2 goodness predicates
`DivineWillsGoodForAllExisting` and `GodIsSupremelyGood`.

A prevention way for a being and a suffering event is described by a trolley
`Case`: intervening is preventing; `harmOne` is a harm the preventer itself would
do to a third party; `saveFive` is the event's being prevented. `Better b e`
says preventing `e` is strictly better overall than permitting it. Both are
supplied interpretations: no claim is made about which ways an omnipotent being
actually has, or about any actual comparison of outcomes.

Senses of WHOLLY_GOOD:
* WHOLLY_GOOD_1 `OutcomeStandard`: an outcome-minimizing agent never permits what
  it would be strictly better to prevent (the trolley act-consequentialist
  pattern applied to permitting).
* WHOLLY_GOOD_2 `ConstraintStandard`: a constraint-respecting rescuer keeps that
  rescue duty unless every way of preventing violates one of the first three
  double-effect conditions (doing/allowing and the means/side-effect distinction
  shape the duty; they do not remove it).
* WHOLLY_GOOD_3: ontological supreme goodness plus willing some good to every
  existing being (`GodIsSupremelyGood`, `DivineWillsGoodForAllExisting`), with
  Rowe's `WhollyGood` read as that bearer predicate on a shared carrier.
-/

@[expose] public section

namespace TruthCore.Ethics.TrolleyRowe
open TruthCore.Ethics.Trolley TruthCore.English.Rowe

/-- Supplied prevention ways and the all-things-considered comparison. -/
structure PreventionWays (s : Sig) where
  Way : s.Being → s.Event → Case → Prop
  Better : s.Being → s.Event → Prop

/-- A prevention way fails one of double-effect conditions 1–3: an evil object,
a planned harm, or a harm used as a causal means (MEANS_1). -/
def ConstraintViolating (w : Case) : Prop :=
  w.objectNotEvil = false ∨ PlansHarm w ∨ HarmIsCausalMeans w

/-- Some way of preventing exists, and every such way violates a constraint. -/
def ConstraintBlocked (s : Sig) (W : PreventionWays s) (b : s.Being) (e : s.Event) : Prop :=
  (∃ w, W.Way b e w) ∧ ∀ w, W.Way b e w → ConstraintViolating w

/-- WHOLLY_GOOD_1: a wholly good being never permits an occurring event it could
prevent when preventing it would be strictly better. -/
def OutcomeStandard (s : Sig) (W : PreventionWays s) : Prop :=
  ∀ b e, s.WhollyGood b → s.Occurs e → s.CanPrevent b e → ¬ W.Better b e

/-- WHOLLY_GOOD_2: a wholly good being permits an occurring preventable event that
would be strictly better prevented only when every way of preventing it is
constraint-violating. -/
def ConstraintStandard (s : Sig) (W : PreventionWays s) : Prop :=
  ∀ b e, s.WhollyGood b → s.Occurs e → s.CanPrevent b e →
    ¬ W.Better b e ∨ ConstraintBlocked s W b e

/-- OPEN outcome bridge: when a preventable event has no blocking cost in Rowe's
sense, preventing it is strictly better than permitting it. It fails if several
individually lesser costs can jointly outweigh the suffering. -/
def UnblockedPreventionBetter (s : Sig) (W : PreventionWays s) : Prop :=
  ∀ b e, s.CanPrevent b e → ¬ BlockingCost s b e → W.Better b e

/-- The weakened permission constraint: Rowe's blocking cost, or every way of
preventing is constraint-violating. -/
def ConstraintQualifiedPermission (s : Sig) (W : PreventionWays s) : Prop :=
  ∀ b e, s.Omniscient b → s.WhollyGood b → s.Occurs e → s.IntenseSuffering e →
    s.CanPrevent b e → BlockingCost s b e ∨ ConstraintBlocked s W b e

/-- A prevention way with no harm at all: the act prevents the event directly. -/
def harmlessRescue : Case where
  edge
    | .act, .saveFive => true
    | _, _ => false
  deathsIfIntervene := 0
  deathsIfRefrain := 1
  plan
    | .harmOne => false
    | _ => true
  objectNotEvil := true

/-- Controls for the three senses.
(1) The constraint sense does not yield Rowe's simplified constraint: a model with
the outcome bridge, the constraint standard, a narrow theistic being and an
unblocked preventable suffering whose only prevention way is the footbridge
structure.
(2) Easy rescue survives: under the qualified constraint, a constraint-free way
of preventing restores Rowe's blocking-cost requirement.
(3) The ontological sense (WHOLLY_GOOD_3) does not yield it either: Rowe's
`WhollyGood` read as a bearer of supreme goodness who wills some good to every
existing being, with omniscience, omnipotence and an unblocked preventable
suffering, while the permission constraint fails.
(4) The outcome bridge is needed for WHOLLY_GOOD_1.
(5) How the constraint clause classifies the trolley-shaped ways: the switch,
side-effect and harmless ways are constraint-free; footbridge, transplant and
loop ways are constraint-violating (the loop through MEANS_1 alone). -/
def GoodnessSenseControls : Prop :=
  (∃ (s : Sig) (W : PreventionWays s), UnblockedPreventionBetter s W ∧
    ConstraintStandard s W ∧ TheisticBeingExists s ∧ ¬ PermissionConstraintReading s) ∧
  (∀ (s : Sig) (W : PreventionWays s), ConstraintQualifiedPermission s W →
    ∀ b e, s.Omniscient b → s.WhollyGood b → s.Occurs e → s.IntenseSuffering e →
      s.CanPrevent b e → (∃ w, W.Way b e w ∧ ¬ ConstraintViolating w) →
        BlockingCost s b e) ∧
  (∃ (s : Sig) (Respect : Type) (InAct GoodIn : s.Being → Respect → Prop)
      (CausesIn : s.Being → s.Being → Respect → Prop)
      (WillsGoodFor : s.Being → s.Being → Respect → Prop) (esse : Respect),
    TruthCore.Case.Catholicism.GodIsSupremelyGood s.WhollyGood InAct GoodIn CausesIn esse ∧
    TruthCore.Case.Catholicism.DivineLoveBridge.DivineWillsGoodForAllExisting
      s.WhollyGood InAct GoodIn WillsGoodFor esse ∧
    TheisticBeingExists s ∧ ¬ PermissionConstraintReading s) ∧
  (∃ (s : Sig) (W : PreventionWays s), OutcomeStandard s W ∧
    TheisticBeingExists s ∧ ¬ PermissionConstraintReading s) ∧
  (¬ ConstraintViolating switchCase ∧ ¬ ConstraintViolating sideEffectFootbridge ∧
    ¬ ConstraintViolating harmlessRescue ∧ ConstraintViolating footbridgeCase ∧
    ConstraintViolating transplantCase ∧ ConstraintViolating loopCase ∧
    ¬ PlansHarm loopCase)

end TruthCore.Ethics.TrolleyRowe
