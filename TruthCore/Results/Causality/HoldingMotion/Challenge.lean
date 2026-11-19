import TruthCore.Causality.HoldingMotion

namespace TruthCore.Results.Causality.HoldingMotion

open TruthCore.Causality.HoldingMotion
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualizedByAnother)
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Modal.TemporalHistory (History)
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Unfold the control models and decide. -/
local macro "models" : tactic => `(tactic| ((try simp only [Control.cards, Control.stick, Control.notZero,
  Control.iron, Control.crossed, Control.crossedLack, Control.crossedInAct] at *) <;>
  first | decide | simp_all | trivial))

/-- C\* in the holding sense from respect-general concurrent actualization. A
mover `y` presently actualizing `x` in `r` is in act in `r` (actualizer
premise); if it could lack that act, concurrent actualization makes it
presently held in `r` by something other than itself. -/
theorem cstarHoldingOfConcurrentActualization {B R : Type} (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R)
    (hActualizer : ActualizerIsInAct InAct H)
    (hConcurrent : LackableActsAreHeld InAct L H) :
    HeldMoverIsHeldInItsOperativeAct InAct L H := by
  sorry

/-- Respect-general concurrent actualization from its esse instance. A thing in
act in `r` that could lack that act is in act as to being and could lack being;
so something other than it presently gives it being, and what gives it being
presently actualizes it in every act it could lack, `r` included. -/
theorem lackableActsHeldOfEsse {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R) (esse : R)
    (hEsse : LackableBeingIsHeld InAct L H esse)
    (hAccidents : GivingBeingHoldsLackableActs InAct L H esse)
    (hBeing : LackableActBringsLackableBeing InAct L esse) :
    LackableActsAreHeld InAct L H := by
  sorry

/-- The untimed esse instance from the timed strong concurrent actualization
`ConcurrentlyActualizedByAnother`, read at one moment of one history. -/
theorem lackableBeingHeldOfTimed {W B T P R : Type} (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop) (v : W) (t : T) (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R)
    (hTimed : ConcurrentlyActualizedByAnother h G EsseReceivedIn)
    (hReading : PresentMomentHoldingReading h G EsseReceivedIn v t InAct L H esse) :
    LackableBeingIsHeld InAct L H esse := by
  sorry

/-- The holding First Way to a relative first holder. Take a held thing `x` and
a holder `z` of it. If `z` is not held in the respect by which it holds `x`, it
is the holder sought; if it is, `z` is a per se link of `x`, and the argument
repeats one step up the well-founded holding series. -/
theorem unheldOperativeHolder {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (AsHeld : B → B → Prop)
    (hSomething : SomethingIsHeld InAct H)
    (hPerSe : HeldInOperativeActIsPerSe InAct H AsHeld)
    (hRegress : NoInfiniteHoldingSeries AsHeld) :
    UnheldOperativeHolderCannotBeLacking InAct H := by
  sorry

/-- From a relative first holder, the actualizer premise and C\* in the holding
sense: the first holder could not lack the act by which it holds. -/
theorem unlosableOperativeHolder {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R)
    (hFirst : UnheldOperativeHolderCannotBeLacking InAct H)
    (hActualizer : ActualizerIsInAct InAct H)
    (hCStar : HeldMoverIsHeldInItsOperativeAct InAct L H) :
    UnlosableOperativeHolderCannotBeLacking InAct L H := by
  sorry

/-- The holding per se premise and the holding regress exclude mutual holding:
each of two beings holding the other in a respect in which both are in act is a
per se link of the other, a two-cycle that well-foundedness excludes. -/
theorem noMutualHolding {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (AsHeld : B → B → Prop)
    (hPerSe : HeldInOperativeActIsPerSe InAct H AsHeld)
    (hRegress : NoInfiniteHoldingSeries AsHeld) :
    NoTwoHoldEachOther InAct H := by
  sorry

/-- The controls of `Control.Certificate`. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.HoldingMotion
