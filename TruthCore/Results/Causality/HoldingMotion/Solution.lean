module

public import TruthCore.Causality.HoldingMotion

@[expose] public section

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
    HeldMoverIsHeldInItsOperativeAct InAct L H :=
  fun y x r _ hA hLack => hConcurrent y r (hActualizer y x r hA) hLack

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
  intro x r hAct hLack
  obtain ⟨hActEsse, hLackEsse⟩ := hBeing x r hAct hLack
  cases hEsse x hActEsse hLackEsse with
  | intro g _ hgx hGives => exact ⟨g, hAct, hgx, hAccidents g x r hgx hGives hAct hLack⟩

/-- The untimed esse instance from the timed strong concurrent actualization
`ConcurrentlyActualizedByAnother`, read at one moment of one history. -/
theorem lackableBeingHeldOfTimed {W B T P R : Type} (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop) (v : W) (t : T) (InAct : B → R → Prop)
    (L : Lackability B R) (H : Holding B R) (esse : R)
    (hTimed : ConcurrentlyActualizedByAnother h G EsseReceivedIn)
    (hReading : PresentMomentHoldingReading h G EsseReceivedIn v t InAct L H esse) :
    LackableBeingIsHeld InAct L H esse := by
  intro x hAct hLack
  obtain ⟨hPresent, hReceived, hGives⟩ := hReading
  obtain ⟨p, hp⟩ := hReceived x hLack
  obtain ⟨g, hgx, hg⟩ := hTimed v x t p hp (hPresent x hAct)
  exact ⟨g, hAct, hgx, hGives g x hg⟩

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
  intro hNone
  have key : ∀ x, Acc AsHeld x → ∀ z r, z ≠ x → H.ActualizesNow z x r → False := by
    intro x hAcc
    induction hAcc with
    | intro x _ ih =>
      intro z r hzx hA
      exact hNone ⟨z, x, r, hzx, hA, fun hHeld => by
        have hLink := hPerSe z x r hzx hA hHeld
        cases hHeld with
        | intro w _ hwz hAw => exact ih z hLink w r hwz hAw⟩
  obtain ⟨x, r, hHeld⟩ := hSomething
  cases hHeld with
  | intro z _ hzx hA => exact key x (hRegress x) z r hzx hA

/-- From a relative first holder, the actualizer premise and C\* in the holding
sense: the first holder could not lack the act by which it holds. -/
theorem unlosableOperativeHolder {B R : Type} (InAct : B → R → Prop) (L : Lackability B R)
    (H : Holding B R)
    (hFirst : UnheldOperativeHolderCannotBeLacking InAct H)
    (hActualizer : ActualizerIsInAct InAct H)
    (hCStar : HeldMoverIsHeldInItsOperativeAct InAct L H) :
    UnlosableOperativeHolderCannotBeLacking InAct L H := by
  intro hNone
  exact hFirst fun ⟨f, x, r, hfx, hA, hUnheld⟩ =>
    hNone ⟨f, x, r, hfx, hA, hActualizer f x r hA, fun hLack =>
      hUnheld (hCStar f x r hfx hA hLack)⟩

/-- The holding per se premise and the holding regress exclude mutual holding:
each of two beings holding the other in a respect in which both are in act is a
per se link of the other, a two-cycle that well-foundedness excludes. -/
theorem noMutualHolding {B R : Type} (InAct : B → R → Prop) (H : Holding B R)
    (AsHeld : B → B → Prop)
    (hPerSe : HeldInOperativeActIsPerSe InAct H AsHeld)
    (hRegress : NoInfiniteHoldingSeries AsHeld) :
    NoTwoHoldEachOther InAct H := by
  rintro ⟨a, b, r, hab, hAB, hBA, hActA, hActB⟩
  have e1 : AsHeld a b := hPerSe a b r hab hAB ⟨b, hActA, fun h => hab h.symm, hBA⟩
  have e2 : AsHeld b a := hPerSe b a r (fun h => hab h.symm) hBA ⟨a, hActB, hab, hAB⟩
  have key : ∀ z, Acc AsHeld z → z ≠ a ∧ z ≠ b := by
    intro z hz
    induction hz with
    | intro w _ ih =>
      constructor
      · intro hw; subst hw; exact (ih b e2).2 rfl
      · intro hw; subst hw; exact (ih a e1).1 rfl
  exact (key a (hRegress a)).1 rfl

/-- The controls of `Control.Certificate`. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- (1) cards
  · exact ⟨true, false, (), by models, by models, by models, trivial, trivial⟩
  · intro _ _ _ _; trivial
  · intro y x _ hyx _ _; exact ⟨x, trivial, fun h => hyx h.symm, fun h => hyx h.symm⟩
  · intro x _ _ _; exact ⟨!x, trivial, by cases x <;> models, by cases x <;> models⟩
  -- (2) iron
  · intro x _ hLack
    exact ⟨0, trivial, fun h => hLack h.symm, Or.inl ⟨rfl, fun h => hLack h, rfl⟩⟩
  · intro _ _ _ _; trivial
  · intro _ _ _ hLack; exact ⟨trivial, hLack⟩
  · intro hAcc
    have h := hAcc 0 1 true (by models) (Or.inl ⟨rfl, by models, rfl⟩) trivial (by models)
    rcases h with ⟨_, _, h⟩ | ⟨h, _⟩ <;> exact absurd h (by models)
  · intro hC
    have h := hC 1 2 true (by models) (Or.inr ⟨rfl, rfl, rfl⟩) (by models)
    cases h with
    | intro z _ hz hA =>
      rcases hA with ⟨_, _, h⟩ | ⟨_, h, _⟩ <;> exact absurd h (by models)
  -- (3) stick
  · intro y x r _ hA hLack
    rcases hA with ⟨hr, ⟨hy, _⟩ | ⟨hy, _⟩⟩
    · exact absurd hy hLack
    · subst hy; subst hr; exact ⟨0, trivial, by models, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨1, 2, true, by models, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, by models⟩
  · intro _ _ _ _; trivial
  · intro hAll
    cases hAll 1 false trivial (by models) with
    | intro z _ _ hA => exact absurd hA.1 (by models)
  · intro hAll
    cases hAll 1 trivial (by models) with
    | intro z _ _ hA => exact absurd hA.1 (by models)
  -- (4) MOTION_1's potency premise fails for MOTION_3
  · intro B R InAct CanBe H hSome hPot
    obtain ⟨x, r, hHeld⟩ := hSome
    cases hHeld with
    | intro z hAct hzx hA => exact (hPot x r ⟨z, hAct, hzx, hA⟩).2 hAct
  -- (5) no being is moved in one respect in both senses
  · intro B R InAct CanBe H moved hPot x r hBroad hHeld
    cases hBroad with
    | intro hMoved =>
      cases hHeld with
      | intro z hAct _ _ => exact (hPot x r hMoved).2 hAct
  -- (6) crossed
  · exact ⟨1, true, ⟨0, by models, by models, Or.inl ⟨rfl, by models, rfl⟩⟩⟩
  · intro y x r _ hA hHeld
    cases hHeld with
    | intro z _ hzy hZ =>
      rcases hA with ⟨rfl, _, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rcases hZ with ⟨_, h, _⟩ | ⟨_, _, h⟩
        · exact h rfl
        · exact absurd h (by models)
      · rcases hZ with ⟨_, _, h⟩ | ⟨_, h, _⟩ <;> exact absurd h (by models)
  · intro x; exact ⟨x, fun _ h => h.elim⟩
  · intro z x r hA
    rcases hA with ⟨rfl, _, _⟩ | ⟨rfl, _, rfl⟩ <;> models
  · intro y x r _ hA hLack
    rcases hA with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;> exact absurd hLack (by models)
  · intro x r hAct hLack
    rcases hLack with ⟨rfl, rfl⟩ | ⟨hx, rfl⟩
    · exact ⟨2, hAct, by models, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨0, hAct, fun h => hx h.symm, Or.inl ⟨rfl, hx, rfl⟩⟩
  · exact ⟨0, 1, true, by models, Or.inl ⟨rfl, by models, rfl⟩, by models, by models⟩
  · intro hNN
    apply hNN
    rintro ⟨f, ⟨x, r, hA⟩, hUnmoved⟩
    rcases hA with ⟨rfl, _, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact hUnmoved false ⟨2, by models, by models, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · exact hUnmoved true ⟨0, by models, by models, Or.inl ⟨rfl, by models, rfl⟩⟩

end TruthCore.Results.Causality.HoldingMotion
