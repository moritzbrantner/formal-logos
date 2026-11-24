module

public import TruthCore.Causality.DependenceOrderSenses
public import TruthCore.Results.Causality.OneDependenceOrder.Solution

/-!
# Sense splits for the one dependence order (#1926 phase 3, continued)

(i) SERIES_OF_CAUSES_4, the existential per se efficient-cause link:

* `perSeEsseSeriesOfPerSeEsseRegress`: the PER_SE_5 regress (ea251340) and the
  restated bridge (every existential per se link is a PER_SE_5 actual cause of
  being) give the existential no-regress premise.
* `perSeEsseLinksOfPresentEsseCause`: no self-causation (8b2561cd) and the
  cross-vocabulary bridge (a here-and-now efficient cause of another's being is an
  actual cause of its being) give the restated bridge.
* `perSeEsseSeriesOfPerSeEfficientSeries`: 97f5850f (SERIES_OF_CAUSES_3) and the
  inclusion of SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3 give the existential
  no-regress premise.
* `perSeEsseLinksOfPerSeEfficientLinks`: e8664ab8 and the inclusion give the
  restated bridge.

(ii) PRIOR_4:

* `priorityInBeingWFOfActualGroundingWF`: actual grounding well-founded and the
  PRIOR_4 bridge among actual concreta give PRIOR_4 well-founded among actual
  concreta.

Controls: omissions and nonvacuity for each result, `secundaSplitLimit` and
`priorityConsumerLimit`.
-/

@[expose] public section

namespace TruthCore.Results.Causality.DependenceOrderSenses

open TruthCore.Causality.DependenceOrderSenses
open TruthCore.Causality.DependenceOrderSenses.Control
open TruthCore.Causality.OneDependenceOrder
  (PerSeEfficientCausesArePerSeEsseCauses ActualEsseCauseIsActualGround
   wellFounded_of_predecessorInclusion not_wellFounded_of_twoCycle not_wellFounded_of_loop
   wellFounded_of_singleEdge not_wellFounded_succ actualGroundingWF_of_wellFounded)
open TruthCore.Causality.OneDependenceOrder.Control
open TruthCore.Results.Causality.OneDependenceOrder
  (true_ne_false' cyc_not_wf noRel_wf edgeTF_wf edge10_wf pNone_regress pEdge_regress)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.PriorityInBeing (PriorInBeing)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause PerSeActualEsseCause NoInfiniteActualEsseCauseRegress
   NoInfinitePerSeActualEsseCauseRegress)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NoInfinitePerSeEfficientCauseSeriesReading NothingIsEfficientCauseOfItselfReading)

/-! ## (i) The existential per se series -/

/-- Existential per se links into PER_SE_5 actual causes of being: every
existential link is a PER_SE_5 link (restated bridge), so accessibility along
PER_SE_5 links gives accessibility along existential links. -/
theorem perSeEsseSeriesOfPerSeEsseRegress {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused : B → B → Prop)
    (hRegress : NoInfinitePerSeActualEsseCauseRegress p AsCaused)
    (hBridge : PerSeEsseLinksArePerSeEsseCauses p EfficientlyCausesIn AsCaused) :
    NoInfinitePerSeEsseEfficientCauseSeries EfficientlyCausesIn p.esse AsCaused :=
  fun x => Subrelation.accessible (fun h => hBridge _ _ h) (hRegress.apply x)

/-- The restated bridge from its parts: an existential link's cause is other than
its effect (no efficient self-causation), so the cross-vocabulary bridge makes it
an actual cause of being; the per se link carries over unchanged. -/
theorem perSeEsseLinksOfPresentEsseCause {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused : B → B → Prop)
    (hSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
    (hPresent : PresentEfficientEsseCauseIsActualEsseCause p EfficientlyCausesIn) :
    PerSeEsseLinksArePerSeEsseCauses p EfficientlyCausesIn AsCaused := by
  intro c x h
  have hne : c ≠ x := fun e => hSelf x p.esse (e ▸ h.1)
  exact ⟨hPresent c x hne h.1, h.2⟩

/-- SERIES_OF_CAUSES_4 into SERIES_OF_CAUSES_3: accessibility along
`CausesAsCaused` gives accessibility along existential links included in it. -/
theorem perSeEsseSeriesOfPerSeEfficientSeries {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (esse : R) (AsCaused CausesAsCaused : B → B → Prop)
    (hSeries : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused)
    (hIncl : PerSeEsseLinkIsPerSeCauseLink EfficientlyCausesIn esse AsCaused CausesAsCaused) :
    NoInfinitePerSeEsseEfficientCauseSeries EfficientlyCausesIn esse AsCaused :=
  fun x => Subrelation.accessible (fun h => hIncl _ _ h) (hSeries x)

/-- The restated bridge from e8664ab8 and the inclusion: an existential link is a
`CausesAsCaused` link, which e8664ab8 makes a PER_SE_5 link. -/
theorem perSeEsseLinksOfPerSeEfficientLinks {B P R : Type} (p : Q3Profile B P R)
    (EfficientlyCausesIn : B → B → R → Prop) (AsCaused CausesAsCaused : B → B → Prop)
    (hOld : PerSeEfficientCausesArePerSeEsseCauses p AsCaused CausesAsCaused)
    (hIncl : PerSeEsseLinkIsPerSeCauseLink EfficientlyCausesIn p.esse AsCaused CausesAsCaused) :
    PerSeEsseLinksArePerSeEsseCauses p EfficientlyCausesIn AsCaused :=
  fun c x h => hOld c x (hIncl c x h)

/-! ## (ii) Priority in being -/

/-- PRIOR_4 among actual concreta into grounding: each PRIOR_4 step between
actual concreta is a grounding step (bridge), so well-foundedness of grounding
among actual concreta transfers. -/
theorem priorityInBeingWFOfActualGroundingWF {W B : Type} (m : GProfile W B) (w : W)
    (CanBeWithout : B → B → Prop)
    (hWF : ActualGroundingWF m w)
    (hBridge : PriorInBeingAmongActualConcretaIsGround m w CanBeWithout) :
    PriorityInBeingWFAmongActualConcreta m w CanBeWithout :=
  Subrelation.wf (fun {a b} h => hBridge a.1 b.1 a.2 b.2 h) hWF

/-! ## Controls -/

theorem cyc_ne {a b : Bool} (h : cyc a b) : a ≠ b := h

theorem effCyc_not_series :
    ¬ NoInfinitePerSeEsseEfficientCauseSeries (eff cyc) () (allLinks : Bool → Bool → Prop) :=
  fun h => not_wellFounded_of_twoCycle
    (R := CausesBeingAsCaused (eff cyc) () (allLinks : Bool → Bool → Prop)) true false
    ⟨true_ne_false', trivial⟩ ⟨fun e => true_ne_false' e.symm, trivial⟩ ⟨h⟩

theorem effEdge_series :
    NoInfinitePerSeEsseEfficientCauseSeries (eff edgeTF) () (allLinks : Bool → Bool → Prop) :=
  fun x => (wellFounded_of_singleEdge true false true_ne_false' (fun _ _ h => h.1)).apply x

theorem perSeEsseSeriesControls : PerSeEsseSeriesControls := by
  refine ⟨⟨?_, fun c x h => ⟨⟨h.1, trivial, trivial, h.1⟩, trivial⟩, effCyc_not_series⟩,
    ⟨Subrelation.wf (fun h => h.1) pNone_regress, ?_, effCyc_not_series⟩,
    ⟨Subrelation.wf (fun h => h.1) pEdge_regress, ?_, effEdge_series, ⟨rfl, rfl⟩, trivial⟩⟩
  · exact not_wellFounded_of_twoCycle true false
      ⟨⟨true_ne_false', trivial, trivial, true_ne_false'⟩, trivial⟩
      ⟨⟨fun h => true_ne_false' h.symm, trivial, trivial, fun h => true_ne_false' h.symm⟩, trivial⟩
  · exact fun h => (h true false ⟨true_ne_false', trivial⟩).1.2.2.2
  · intro c x h
    refine ⟨⟨?_, trivial, trivial, h.1⟩, trivial⟩
    intro e
    exact true_ne_false' (h.1.1.symm.trans (e.trans h.1.2))

theorem presentCauseControls : PresentCauseControls := by
  refine ⟨⟨fun h => h true () ⟨rfl, rfl⟩, ?_, ?_⟩,
    ⟨fun x _ h => h rfl, fun h => (h true false true_ne_false' true_ne_false').2.2.2, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩
  · intro c x hne h
    exact (hne (h.1.trans h.2.symm)).elim
  · exact fun h => (h true true ⟨⟨rfl, rfl⟩, trivial⟩).1.1 rfl
  · exact fun h => (h true false ⟨true_ne_false', trivial⟩).1.2.2.2
  · intro x _ h
    exact true_ne_false' (h.1.symm.trans h.2)
  · intro c x hne h
    exact ⟨hne, trivial, trivial, h⟩
  · intro c x h
    refine ⟨⟨?_, trivial, trivial, h.1⟩, trivial⟩
    intro e
    exact true_ne_false' (h.1.1.symm.trans (e.trans h.1.2))

theorem senseInclusionControls : SenseInclusionControls := by
  refine ⟨⟨fun h => cyc_not_wf ⟨h⟩, fun _ _ h => h.1, effCyc_not_series⟩,
    ⟨fun x => noRel_wf.apply x, fun h => h true false ⟨true_ne_false', trivial⟩,
      effCyc_not_series⟩,
    ⟨fun x => edgeTF_wf.apply x, fun _ _ h => h.1, effEdge_series⟩⟩

theorem oldBridgeControls : OldBridgeControls := by
  refine ⟨⟨fun h => (h true false true_ne_false').1.2.2.2, fun _ _ h => h.1, ?_⟩,
    ⟨fun _ _ h => h.elim, fun h => h true false ⟨true_ne_false', trivial⟩, ?_⟩,
    ⟨?_, fun _ _ h => h.1, ?_⟩⟩
  · exact fun h => (h true false ⟨true_ne_false', trivial⟩).1.2.2.2
  · exact fun h => (h true false ⟨true_ne_false', trivial⟩).1.2.2.2
  · intro c x h
    refine ⟨⟨?_, trivial, trivial, h⟩, trivial⟩
    intro e
    exact true_ne_false' (h.1.symm.trans (e.trans h.2))
  · intro c x h
    refine ⟨⟨?_, trivial, trivial, h.1⟩, trivial⟩
    intro e
    exact true_ne_false' (h.1.1.symm.trans (e.trans h.1.2))

theorem one_ne_zero' : (1 : Nat) ≠ 0 := fun h => Nat.noConfusion h

theorem secundaSplitLimit : SecundaSplitLimit := by
  refine ⟨actualGroundingWF_of_wellFounded _ _ edge10_wf, fun _ _ _ _ _ h => h,
    fun _ _ => trivial, fun _ _ => trivial,
    wellFounded_of_singleEdge 1 0 one_ne_zero' (fun _ _ h => h.2.2.2),
    wellFounded_of_singleEdge 1 0 one_ne_zero' (fun _ _ h => h.1.2.2.2),
    ?_, ?_,
    fun x => (wellFounded_of_singleEdge 1 0 one_ne_zero' (fun _ _ h => h.1)).apply x,
    ⟨⟨rfl, rfl⟩, trivial⟩,
    fun h => not_wellFounded_succ ⟨h⟩, fun h => not_wellFounded_succ ⟨h⟩, ?_⟩
  · intro c x h
    refine ⟨⟨?_, trivial, trivial, h.1⟩, trivial⟩
    intro e
    exact one_ne_zero' (h.1.1.symm.trans (e.trans h.1.2))
  · intro c x h
    have h1 : c = 1 := h.1.1
    have h2 : x = 0 := h.1.2
    subst h1 h2
    rfl
  · intro h
    have k := (h 2 1 rfl).1.2.2.2
    exact Nat.noConfusion (Nat.succ.inj k.1)

theorem lt_not_wf_sub (m : GProfile Unit Nat) (hAll : ∀ x, ActualConcrete m () x)
    (R : Nat → Nat → Prop) (hR : ∀ x, R (x + 1) x) :
    ¬ WellFounded fun a b : {x // ActualConcrete m () x} => R a.1 b.1 := by
  intro hWF
  apply not_wellFounded_succ
  have hWF' : WellFounded R :=
    Subrelation.wf (r := InvImage (fun a b : {x // ActualConcrete m () x} => R a.1 b.1)
      (fun x => ⟨x, hAll x⟩)) (fun h => h) (InvImage.wf _ hWF)
  exact Subrelation.wf (fun {y x} (h : y = x + 1) => h ▸ hR x) hWF'

theorem priorInBeing_lt {y x : Nat} (h : x < y) : PriorInBeing ltWithout y x :=
  ⟨h, fun h' => Nat.lt_asymm h h'⟩

theorem priorityInBeingControls : PriorityInBeingControls := by
  refine ⟨⟨lt_not_wf_sub mLt (fun _ => ⟨trivial, trivial⟩) _ (fun x => Nat.lt_succ_self x),
      fun _ _ _ _ h => h.1,
      lt_not_wf_sub mLt (fun _ => ⟨trivial, trivial⟩) _ (fun x => priorInBeing_lt (Nat.lt_succ_self x))⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_,
      lt_not_wf_sub mNoneNat (fun _ => ⟨trivial, trivial⟩) _
        (fun x => priorInBeing_lt (Nat.lt_succ_self x))⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ edgeTF_wf, fun _ _ _ _ h => h.1, ?_, ⟨⟨rfl, rfl⟩, ?_⟩⟩⟩
  · exact fun h => h 1 0 ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ (priorInBeing_lt Nat.zero_lt_one)
  · exact Subrelation.wf (r := InvImage edgeTF (fun a : {x // ActualConcrete mEdge () x} => a.1))
      (fun h => h.1) (InvImage.wf _ edgeTF_wf)
  · exact fun h => true_ne_false' h.2

theorem priorityConsumerLimit : PriorityConsumerLimit := by
  refine ⟨⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, fun _ _ _ _ h => (h.2 trivial).elim,
      ?_, ?_, fun y x h => ⟨(), h⟩, fun _ _ _ h => h, fun _ h => h rfl, cyc_not_wf, cyc_not_wf,
      fun h => (h true false true_ne_false' true_ne_false').2.2,
      fun h => (h true false () true_ne_false').2 trivial, true_ne_false',
      fun h => h.2 trivial⟩,
    ⟨⟨rfl, rfl⟩, fun h => true_ne_false' h.2⟩, fun h => h⟩
  · exact ⟨fun a => ⟨a, fun _ h => (h.2 trivial).elim⟩⟩
  · exact ⟨fun a => ⟨a, fun _ h => (h.2 trivial).elim⟩⟩

end TruthCore.Results.Causality.DependenceOrderSenses
