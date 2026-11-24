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
  (NoInfinitePerSeEfficientCauseSeriesReading NothingIsEfficientCauseOfItselfReading
   SecondEfficientCausesCauseOnlyAsCausedReading NoInfinitePerSeMoverSeriesReading)
open TruthCore.Causality.PriorityInBeing (PriorityInBeingRequiresNonmutualDependence)
open TruthCore.Causality.ReflexiveDependenceScope (ActualDistinctDependenceIsGrounding)

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

/-- The sense inclusion from the secunda via's per se ordering premise: an
existential link's cause is other than its effect (no efficient self-causation)
and is itself efficiently caused, so by the per se ordering premise it causes
as caused. -/
theorem perSeEsseLinkIsPerSeCauseLinkOfOrdering {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (esse : R) (AsCaused CausesAsCaused : B → B → Prop)
    (hOrder : SecondEfficientCausesCauseOnlyAsCausedReading EfficientlyCausesIn CausesAsCaused)
    (hSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
    (hCaused : ExistentialLinkCauseIsEfficientlyCaused EfficientlyCausesIn esse AsCaused) :
    PerSeEsseLinkIsPerSeCauseLink EfficientlyCausesIn esse AsCaused CausesAsCaused := by
  intro c x h
  have hne : c ≠ x := fun e => hSelf x esse (e ▸ h.1)
  exact hOrder c x esse hne h.1 (hCaused c x h)

/-! ## (ii) Priority in being -/

/-- The PRIOR_4 bridge from dependence: what is PRIOR_4 to `x` is other than `x`
(PRIOR_4 is irreflexive by definition), `x` depends for its being on it
(c4bb0481), and a distinct actual dependee grounds (a8298fbd). -/
theorem priorInBeingGroundOfDependence {W B : Type} (m : GProfile W B) (w : W)
    (CanBeWithout DependsForBeing : B → B → Prop)
    (hDep : PriorityInBeingRequiresNonmutualDependence CanBeWithout DependsForBeing)
    (hGround : ActualDistinctDependenceIsGrounding m w DependsForBeing) :
    PriorInBeingAmongActualConcretaIsGround m w CanBeWithout := by
  intro y x hy hx h
  have hne : y ≠ x := fun e => by subst e; exact h.2 h.1
  exact hGround y x hne hx hy (hDep y x h).1

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
    ⟨?_, ?_, ?_, ⟨rfl, rfl⟩, trivial⟩⟩
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
    ⟨fun x => edgeTF_wf.apply x, fun _ _ h => h.1, effEdge_series, ⟨rfl, rfl⟩, trivial⟩⟩

theorem cyc_caused (c : Bool) : ∃ d r, eff cyc d c r :=
  ⟨!c, (), by cases c <;> exact fun h => Bool.noConfusion h⟩

theorem inclusionSupportControls : InclusionSupportControls := by
  refine ⟨⟨fun h => h true false () true_ne_false' true_ne_false' ⟨false, (), fun e => true_ne_false' e.symm⟩,
      fun _ _ h => h rfl, fun c _ _ => cyc_caused c,
      fun h => h true false ⟨true_ne_false', trivial⟩⟩,
    ⟨fun c x _ hne h _ => (hne (h.1.trans h.2.symm)).elim, fun h => h true () ⟨rfl, rfl⟩,
      fun c x h => ⟨c, (), ⟨h.1.1, h.1.1⟩⟩, fun h => h true true ⟨⟨rfl, rfl⟩, trivial⟩⟩,
    ⟨?_, fun x _ h => true_ne_false' (h.1.symm.trans h.2), ?_,
      fun h => h true false ⟨⟨rfl, rfl⟩, trivial⟩⟩,
    ⟨fun _ _ _ _ h _ => h, fun _ _ h => h rfl, fun c _ _ => cyc_caused c, fun _ _ h => h.1,
      true_ne_false', trivial⟩⟩
  · intro c x r _ h hc
    obtain ⟨d, _, hd⟩ := hc
    exact (true_ne_false' (h.1.symm.trans hd.2)).elim
  · intro h
    obtain ⟨d, _, hd⟩ := h true false ⟨⟨rfl, rfl⟩, trivial⟩
    exact true_ne_false' hd.2
theorem oldBridgeControls : OldBridgeControls := by
  refine ⟨⟨fun h => (h true false true_ne_false').1.2.2.2, fun _ _ h => h.1, ?_⟩,
    ⟨fun _ _ h => h.elim, fun h => h true false ⟨true_ne_false', trivial⟩, ?_⟩,
    ⟨?_, fun _ _ h => h.1, ?_, ⟨rfl, rfl⟩, trivial⟩⟩
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

theorem caaTwo_not_acc : ¬ NoInfinitePerSeEfficientCauseSeriesReading caaTwo := by
  intro h
  have key : ∀ n, Acc caaTwo n → False := by
    intro n hn
    induction hn with
    | intro n _ ih => exact ih (n + 1) (Or.inr rfl)
  exact key 0 (h 0)

theorem succUp_not_acc : ¬ NoInfinitePerSeMoverSeriesReading succUp := by
  intro h
  have key : ∀ n, Acc succUp n → False := by
    intro n hn
    induction hn with
    | intro n _ ih => exact ih (n + 1) rfl
  exact key 0 (h 0)

theorem effTwo_esse {c x : Nat} (h : effTwo c x true) : edge10 c x := by
  rcases h with h | h
  · exact h.2
  · exact (Bool.noConfusion h.1)

theorem secundaSplitLimit : SecundaSplitLimit := by
  refine ⟨actualGroundingWF_of_wellFounded _ _ edge10_wf, fun _ _ _ _ _ h => h.2,
    fun _ _ => trivial, fun _ _ => trivial,
    wellFounded_of_singleEdge 1 0 one_ne_zero' (fun _ _ h => h.2.2.2.2),
    wellFounded_of_singleEdge 1 0 one_ne_zero' (fun _ _ h => h.1.2.2.2.2),
    ?_, ?_,
    fun x => (wellFounded_of_singleEdge 1 0 one_ne_zero' (fun _ _ h => effTwo_esse h.1)).apply x,
    ⟨Or.inl ⟨rfl, rfl, rfl⟩, trivial⟩, ?_, fun _ _ h => Or.inr h, Or.inr ⟨rfl, rfl⟩,
    caaTwo_not_acc, succUp_not_acc, ?_⟩
  · intro c x h
    have he := effTwo_esse h.1
    refine ⟨⟨?_, trivial, trivial, rfl, he⟩, trivial⟩
    intro e
    exact one_ne_zero' (he.1.symm.trans (e.trans he.2))
  · intro c x h
    exact Or.inl (effTwo_esse h.1)
  · intro c x r _ h _
    rcases h with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  · intro h
    have k := (h 2 1 (Or.inr rfl)).1.2.2.2.2
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

theorem tfWithout_wf : WellFounded (PriorInBeing tfWithout) :=
  wellFounded_of_singleEdge true false true_ne_false' (fun _ _ h => h.1)

theorem priorityBridgeControls : PriorityBridgeControls := by
  refine ⟨⟨fun h => (h true false ⟨⟨rfl, rfl⟩, fun e => true_ne_false' e.2⟩).1,
      fun _ _ _ _ _ h => h, fun h => h true false ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
        ⟨⟨rfl, rfl⟩, fun e => true_ne_false' e.2⟩⟩,
    ⟨?_, fun h => h true false true_ne_false' ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨rfl, rfl⟩,
      fun h => h true false ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
        ⟨⟨rfl, rfl⟩, fun e => true_ne_false' e.2⟩⟩,
    ⟨?_, ?_, fun _ _ _ _ h => h.1, ⟨rfl, rfl⟩, fun e => true_ne_false' e.2⟩⟩
  · intro y x h
    exact ⟨⟨h.1.2, h.1.1⟩, fun e => true_ne_false' (h.1.1.symm.trans e.1)⟩
  · intro y x h
    exact ⟨⟨h.1.2, h.1.1⟩, fun e => true_ne_false' (h.1.1.symm.trans e.1)⟩
  · intro c x _ _ _ h
    exact ⟨h.2, h.1⟩

theorem priorityConsumerLimit : PriorityConsumerLimit := by
  refine ⟨⟨actualGroundingWF_of_wellFounded _ _ edgeTF_wf, fun _ _ _ _ h => h.1, ?_, tfWithout_wf,
      ⟨⟨rfl, rfl⟩, fun e => true_ne_false' e.2⟩, fun y x h => ⟨(), h⟩, fun _ _ _ h => h,
      fun _ h => h rfl, cyc_not_wf, cyc_not_wf,
      fun h => true_ne_false' (h false true (fun e => true_ne_false' e.symm) (fun e => true_ne_false' e.symm)).2.2.2,
      fun h => true_ne_false' (h false true () (fun e => true_ne_false' e.symm)).1.1.symm,
      fun e => true_ne_false' e.symm, fun h => true_ne_false' h.1.1.symm⟩,
    ⟨⟨rfl, rfl⟩, fun e => true_ne_false' e.2⟩, fun h => h⟩
  · exact Subrelation.wf (r := InvImage (PriorInBeing tfWithout)
      (fun a : {x // ActualConcrete mEdge () x} => a.1)) (fun h => h) (InvImage.wf _ tfWithout_wf)

end TruthCore.Results.Causality.DependenceOrderSenses
