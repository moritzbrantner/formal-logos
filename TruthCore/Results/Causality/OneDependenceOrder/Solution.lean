module

public import TruthCore.Causality.OneDependenceOrder

/-!
# One dependence order (#1926 phase 3)

* `esseRegressOfActualGroundingWF`: actual grounding well-founded, an actual
  concretum's distinct esse cause is its actual concrete ground (cb1cdea9),
  what is in act of esse exists at `w` (546975ef) and is concrete (2d9807a5)
  give no infinite regress of actual causes of being (fd12ad3d).
* `esseRegressOfActualGroundingWFWeak`: the same with the weak bridge
  `ActualEsseCauseIsActualGround` (an actual cause of being between actual
  concreta grounds), which `actualEsseCauseIsActualGroundOfEsseCause` derives
  from cb1cdea9.
* `actualGroundingWFOfEsseRegress`: the converse inclusion. The esse regress,
  an actual concrete ground of an actual concretum is a distinct cause of its
  esse (98efaa9e) and what exists at `w` is in act of esse (0436de86) give
  well-founded actual grounding.
* `simplePriorityWFOfActualGroundingWF`: actual grounding well-founded, what is
  simply prior to something other than itself is its actual concrete ground
  (86efed1a) and nothing is prior to itself (32d77f18) give well-founded simple
  priority (d85de8e1), for the frame's `F.PriorSimply`.
* `perSeEfficientSeriesOfPerSeEsseRegress`: the per se esse regress
  (ea251340) and the new bridge that per se efficient-cause links are per se
  actual causes of being give no infinite per se series of efficient causes
  (97f5850f).

Each step transfers well-foundedness along an explicit inclusion; nothing
identifies the relations. The controls show each input is needed under the
encoded predicates, that actual grounding is not recovered from what it implies
without the converse bridge, and (`ascentLimit`) that actual grounding with
the inclusions listed in `AscentLimit` does not give the quarta via's
no-infinite-ascent premise.
-/

@[expose] public section

namespace TruthCore.Results.Causality.OneDependenceOrder

open TruthCore.Causality.OneDependenceOrder
open TruthCore.Causality.OneDependenceOrder.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Latin.Aquinas.DeEnte
  (ActualEsseCause NoInfiniteActualEsseCauseRegress NoInfinitePerSeActualEsseCauseRegress)
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.GradedSupportFoundation
  (ActualGroundIsDistinctEsseCause NoInfiniteAscentAmongActualConcreta)
open TruthCore.Causality.Round5Worklist (SimplePriorityWellFounded)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NothingPriorToItselfReading NoInfinitePerSeEfficientCauseSeriesReading)

/-! ## The derivations -/

/-- Esse causing into actual grounding: every actual cause of being `c` of `x`
is, by the two actuality calibrations, a cause of the esse of an actual
concretum, hence (bridge) an actual concrete ground of it. Well-foundedness of
grounding among actual concreta transfers to actual causes of being. -/
theorem esseRegressOfActualGroundingWF {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hWF : ActualGroundingWF m w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExists : ActOfEsseSufficesForExistenceAt m.ontic p.InAct p.esse w)
    (hConcrete : EsseInReIsConcrete m p.InAct p.esse) :
    NoInfiniteActualEsseCauseRegress p := by
  refine wellFounded_of_predecessorInclusion (ActualConcrete m w) (m.grounds w) _ hWF ?_
  intro c x h
  obtain ⟨hne, _, hx, hcause⟩ := h
  have g := hEsse c x hne ⟨hConcrete x hx, hExists x hx⟩ hcause
  exact ⟨⟨g.1, g.2.1⟩, g.2.2⟩

/-- The same with the weak bridge: an actual cause of being `c` of `x` is in
act, as is `x`, so by the two calibrations both are actual concreta; the weak
bridge then makes `c` ground `x`. -/
theorem esseRegressOfActualGroundingWFWeak {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hWF : ActualGroundingWF m w)
    (hGround : ActualEsseCauseIsActualGround m w p.CausesIn p.esse)
    (hExists : ActOfEsseSufficesForExistenceAt m.ontic p.InAct p.esse w)
    (hConcrete : EsseInReIsConcrete m p.InAct p.esse) :
    NoInfiniteActualEsseCauseRegress p := by
  refine wellFounded_of_predecessorInclusion (ActualConcrete m w) (m.grounds w) _ hWF ?_
  intro c x h
  obtain ⟨hne, hc, hx, hcause⟩ := h
  have hcA : ActualConcrete m w c := ⟨hConcrete c hc, hExists c hc⟩
  exact ⟨hcA, hGround c x hcA ⟨hConcrete x hx, hExists x hx⟩ hne hcause⟩

/-- Strength step: cb1cdea9 implies its weak version. -/
theorem actualEsseCauseIsActualGroundOfEsseCause {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    ActualEsseCauseIsActualGround m w CausesIn esse :=
  fun c x _ hx hne hcause => (h c x hne hx hcause).2.2

/-- Actual grounding into esse causing: a ground between actual concreta is a
distinct cause of the grounded thing's esse (bridge), and both are in act of
esse because they exist at `w`. Well-foundedness of actual causes of being
transfers to grounding among actual concreta. -/
theorem actualGroundingWFOfEsseRegress {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hRegress : NoInfiniteActualEsseCauseRegress p)
    (hGround : ActualGroundIsDistinctEsseCause m w p.CausesIn p.esse)
    (hInAct : ExistingInActAt m.ontic p.InAct p.esse w) :
    ActualGroundingWF m w := by
  refine Subrelation.wf (r := InvImage (ActualEsseCause p) (fun a : {x // ActualConcrete m w x} => a.1))
    ?_ (InvImage.wf _ hRegress)
  intro a b hab
  obtain ⟨hne, hcause⟩ := hGround a.1 b.1 a.2 b.2 hab
  exact ⟨hne, hInAct a.1 a.2.2, hInAct b.1 b.2.2, hcause⟩

/-- Simple priority into actual grounding: what is simply prior to x is other
than x (irreflexivity) and hence (bridge) an actual concrete ground of x.
Well-foundedness of grounding among actual concreta transfers to simple
priority on the whole carrier. -/
theorem simplePriorityWFOfActualGroundingWF {W B T R : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w)
    (hPrior : SimplyPriorIsActualConcreteGround m w F.PriorSimply)
    (hIrrefl : NothingPriorToItselfReading F.PriorSimply) :
    SimplePriorityWellFounded F.PriorSimply := by
  refine wellFounded_of_predecessorInclusion (ActualConcrete m w) (m.grounds w) _ hWF ?_
  intro y x h
  have hne : y ≠ x := fun e => hIrrefl x (e ▸ h)
  have g := hPrior y x hne h
  exact ⟨⟨g.1, g.2.1⟩, g.2.2⟩

/-- Per se efficient causing into per se esse causing: every per se link is a
per se actual cause of being (bridge), so accessibility along per se actual
causes of being gives accessibility along per se efficient-cause links. -/
theorem perSeEfficientSeriesOfPerSeEsseRegress {B P R : Type}
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (AsCaused CausesAsCaused : B → B → Prop)
    (hRegress : NoInfinitePerSeActualEsseCauseRegress p AsCaused)
    (hBridge : PerSeEfficientCausesArePerSeEsseCauses p AsCaused CausesAsCaused) :
    NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused :=
  fun x => Subrelation.accessible (fun h => hBridge _ _ h) (hRegress.apply x)

/-! ## Controls -/

theorem true_ne_false' : true ≠ false := fun h => Bool.noConfusion h

theorem cyc_not_wf : ¬ WellFounded cyc :=
  not_wellFounded_of_twoCycle true false true_ne_false' (fun h => true_ne_false' h.symm)

theorem noRel_wf {B : Type} : WellFounded (noRel : B → B → Prop) :=
  ⟨fun x => ⟨x, fun _ h => h.elim⟩⟩

theorem edgeTF_wf : WellFounded edgeTF :=
  wellFounded_of_singleEdge true false true_ne_false' (fun _ _ h => h)

theorem mCyc_not_agwf : ¬ ActualGroundingWF mCyc () :=
  not_wellFounded_of_twoCycle (R := fun a b : {x // ActualConcrete mCyc () x} => mCyc.grounds () a.1 b.1)
    ⟨true, trivial, trivial⟩ ⟨false, trivial, trivial⟩ true_ne_false' (fun h => true_ne_false' h.symm)

theorem pCyc_not_regress : ¬ NoInfiniteActualEsseCauseRegress pCyc :=
  not_wellFounded_of_twoCycle (R := ActualEsseCause pCyc) true false
    ⟨true_ne_false', trivial, trivial, true_ne_false'⟩
    ⟨fun h => true_ne_false' h.symm, trivial, trivial, fun h => true_ne_false' h.symm⟩

theorem pNone_regress : NoInfiniteActualEsseCauseRegress pNone :=
  ⟨fun x => ⟨x, fun _ h => h.2.2.2.elim⟩⟩

theorem pIdle_regress : NoInfiniteActualEsseCauseRegress pIdle :=
  ⟨fun x => ⟨x, fun _ h => h.2.1.elim⟩⟩

theorem pEdge_regress : NoInfiniteActualEsseCauseRegress pEdge :=
  wellFounded_of_singleEdge true false true_ne_false' (fun _ _ h => h.2.2.2)

theorem esseRegressControls : EsseRegressControls := by
  refine ⟨⟨mCyc_not_agwf, ?_, fun _ _ => trivial, fun _ _ => trivial, pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, fun _ _ => trivial, fun _ _ => trivial,
      pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, ?_, fun _ _ => trivial, pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, fun _ _ => trivial, ?_, pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ edgeTF_wf, ?_, fun _ _ => trivial, fun _ _ => trivial,
      pEdge_regress, true_ne_false', trivial, trivial, rfl, rfl⟩⟩
  · exact fun _ _ hne _ h => ⟨trivial, trivial, h⟩
  · exact fun h => (h true false true_ne_false' ⟨trivial, trivial⟩ true_ne_false').2.2
  · exact fun _ _ _ hx _ => hx.2.elim
  · exact fun h => h true trivial
  · exact fun _ _ _ hx _ => hx.1.elim
  · exact fun h => h true trivial
  · exact fun _ _ _ _ h => ⟨trivial, trivial, h⟩

theorem weakEsseRegressControls : WeakEsseRegressControls := by
  refine ⟨⟨mCyc_not_agwf, fun _ _ _ _ _ h => h, fun _ _ => trivial, fun _ _ => trivial,
      pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, fun _ _ => trivial, fun _ _ => trivial,
      pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, ?_, fun _ _ => trivial, pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, fun _ _ => trivial, ?_, pCyc_not_regress⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ edgeTF_wf, fun _ _ _ _ _ h => h, fun _ _ => trivial,
      fun _ _ => trivial, pEdge_regress, true_ne_false', trivial, trivial, rfl, rfl⟩⟩
  · exact fun h => h true false ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ true_ne_false' true_ne_false'
  · exact fun _ _ _ hx _ _ => hx.2.elim
  · exact fun h => h true trivial
  · exact fun _ _ _ hx _ _ => hx.1.elim
  · exact fun h => h true trivial

theorem converseControls : ConverseControls := by
  refine ⟨⟨pCyc_not_regress, fun _ _ _ _ h => ⟨h, h⟩, fun _ _ => trivial, mCyc_not_agwf⟩,
    ⟨pNone_regress, ?_, fun _ _ => trivial, mCyc_not_agwf⟩,
    ⟨pIdle_regress, fun _ _ _ _ h => ⟨h, h⟩, ?_, mCyc_not_agwf⟩,
    ⟨pEdge_regress, ?_, fun _ _ => trivial, actualGroundingWF_of_wellFounded _ _ edgeTF_wf⟩,
    ⟨fun _ _ _ _ h => h.elim, fun _ _ => trivial, fun _ _ => trivial,
      fun _ _ _ h => h.elim, fun _ h => h, pNone_regress, noRel_wf, mCyc_not_agwf⟩⟩
  · exact fun h => (h true false ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ true_ne_false').2
  · exact fun h => h true trivial
  · intro a b _ _ h
    refine ⟨?_, h⟩
    intro e
    have h1 : a = true := h.1
    have h2 : b = false := h.2
    exact true_ne_false' (h1.symm.trans (e.trans h2))

theorem priorityControls : PriorityControls := by
  refine ⟨⟨mCyc_not_agwf, fun _ _ _ h => ⟨trivial, trivial, h⟩, fun _ h => h rfl, cyc_not_wf⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, fun _ h => h rfl, cyc_not_wf⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ noRel_wf, ?_, ?_, ?_⟩,
    ⟨actualGroundingWF_of_wellFounded _ _ edgeTF_wf, fun _ _ _ h => ⟨trivial, trivial, h⟩, ?_,
      edgeTF_wf, rfl, rfl⟩⟩
  · exact fun h => (h true false true_ne_false' true_ne_false').2.2
  · intro y x hne h
    exact (hne (h.1.trans h.2.symm)).elim
  · exact fun h => h true ⟨rfl, rfl⟩
  · exact not_wellFounded_of_loop (R := fun a b : Bool => a = true ∧ b = true) true ⟨rfl, rfl⟩
  · intro x h
    exact true_ne_false' (h.1.symm.trans h.2)

theorem secundaControls : SecundaControls := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, fun _ _ h => ⟨⟨h, trivial, trivial, h⟩, trivial⟩, ?_⟩,
    ⟨?_, ?_, fun x => edgeTF_wf.apply x, rfl, rfl⟩⟩
  · exact Subrelation.wf (fun h => h.1) pNone_regress
  · exact fun h => (h true false true_ne_false').1.2.2.2
  · exact fun h => cyc_not_wf ⟨h⟩
  · exact not_wellFounded_of_twoCycle true false
      ⟨⟨true_ne_false', trivial, trivial, true_ne_false'⟩, trivial⟩
      ⟨⟨fun h => true_ne_false' h.symm, trivial, trivial, fun h => true_ne_false' h.symm⟩, trivial⟩
  · exact fun h => cyc_not_wf ⟨h⟩
  · exact Subrelation.wf (fun h => h.1) pEdge_regress
  · intro c x h
    refine ⟨⟨?_, trivial, trivial, h⟩, trivial⟩
    intro e
    exact true_ne_false' (h.1.symm.trans (e.trans h.2))

theorem edge10_wf : WellFounded edge10 :=
  wellFounded_of_singleEdge 1 0 (fun h => Nat.noConfusion h) (fun _ _ h => h)

theorem ascentLimit : AscentLimit := by
  refine ⟨actualGroundingWF_of_wellFounded _ _ edge10_wf, fun _ _ _ _ h => ⟨trivial, trivial, h⟩,
    ?_, fun _ _ _ h => ⟨trivial, trivial, h⟩, ?_, ?_, fun _ _ => trivial, fun _ _ => trivial,
    fun _ _ => trivial, ?_, edge10_wf, ⟨1, 0, rfl⟩, ?_, ?_⟩
  · intro a b _ _ h
    refine ⟨?_, h⟩
    intro e
    have h1 : a = 1 := h.1
    have h2 : b = 0 := h.2
    exact Nat.noConfusion (h1.symm.trans (e.trans h2))
  · intro a b _ _ h
    have h1 : a = 1 := h.1
    have h2 : b = 0 := h.2
    subst h1 h2
    rfl
  · intro r x hMax
    exact (hMax.2 (x + 1) rfl).elim
  · exact wellFounded_of_singleEdge 1 0 (fun h => Nat.noConfusion h) (fun _ _ h => h.2.2.2)
  · intro h
    exact not_wellFounded_succ
      (Subrelation.wf (r := fun y x : Nat => ActualConcrete mNat () y ∧ ActualConcrete mNat () x ∧
        succGrade () y x) (fun hs => ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, hs⟩) h)
  · exact not_wellFounded_succ

end TruthCore.Results.Causality.OneDependenceOrder
