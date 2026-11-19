module

public import TruthCore.Causality.PrimaViaCertificates
public import TruthCore.Logic.Configuration
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Alternatives.NightCosmogony
public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.GradedSupportFoundation
public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Logic.CogitoConcrete
public import TruthCore.Causality.FiniteBranching
public import TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-!
# Prima via certificates (#1751)

Certificates for the 2026-11-18 cluster assessments of the prima via route to
GOD_4 exists: three verified inconsistent premise sets (the factive
`CausesIn` set, reciprocal cross-respect moving against respect-free simple
priority, and the self-dependence package), the strength step from the
every-world distinct-esse-cause bridge to its actual-world sibling, the bypass
from well-founded causal predecessors to the per se regress premise, and the
converse selection that rebinds well-founded predecessors to the per se regress
premise. Every proof is constructive and uses no axiom.

An incompatibility certifies only that its explicit premises cannot all hold
under one interpretation of their shared parameters. It rejects no preferred
member and establishes nothing about which premise is false.
-/

@[expose] public section

namespace TruthCore.Results.Causality.PrimaViaCertificates

open TruthCore.Logic (ConfigurationFalse)
open TruthCore.Causality.PrimaViaCertificates
open TruthCore.Latin.Aquinas.SummaTheologiae
  (SomethingIsMovedReading ReducedOnlyByABeingInActReading MovedOnlyAsInPotencyReading
   NothingPriorToItselfReading NoInfinitePerSeEfficientCauseSeriesReading)
open TruthCore.Causality.CausalMapsBatch1
  (MoverCausesWhatItMovesTo CausedPerfectionIsHad PriorityRequiresNonmutualDependence)
open TruthCore.Alternatives.NightCosmogony (ActualMoverIsSimplyPriorReading)
open TruthCore.Alternatives.ActPotencyRegress (SimplePriorityTransitiveReading)
open TruthCore.Causality.Round2PerfectionPrimacy (IndependenceAllowsBeingWithout)
open TruthCore.Causality.Round2Grounding (ActualDependenceIsGrounding)
open TruthCore.Causality.GradedSupportFoundation
  (ActualGroundIsDistinctEsseCause SupportIsDistinctEsseCauseEverywhere)
open TruthCore.Causality.ReflexiveDependenceScope (ActualDistinctDependenceIsGrounding)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Causality.FiniteBranching (WellFoundedPredecessors)
open TruthCore.Case.Catholicism.StageOne.CausalFinitism (PerSeLinksIncluded)

/-! ## 1. The factive `CausesIn` set, under adopted potency -/

/-- Under adopted potency (`InPotency x r := CanBe x r ∧ ¬ InAct x r`), the
observation of motion, reduction only by a being in act, motion only as in
potency, "the mover causes what it moves to" and "a caused perfection is had"
cannot all hold with one `CausesIn` and one `InAct`. Some `x` is moved in `r`;
a mover `y` of `x` in `r` exists; `y` then causes `x`'s being `r`, so `x` is in
act in `r`; but `x`, being moved in `r`, is in adopted potency in `r`, so it is
not in act in `r`. The in-act clause of the reduction premise is not used.
No excluded middle is used. -/
theorem causesInIncompatible {Being Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn CausesIn : Being → Being → Respect → Prop)
    (InAct CanBe : Being → Respect → Prop)
    (hMoved : SomethingIsMovedReading MovedIn)
    (hReduced : ReducedOnlyByABeingInActReading MovedIn MovesIn InAct)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe))
    (hCauses : MoverCausesWhatItMovesTo MovesIn CausesIn)
    (hHad : CausedPerfectionIsHad CausesIn InAct) :
    ConfigurationFalse := by
  obtain ⟨x, r, hx⟩ := hMoved
  obtain ⟨y, hy, -⟩ := hReduced x r hx
  exact (hPotency x r hx).2 (hHad y x r (hCauses y x r hy))

namespace CausesInControl

open TruthCore.Causality.PrimaViaCertificates.Control.CausesIn

theorem potency : MovedOnlyAsInPotencyReading MovedIn Pot :=
  fun _ _ h => ⟨trivial, fun h' => Bool.noConfusion (h.symm.trans h')⟩

/-- Dropping "the mover causes what it moves to": the other four hold with an
empty `CausesIn`, and the dropped premise fails. -/
theorem withoutMoverCauses :
    SomethingIsMovedReading MovedIn ∧
    ReducedOnlyByABeingInActReading MovedIn MovesIn InAct ∧
    MovedOnlyAsInPotencyReading MovedIn Pot ∧
    CausedPerfectionIsHad Never2 InAct ∧
    ¬ MoverCausesWhatItMovesTo MovesIn Never2 :=
  ⟨⟨false, (), rfl⟩, fun _ _ h => ⟨true, ⟨rfl, h⟩, rfl⟩, potency,
   fun _ _ _ h => h.elim, fun h => h true false () ⟨rfl, rfl⟩⟩

/-- Dropping "a caused perfection is had": causing is moving, and the moved
thing does not yet have the perfection. -/
theorem withoutCausedPerfectionHad :
    SomethingIsMovedReading MovedIn ∧
    ReducedOnlyByABeingInActReading MovedIn MovesIn InAct ∧
    MovedOnlyAsInPotencyReading MovedIn Pot ∧
    MoverCausesWhatItMovesTo MovesIn MovesIn ∧
    ¬ CausedPerfectionIsHad MovesIn InAct :=
  ⟨⟨false, (), rfl⟩, fun _ _ h => ⟨true, ⟨rfl, h⟩, rfl⟩, potency,
   fun _ _ _ h => h, fun h => Bool.noConfusion (h true false () ⟨rfl, rfl⟩)⟩

/-- Dropping the observation of motion: nothing is moved. -/
theorem withoutMotion :
    ReducedOnlyByABeingInActReading Never1 Never2 InAct ∧
    MovedOnlyAsInPotencyReading Never1 Pot ∧
    MoverCausesWhatItMovesTo Never2 Never2 ∧
    CausedPerfectionIsHad Never2 InAct ∧
    ¬ SomethingIsMovedReading Never1 :=
  ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ _ h => h, fun _ _ _ h => h.elim,
   fun ⟨_, _, h⟩ => h⟩

/-- Dropping reduction by a being in act: something is moved by nothing. -/
theorem withoutReduction :
    SomethingIsMovedReading MovedIn ∧
    MovedOnlyAsInPotencyReading MovedIn Pot ∧
    MoverCausesWhatItMovesTo Never2 Never2 ∧
    CausedPerfectionIsHad Never2 InAct ∧
    ¬ ReducedOnlyByABeingInActReading MovedIn Never2 InAct :=
  ⟨⟨false, (), rfl⟩, potency, fun _ _ _ h => h, fun _ _ _ h => h.elim,
   fun h => by obtain ⟨_, hy, -⟩ := h false () rfl; exact hy⟩

/-- Dropping motion only as in potency: everything is in act, and the moved
thing is not in adopted potency. -/
theorem withoutPotency :
    SomethingIsMovedReading MovedIn ∧
    ReducedOnlyByABeingInActReading MovedIn MovesIn AllAct ∧
    MoverCausesWhatItMovesTo MovesIn MovesIn ∧
    CausedPerfectionIsHad MovesIn AllAct ∧
    ¬ MovedOnlyAsInPotencyReading MovedIn
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency AllAct CanBe) :=
  ⟨⟨false, (), rfl⟩, fun _ _ h => ⟨true, ⟨rfl, h⟩, trivial⟩, fun _ _ _ h => h,
   fun _ _ _ _ => trivial, fun h => (h false () rfl).2 trivial⟩

end CausesInControl

/-- Every single deletion from the five-member core has a model in the same
Bool/Unit vocabulary under adopted potency. -/
theorem causesInControls :
    (SomethingIsMovedReading Control.CausesIn.MovedIn ∧
      ReducedOnlyByABeingInActReading Control.CausesIn.MovedIn Control.CausesIn.MovesIn
        Control.CausesIn.InAct ∧
      MovedOnlyAsInPotencyReading Control.CausesIn.MovedIn Control.CausesIn.Pot ∧
      CausedPerfectionIsHad Control.CausesIn.Never2 Control.CausesIn.InAct ∧
      ¬ MoverCausesWhatItMovesTo Control.CausesIn.MovesIn Control.CausesIn.Never2) ∧
    (SomethingIsMovedReading Control.CausesIn.MovedIn ∧
      ReducedOnlyByABeingInActReading Control.CausesIn.MovedIn Control.CausesIn.MovesIn
        Control.CausesIn.InAct ∧
      MovedOnlyAsInPotencyReading Control.CausesIn.MovedIn Control.CausesIn.Pot ∧
      MoverCausesWhatItMovesTo Control.CausesIn.MovesIn Control.CausesIn.MovesIn ∧
      ¬ CausedPerfectionIsHad Control.CausesIn.MovesIn Control.CausesIn.InAct) ∧
    (ReducedOnlyByABeingInActReading Control.CausesIn.Never1 Control.CausesIn.Never2
        Control.CausesIn.InAct ∧
      MovedOnlyAsInPotencyReading Control.CausesIn.Never1 Control.CausesIn.Pot ∧
      MoverCausesWhatItMovesTo Control.CausesIn.Never2 Control.CausesIn.Never2 ∧
      CausedPerfectionIsHad Control.CausesIn.Never2 Control.CausesIn.InAct ∧
      ¬ SomethingIsMovedReading Control.CausesIn.Never1) ∧
    (SomethingIsMovedReading Control.CausesIn.MovedIn ∧
      MovedOnlyAsInPotencyReading Control.CausesIn.MovedIn Control.CausesIn.Pot ∧
      MoverCausesWhatItMovesTo Control.CausesIn.Never2 Control.CausesIn.Never2 ∧
      CausedPerfectionIsHad Control.CausesIn.Never2 Control.CausesIn.InAct ∧
      ¬ ReducedOnlyByABeingInActReading Control.CausesIn.MovedIn Control.CausesIn.Never2
        Control.CausesIn.InAct) ∧
    (SomethingIsMovedReading Control.CausesIn.MovedIn ∧
      ReducedOnlyByABeingInActReading Control.CausesIn.MovedIn Control.CausesIn.MovesIn
        Control.CausesIn.AllAct ∧
      MoverCausesWhatItMovesTo Control.CausesIn.MovesIn Control.CausesIn.MovesIn ∧
      CausedPerfectionIsHad Control.CausesIn.MovesIn Control.CausesIn.AllAct ∧
      ¬ MovedOnlyAsInPotencyReading Control.CausesIn.MovedIn
        (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency
          Control.CausesIn.AllAct Control.CausesIn.CanBe)) :=
  ⟨CausesInControl.withoutMoverCauses, CausesInControl.withoutCausedPerfectionHad,
   CausesInControl.withoutMotion, CausesInControl.withoutReduction,
   CausesInControl.withoutPotency⟩

/-! ## 2. Reciprocal cross-respect moving and respect-free simple priority -/

/-- Respect-free simple priority from actual moving (6ca87431), transitivity
(7ad36aca), irreflexivity (32d77f18) and one reciprocal cross-respect moving
case cannot all hold for one `PriorSimply`. The case gives `PriorSimply y x`
and `PriorSimply x y`; transitivity gives `PriorSimply y y`. -/
theorem reciprocityIncompatible {Being Respect : Type}
    (InAct InPotency : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hPrior : ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply)
    (hTrans : SimplePriorityTransitiveReading PriorSimply)
    (hIrrefl : NothingPriorToItselfReading PriorSimply)
    (hCase : ReciprocalCrossRespectMoving InAct InPotency MovesIn) :
    ConfigurationFalse := by
  obtain ⟨y, x, r, r', hne, hy, hx, hyx, hx', hy', hxy⟩ := hCase
  exact hIrrefl y (hTrans y x y (hPrior y x r hx hyx hy hne)
    (hPrior x y r' hy' hxy hx' (Ne.symm hne)))

/-- The same case with the priority-requires-nonmutual-dependence bridge
(47aff057) in place of transitivity and irreflexivity: the two priorities give
`D x y ∧ ¬ D y x` and `D y x ∧ ¬ D x y`. -/
theorem reciprocityIncompatibleViaDependence {Being Respect : Type}
    (InAct InPotency : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply DependsForBeing : Being → Being → Prop)
    (hPrior : ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing)
    (hCase : ReciprocalCrossRespectMoving InAct InPotency MovesIn) :
    ConfigurationFalse := by
  obtain ⟨y, x, r, r', hne, hy, hx, hyx, hx', hy', hxy⟩ := hCase
  exact (hReq y x (hPrior y x r hx hyx hy hne)).2
    (hReq x y (hPrior x y r' hy' hxy hx' (Ne.symm hne))).1

namespace ReciprocityControl

open TruthCore.Causality.PrimaViaCertificates.Control.Reciprocity

theorem case : ReciprocalCrossRespectMoving InAct InPotency MovesIn :=
  ⟨true, false, true, false, Bool.noConfusion, rfl, Bool.noConfusion,
   ⟨rfl, Bool.noConfusion⟩, rfl, Bool.noConfusion, ⟨rfl, Bool.noConfusion⟩⟩

end ReciprocityControl

/-- Every single deletion from the four-member reciprocity core has a model on
two beings and two respects, so the core is inclusion-minimal in this
vocabulary. These are facts about the stated interpretations only. -/
theorem reciprocityControls :
    -- without the case: nothing moves
    (ActualMoverIsSimplyPriorReading Control.Reciprocity.NeverAct Control.Reciprocity.NeverAct
        Control.Reciprocity.NeverMoves Control.Reciprocity.NeverPrior ∧
      SimplePriorityTransitiveReading Control.Reciprocity.NeverPrior ∧
      NothingPriorToItselfReading Control.Reciprocity.NeverPrior ∧
      ¬ ReciprocalCrossRespectMoving Control.Reciprocity.NeverAct Control.Reciprocity.NeverAct
        Control.Reciprocity.NeverMoves) ∧
    -- without priority from actual moving: no priority at all
    (SimplePriorityTransitiveReading Control.Reciprocity.NeverPrior ∧
      NothingPriorToItselfReading Control.Reciprocity.NeverPrior ∧
      ReciprocalCrossRespectMoving Control.Reciprocity.InAct Control.Reciprocity.InPotency
        Control.Reciprocity.MovesIn ∧
      ¬ ActualMoverIsSimplyPriorReading Control.Reciprocity.InAct Control.Reciprocity.InPotency
        Control.Reciprocity.MovesIn Control.Reciprocity.NeverPrior) ∧
    -- without transitivity: priority is distinctness
    (ActualMoverIsSimplyPriorReading Control.Reciprocity.InAct Control.Reciprocity.InPotency
        Control.Reciprocity.MovesIn Control.Reciprocity.Distinct ∧
      NothingPriorToItselfReading Control.Reciprocity.Distinct ∧
      ReciprocalCrossRespectMoving Control.Reciprocity.InAct Control.Reciprocity.InPotency
        Control.Reciprocity.MovesIn ∧
      ¬ SimplePriorityTransitiveReading Control.Reciprocity.Distinct) ∧
    -- without irreflexivity: everything is prior to everything
    (ActualMoverIsSimplyPriorReading Control.Reciprocity.InAct Control.Reciprocity.InPotency
        Control.Reciprocity.MovesIn Control.Reciprocity.AlwaysPrior ∧
      SimplePriorityTransitiveReading Control.Reciprocity.AlwaysPrior ∧
      ReciprocalCrossRespectMoving Control.Reciprocity.InAct Control.Reciprocity.InPotency
        Control.Reciprocity.MovesIn ∧
      ¬ NothingPriorToItselfReading Control.Reciprocity.AlwaysPrior) :=
  ⟨⟨fun _ _ _ _ h => h.elim, fun _ _ _ h => h.elim, fun _ h => h,
     fun ⟨_, _, _, _, _, h, _⟩ => h⟩,
   ⟨fun _ _ _ h => h.elim, fun _ h => h, ReciprocityControl.case,
     fun h => h true false true Bool.noConfusion ⟨rfl, Bool.noConfusion⟩ rfl Bool.noConfusion⟩,
   ⟨fun _ _ _ _ _ _ hne => hne, fun _ h => h rfl, ReciprocityControl.case,
     fun h => h true false true Bool.noConfusion Bool.noConfusion rfl⟩,
   ⟨fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, ReciprocityControl.case,
     fun h => h true trivial⟩⟩

/-! ## 3. The self-dependence package -/

/-- Independence allows being-without (8ab3d114), nothing can be without itself,
the unrestricted dependence-to-grounding bridge (2e248016) and the actual-world
distinct-esse-cause bridge (98efaa9e) exclude every actual concretum (56f68b40)
at the reading world. For an actual concretum `x`: if `D x x`, the bridge makes
`x` ground itself at `w`, and the distinct-cause bridge gives `x ≠ x`; so
`¬ D x x`. Then independence gives `CanBeWithout x x`, which the postulate
denies. Constructive: no excluded middle is used. -/
theorem selfDependenceIncompatible {W B R : Type} (m : Profile W B) (w : W)
    (DependsForBeing CanBeWithout : B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hIndep : IndependenceAllowsBeingWithout DependsForBeing CanBeWithout)
    (hSelf : NothingCanBeWithoutItself CanBeWithout)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing)
    (hDistinct : ActualGroundIsDistinctEsseCause m w CausesIn esse)
    (hActual : InhabitedConcreteAt m.ontic m.concrete w) :
    ConfigurationFalse := by
  obtain ⟨x, hc, he⟩ := hActual
  have hAC : ActualConcrete m w x := ⟨hc, he⟩
  have hNotD : ¬ DependsForBeing x x := fun hD =>
    (hDistinct x x hAC hAC (hGround x x hAC hAC hD)).1 rfl
  exact hSelf x (hIndep x x hNotD)

/-- Strength step: the every-world distinct-esse-cause bridge (402cf70f)
implies its actual-world sibling (98efaa9e) at any reading world, by
instantiating its world quantifier at that world. -/
theorem actualGroundDistinctOfEverywhere {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hEverywhere : SupportIsDistinctEsseCauseEverywhere m CausesIn esse) :
    ActualGroundIsDistinctEsseCause m w CausesIn esse :=
  fun a b ha hb hg => hEverywhere w a b ha.1 hb.1 ha.2 hg

/-- A joint finite model of one repaired package: the distinct-relata
dependence-to-grounding bridge (a8298fbd) in place of the unrestricted one,
with independence allows being-without, nothing can be without itself, both
distinct-esse-cause bridges, an actual concretum and a nonempty strict part of
dependence (`true` depends on `false`). The unrestricted bridge fails in it,
since `false` depends on itself but does not ground itself. -/
theorem repairedPackageModel :
    IndependenceAllowsBeingWithout Control.Repair.DependsForBeing Control.Repair.CanBeWithout ∧
    NothingCanBeWithoutItself Control.Repair.CanBeWithout ∧
    ActualDistinctDependenceIsGrounding Control.Repair.profile () Control.Repair.DependsForBeing ∧
    ActualGroundIsDistinctEsseCause Control.Repair.profile () Control.Repair.CausesIn () ∧
    SupportIsDistinctEsseCauseEverywhere Control.Repair.profile Control.Repair.CausesIn () ∧
    InhabitedConcreteAt Control.Repair.profile.ontic Control.Repair.profile.concrete () ∧
    Control.Repair.DependsForBeing true false ∧
    ¬ Control.Repair.DependsForBeing false true ∧
    ¬ ActualDependenceIsGrounding Control.Repair.profile () Control.Repair.DependsForBeing :=
  ⟨fun _ _ h => h,
   fun _ h => h (Or.inl rfl),
   fun c x hne _ _ hD => by
     rcases hD with h | ⟨hx, hc⟩
     · exact absurd h.symm hne
     · exact ⟨hc, hx⟩,
   fun _ _ _ _ hg => ⟨fun h => Bool.noConfusion (hg.1.symm.trans (h.trans hg.2)), hg⟩,
   fun _ _ _ _ _ _ hg => ⟨fun h => Bool.noConfusion (hg.1.symm.trans (h.trans hg.2)), hg⟩,
   ⟨false, trivial, trivial⟩,
   Or.inr ⟨rfl, rfl⟩,
   fun h => by
     rcases h with h | ⟨h, _⟩
     · exact Bool.noConfusion h
     · exact Bool.noConfusion h,
   fun h => Bool.noConfusion (h false false ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
     (Or.inl rfl)).2⟩

/-! ## 4. Bypass B1 and the regress rebinding -/

/-- Bypass B1: if the studied causal-history relation is well-founded
(42890b45) and every per se efficient-cause edge is an edge of it (f10d5632),
then every being is accessible along per se links (97f5850f). A subrelation of a
well-founded relation is well-founded (`Subrelation.accessible`). -/
theorem perSeRegressOfWellFoundedHistory {Being : Type}
    (cause perSe : Being → Being → Prop)
    (hWF : WellFoundedPredecessors cause)
    (hIncluded : PerSeLinksIncluded cause perSe) :
    NoInfinitePerSeEfficientCauseSeriesReading perSe :=
  fun x => Subrelation.accessible (fun h => hIncluded h) (hWF.apply x)

/-- Regress rebinding: if no per se ordered series of efficient causes goes on
to infinity (97f5850f) and every edge of the studied causal history is a per se
link, then the studied relation is well-founded (42890b45). Neither simple
priority nor its well-foundedness enters. -/
theorem wellFoundedHistoryOfPerSeRegress {Being : Type}
    (cause perSe : Being → Being → Prop)
    (hRegress : NoInfinitePerSeEfficientCauseSeriesReading perSe)
    (hPerSe : HistoryEdgesArePerSeLinks cause perSe) :
    WellFoundedPredecessors cause :=
  ⟨fun x => Subrelation.accessible (fun h => hPerSe h) (hRegress x)⟩

end TruthCore.Results.Causality.PrimaViaCertificates
