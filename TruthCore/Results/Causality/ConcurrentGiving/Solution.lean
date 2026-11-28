module

public import TruthCore.Causality.ConcurrentGiving
public import TruthCore.Results.Causality.PresentReceipt.Solution
public import TruthCore.Results.Causality.TimeSymmetricGiving.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ConcurrentGiving

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FrameAdapters (giving)
open TruthCore.Causality.ConcurrentGiving
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized ConcurrentlyActualizedByAnother)
open TruthCore.Causality.RelationalReceipt
open TruthCore.Causality.TimeSymmetricGiving
open TruthCore.Causality.PresentReceipt

private theorem distinctOfConcurrent {W B T R P : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop)
    (hConcurrent : ConcurrentlyActualized F.history (giving F) E)
    (hNoSelf : NoReceivedSelfGiving F E) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  intro v x t z hz ht
  obtain ⟨g, hg⟩ := hConcurrent v x t z hz ht
  refine ⟨g, ?_, hg⟩
  intro hEq
  exact hNoSelf v x t z hz ht (hEq ▸ hg)

theorem distinctOfMomentaryExplanation {W B T R P X : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop) (expl : PresenceExplanation W B T X)
    (hPSR : MomentaryPSR F.history expl E)
    (hBridge : ExplanationNeedsGiver F.history (giving F) expl E)
    (hNoSelf : NoReceivedSelfGiving F E) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  exact distinctOfConcurrent F E
    (TruthCore.Results.Causality.TimeSymmetricGiving.concurrentOfMomentaryPSR
      F.history (giving F) expl E hPSR hBridge) hNoSelf

theorem distinctOfOriginTerm {W B T R P : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop) (O : OriginRelation W B T)
    (hAccompanies : RelationAccompaniesEsse F.history O E)
    (hGives : TermGives (giving F) O)
    (hIrreflexive : Irreflexive O) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  intro v x t z hz ht
  obtain ⟨g, hg⟩ := hAccompanies v x z t hz ht
  exact ⟨g, hIrreflexive v x g t hg, hGives v x g t hg⟩

theorem distinctOfPresentReceipt {W B T R P : Type}
    (F : CausalityFrame W B T R) (E : B → P → Prop) (receipt : Receipt W B T P)
    (hPresent : ReceptionIsPresent F.history receipt E)
    (hCorrelative : ReceivingIsCorrelativeWithGiving (giving F) receipt)
    (hNoSelf : NoReceivedSelfGiving F E) :
    ConcurrentlyActualizedByAnother F.history (giving F) E := by
  exact distinctOfConcurrent F E
    (TruthCore.Results.Causality.PresentReceipt.concurrentOfPresentReceipt
      F.history (giving F) receipt E hPresent hCorrelative) hNoSelf

open Control
open TruthCore.Causality.ConcurrentActualization (CausesOfBeingConcur)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Causality.SustainingCausation
open TruthCore.Modal.TemporalHistory (BeginsAt)

private theorem noGivingAtLater (g : Bool) :
    ¬ inertia.GivesAt () g false true :=
  fun hg => Bool.noConfusion hg.2.2

theorem jointInertia : Control.JointInertia := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v x t z hx _
    cases t
    · exact ⟨Sum.inl true, rfl, hx, rfl⟩
    · exact ⟨Sum.inr false, Bool.false_lt_true, trivial, fun _ _ _ h => h⟩
  · exact fun _ _ _ _ _ _ h => False.elim (h trivial)
  · exact fun _ _ _ _ hx _ => ⟨true, hx, rfl⟩
  · exact fun _ _ _ _ hr => ⟨⟨(), hr.1⟩, trivial⟩
  · intro _ x g _ hr hEq
    exact Bool.noConfusion (hr.2.symm.trans (hEq.trans hr.1))
  · exact fun _ _ _ _ _ => trivial
  · exact fun _ _ _ _ hx ht => ⟨hx, ht⟩
  · intro _ x _ _ hx _ hGive
    exact Bool.noConfusion (hGive.1.symm.trans hx)
  · exact fun _ _ _ _ _ => trivial
  · exact fun _ _ _ _ _ _ hc hg => ⟨hc.1, hc.2, hg.2.2⟩
  · intro h
    obtain ⟨g, hg⟩ := h () false true () (Sum.inr false) rfl trivial
      ⟨Bool.false_lt_true, trivial, fun _ _ _ hd => hd⟩
    exact noGivingAtLater g hg
  · exact fun h => noGivingAtLater true (h () false true true ⟨rfl, rfl⟩)
  · intro h
    obtain ⟨g, hg⟩ := h () () false true ⟨rfl, trivial⟩
    exact noGivingAtLater g hg
  · intro h
    obtain ⟨g, hg⟩ := h () false true () rfl trivial
    exact noGivingAtLater g hg
  · exact fun h => noGivingAtLater true
      ((h () true false ⟨rfl, rfl⟩ ⟨false, trivial⟩).2 true trivial)

theorem onsetOnlyPassion : Control.OnsetOnlyPassion := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ x _ b hx hb
    cases b
    · exact ⟨hx, true, rfl, hx, rfl⟩
    · exact False.elim (hb.2 false Bool.false_lt_true trivial)
  · exact fun _ _ _ _ hr => hr.2
  · intro h
    obtain ⟨g, hg⟩ := (h () false () true rfl trivial).2
    exact noGivingAtLater g hg
  · intro h
    obtain ⟨g, hg⟩ := h () false true () rfl trivial
    exact noGivingAtLater g hg

end TruthCore.Results.Causality.ConcurrentGiving
