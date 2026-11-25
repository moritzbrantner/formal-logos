module

public import TruthCore.Explanation.BruteContingencyParity

/-! Existence consequences of a sound intrinsic reason and necessary role occupancy. -/

@[expose] public section

namespace TruthCore.Explanation.FoundationalExistenceApplications

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Explanation.BruteContingencyParity (natureModel)
open TruthCore.Explanation.ExistencePSR (Sound)

theorem ownNatureNecessaryOfSound {W B T R P : Type}
    (F : CausalityFrame W B T R) (essenceOf esseOf : B → P)
    (hSound : Sound (natureModel F essenceOf esseOf))
    (x : B) (hIdentity : ¬ esseOf x ≠ essenceOf x) :
    ∀ v, F.history.ontic.ExistsAt v x :=
  fun v => hSound v x (.intrinsic x) ⟨rfl, hIdentity⟩

theorem occupiedRoleAtAbsence {W B : Type}
    (access : W → W → Prop) (existsAt rootAt : W → B → Prop)
    (w : W) (b : B)
    (occupied : ∀ v, access w v → ∃ x, rootAt v x)
    (rootExists : ∀ v x, rootAt v x → existsAt v x)
    (absent : ∃ v, access w v ∧ ¬ existsAt v b) :
    ∃ v, access w v ∧ ¬ existsAt v b ∧
      ∃ x, rootAt v x ∧ x ≠ b := by
  rcases absent with ⟨v, hv, hb⟩
  rcases occupied v hv with ⟨x, hx⟩
  refine ⟨v, hv, hb, x, hx, ?_⟩
  intro h
  subst x
  exact hb (rootExists v b hx)

open TruthCore.Causality.FirstMoverNecessity
open TruthCore.Causality.EsseCausePriority (DistinctEsseCausePriority)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Case.Catholicism (IsFirstUnmovedMover ThereIsAFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing FirstUnmovedMoverIsPureAct)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.BruteContingencyParity (source reasonModel
  NoBruteContingentExistenceAt ContingentExistenceNotSelfExplained ExistenceReasonSourceCausesEsse)

/-- Restrict the esse-cause premise to the actual first mover selected by the other premises. -/
theorem necessityFromCauseForFirstMover {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (w : W) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hThere : ThereIsAFirstUnmovedMover MovedIn F.MovesIn) (hExist : MoversExistAt F w)
    (hFirst : FirstUnmovedMoverIsFirstBeing MovedIn F.MovesIn F.PriorSimply)
    (hPure : FirstUnmovedMoverIsPureAct MovedIn F.MovesIn (PureAct InPotency))
    (hCause : ∀ f, IsFirstUnmovedMover MovedIn F.MovesIn f →
      ContingentAt F.history.ontic w f → ∃ c, c ≠ f ∧ F.CausesIn c f F.esse)
    (hPrior : DistinctEsseCausePriority F.CausesIn F.esse F.PriorSimply) :
    FirstMoverNecessaryPureActAt F MovedIn InPotency w := by
  obtain ⟨f, hm⟩ := hThere
  obtain ⟨x, r, hMoves⟩ := hm.1
  have hHere := hExist f x r hMoves
  refine ⟨f, hm, hPure f hm, hHere, fun v hv => ?_⟩
  rcases hEM (F.history.ontic.ExistsAt v f) with h | h
  · exact h
  · obtain ⟨c, hne, hc⟩ := hCause f hm ⟨hHere, v, hv, h⟩
    exact (hne (hFirst f hm c (hPrior c f hne hc))).elim

/-- When a contingent individual's existence has a reason, at least one reason
has a distinct bearer. Reasons about the individual itself are permitted. -/
def SomeExternalReasonAvailable {W B : Type} (m : Model W B) (w : W) : Prop :=
  ∀ x, ContingentAt m.ontic w x → (∃ r, m.explains w r (.fact x)) →
    ∃ r, m.explains w r (.fact x) ∧ source r ≠ x

theorem externalAvailableOfNoSelfExplanation {W B : Type} (m : Model W B) (w : W)
    (h : ContingentExistenceNotSelfExplained m w) : SomeExternalReasonAvailable m w := by
  intro x hc ⟨r, hr⟩
  exact ⟨r, hr, h x r hc hr⟩

/-- Local PSR supplies a reason, availability selects an external reason, and
the causal bridge applies to that same reason and recipient. -/
theorem causeFromAvailableExternalReason {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W)
    (hPSR : NoBruteContingentExistenceAt (reasonModel F ex) w)
    (hAvailable : SomeExternalReasonAvailable (reasonModel F ex) w)
    (hSource : ExistenceReasonSourceCausesEsse F (reasonModel F ex) w) :
    ContingentHasDistinctEsseCause F w := by
  intro x hx
  obtain ⟨r, hr, hne⟩ := hAvailable x hx (hPSR x hx)
  exact ⟨source r, hne, hSource x r hx hr hne⟩

end TruthCore.Explanation.FoundationalExistenceApplications
