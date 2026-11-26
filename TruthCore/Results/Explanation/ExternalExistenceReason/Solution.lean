module

public import TruthCore.Explanation.FoundationalExistenceApplications

@[expose] public section

namespace TruthCore.Results.Explanation.ExternalExistenceReason

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FirstMoverNecessity (ContingentHasDistinctEsseCause)
open TruthCore.Causality.FirstMoverNecessity.Model (conserved)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.BruteContingencyParity
open TruthCore.Explanation.FoundationalExistenceApplications (SomeExternalReasonAvailable)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- Excluding all self-explanations makes every available reason external. -/
theorem externalAvailable {W B : Type} (m : Model W B) (w : W)
    (h : ContingentExistenceNotSelfExplained m w) : SomeExternalReasonAvailable m w := by
  exact TruthCore.Explanation.FoundationalExistenceApplications.externalAvailableOfNoSelfExplanation m w h

/-- The local PSR plus one external reason per explained contingent and the
reason-to-cause bridge give B2 on the very same frame. -/
theorem distinctCause {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W)
    (hPSR : NoBruteContingentExistenceAt (reasonModel F ex) w)
    (hAvailable : SomeExternalReasonAvailable (reasonModel F ex) w)
    (hSource : ExistenceReasonSourceCausesEsse F (reasonModel F ex) w) :
    ContingentHasDistinctEsseCause F w := by
  exact TruthCore.Explanation.FoundationalExistenceApplications.causeFromAvailableExternalReason F ex w hPSR hAvailable hSource

/-- A contingent recipient has both an intrinsic reason and an external
circumstance. The new bundle holds while universal exclusion of self-reasons fails. -/
theorem mixedReasons :
    NoBruteContingentExistenceAt (reasonModel conserved selfAndOccasion) true ∧
      SomeExternalReasonAvailable (reasonModel conserved selfAndOccasion) true ∧
      ExistenceReasonSourceCausesEsse conserved (reasonModel conserved selfAndOccasion) true ∧
      ContingentAt conserved.history.ontic true true ∧
      ¬ ContingentExistenceNotSelfExplained (reasonModel conserved selfAndOccasion) true := by
  have hc : ContingentAt conserved.history.ontic true true := by
    refine ⟨Or.inr rfl, false, trivial, ?_⟩
    rintro (h | h) <;> contradiction
  have onlyMover (x : Bool) (hx : ContingentAt conserved.history.ontic true x) : x = true := by
    cases x with
    | false =>
      obtain ⟨_, v, _, habs⟩ := hx
      exact (habs (Or.inl rfl)).elim
    | true => rfl
  have external : selfAndOccasion true (.circumstance false) (.fact true) := Or.inr ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_, hc, ?_⟩
  · intro x hx
    obtain rfl := onlyMover x hx
    exact ⟨.circumstance false, external⟩
  · intro x hx _
    obtain rfl := onlyMover x hx
    exact ⟨.circumstance false, external, by decide⟩
  · intro x r hx _ hne
    obtain rfl := onlyMover x hx
    have hs : source r = false := by
      cases e : source r with
      | false => rfl
      | true => exact (hne e).elim
    exact ⟨hs, rfl, rfl⟩
  · intro h
    exact h true (.intrinsic true) hc (Or.inl rfl) rfl

end TruthCore.Results.Explanation.ExternalExistenceReason
