import TruthCore.Explanation.FoundationalExistenceApplications

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
  sorry

/-- The local PSR plus one external reason per explained contingent and the
reason-to-cause bridge give B2 on the very same frame. -/
theorem distinctCause {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W)
    (hPSR : NoBruteContingentExistenceAt (reasonModel F ex) w)
    (hAvailable : SomeExternalReasonAvailable (reasonModel F ex) w)
    (hSource : ExistenceReasonSourceCausesEsse F (reasonModel F ex) w) :
    ContingentHasDistinctEsseCause F w := by
  sorry

/-- A contingent recipient has both an intrinsic reason and an external
circumstance. The new bundle holds while universal exclusion of self-reasons fails. -/
theorem mixedReasons :
    NoBruteContingentExistenceAt (reasonModel conserved selfAndOccasion) true ∧
      SomeExternalReasonAvailable (reasonModel conserved selfAndOccasion) true ∧
      ExistenceReasonSourceCausesEsse conserved (reasonModel conserved selfAndOccasion) true ∧
      ContingentAt conserved.history.ontic true true ∧
      ¬ ContingentExistenceNotSelfExplained (reasonModel conserved selfAndOccasion) true := by
  sorry

end TruthCore.Results.Explanation.ExternalExistenceReason
