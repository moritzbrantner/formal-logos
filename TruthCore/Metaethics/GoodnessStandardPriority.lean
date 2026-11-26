module

public import TruthCore.Results.Logic.CorrectionCriterion.Solution

/-!
# Strict priority and option-specific eligibility

The three-edge cycle uses a single priority relation. The equal-data result
applies exact classification separately to each option.
-/

@[expose] public section

namespace TruthCore.Metaethics.GoodnessStandardPriority

open TruthCore.Logic.CorrectionCriterion

theorem noStrictCycle {F : Type} (prior : F → F → Prop)
    (trans : ∀ {x y z}, prior x y → prior y z → prior x z)
    (irrefl : ∀ x, ¬ prior x x)
    (a r d : F) (hAR : prior a r) (hRD : prior r d)
    (hDA : prior d a) : False :=
  irrefl a (trans (trans hAR hRD) hDA)

theorem eligibilityOnEqualData {S E O : Type}
    (data : S → E) (Good : S → O → Prop)
    (h : ∀ o, AdmitsCriterion data (fun s => Good s o))
    {s t : S} (same : data s = data t) (o : O) :
    Good s o ↔ Good t o :=
  ((TruthCore.Results.Logic.CorrectionCriterion.characterization.1
    S E data (fun s => Good s o)).mp (h o)) s t same

end TruthCore.Metaethics.GoodnessStandardPriority
