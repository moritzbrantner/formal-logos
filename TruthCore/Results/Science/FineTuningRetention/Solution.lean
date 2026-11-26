module

public import TruthCore.Science.FineTuningRetention

@[expose] public section

namespace TruthCore.Results.Science.FineTuningRetention

open TruthCore.Science.FineTuningSelection
open TruthCore.Science.FineTuningInformation TruthCore.Science.FineTuningRetention
open TruthCore.Teleonomy

theorem retentionScreening (hInformation : ObserverInformationCriterion) :
    RetentionScreening := by
  intro d n hd hn
  have hfilter (s : Sampling) : retainedFineLikelihood selectionExample s = 1 := by
    have htrue : retained selectionExample true = true := rfl
    have hfalse : retained selectionExample false = false := rfl
    simp [retainedFineLikelihood, htrue, hfalse, s.evidence_pos.ne']
  have hreport (s : Sampling) (hs : s.weight 1 = 0) : likelihood s = 1 := by
    simp [likelihood, hs, s.evidence_pos.ne']
  have hdReport := hreport d hd
  have hnReport := hreport n hn
  exact ⟨(hfilter d).trans hdReport.symm, (hfilter n).trans hnReport.symm,
    hdReport, hnReport, fun p hp hp' =>
      (hInformation p d n hp hp').mpr (hdReport.trans hnReport.symm)⟩

end TruthCore.Results.Science.FineTuningRetention
