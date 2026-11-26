module

public import TruthCore.Science.FineTuningInformation
public import TruthCore.Teleonomy.Mechanisms

/-!
Apply the teleonomy fixture's Boolean retention rule to the fine-evidence
indicator. This uses its input-output behavior as a sampling filter. The
sampling states are the three fine-tuning cells.
-/

@[expose] public section

namespace TruthCore.Science.FineTuningRetention

open FineTuningSelection FineTuningInformation
open TruthCore.Teleonomy

/-- Retain the whole fine cell or the whole complementary cell according to
the supplied filter. The denominator is the total retained mass. -/
def retainedFineLikelihood (filter : Selection) (s : Sampling) : ℚ :=
  let fine := if retained filter true then s.weight 0 else 0
  let other := if retained filter false then s.weight 1 + s.weight 2 else 0
  fine / (fine + other)

/-- When only the fine cell contains observers, sampling observers has the
same fine-report probability as applying the actual teleonomy fixture. -/
def RetentionScreening : Prop :=
  ∀ (d n : Sampling), d.weight 1 = 0 → n.weight 1 = 0 →
    retainedFineLikelihood selectionExample d = likelihood d ∧
    retainedFineLikelihood selectionExample n = likelihood n ∧
    likelihood d = 1 ∧ likelihood n = 1 ∧
    ∀ (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      reportInformation p d n = 0

end TruthCore.Science.FineTuningRetention
