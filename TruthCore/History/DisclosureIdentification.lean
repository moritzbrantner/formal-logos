module

public import TruthCore.History.SelectiveDisclosure
public import TruthCore.Science.Identifiability

/-! Occurrence identification from a fixed historical disclosure policy.
Histories differ at the earlier event. The policy retains only the later
entry, and all delivered entries are true in both histories. -/

@[expose] public section

namespace TruthCore.History.DisclosureIdentification

open SelectiveDisclosure
open TruthCore.Science.Identifiability

/-- The later event occurs in both histories. The earlier event occurs only
in the original history, and the third candidate occurs in neither. -/
def occurrence (earlier : Bool) (event : Event) : Prop :=
  if earlier then occurred event else event = 1

def fullRecord (earlier : Bool) : List Event :=
  if earlier then full else selected

def disclose (earlier : Bool) : List Event :=
  (fullRecord earlier).filter (· == 1)

/-- Coverage across the supplied history profile makes omission a correct
test for absence. The two-history control keeps every disclosed entry true
and shows that even unrestricted classifiers of the list cannot recover the
earlier event. Complete disclosure restores identification for this pair. -/
def Boundary : Prop :=
  (∀ (H E : Type) (observe : H → List E) (occurs : H → E → Prop),
    (∀ h e, e ∈ observe h → occurs h e) →
    ((∀ h e, occurs h e → e ∈ observe h) ↔
      ∀ h e, e ∉ observe h ↔ ¬ occurs h e)) ∧
  (∀ earlier event, event ∈ disclose earlier → occurrence earlier event) ∧
  disclose true = disclose false ∧ occurrence true 0 ∧ ¬ occurrence false 0 ∧
  (¬ ∃ classify : List Event → Prop,
    ∀ earlier, classify (disclose earlier) ↔ occurrence earlier 0) ∧
  Identifies fullRecord (fun earlier => occurrence earlier 0)

end TruthCore.History.DisclosureIdentification
