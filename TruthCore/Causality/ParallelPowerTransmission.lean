module

public import TruthCore.Causality.EssentialPower

@[expose] public section

namespace TruthCore.Causality.ParallelPowerTransmission

/-- In parallel successor rays, the only possible supplier of `(k, n)` is
`(k, n + 1)`. `intact k n` says its incoming link is available. The model
specifies local transmission; it makes no identification with a causality
frame's efficient cause or being-giving fields. Natural numbers order positions,
with increasing indices upstream, and do not represent times. -/
def transmissionLink {K : Type} (intact : K → Nat → Prop)
    (supplier recipient : K × Nat) : Prop :=
  supplier = (recipient.1, recipient.2 + 1) ∧ intact recipient.1 recipient.2

/-- Every incoming link from this position onward in one ray is intact. -/
def intactTail (intact : Nat → Prop) (n : Nat) : Prop :=
  ∀ m, n ≤ m → intact m

/-- A solution is exactly the union of the intact tails of its populated rays.
Any selection of rays supplies a solution. A selected ray with no intact tail
contributes nothing; on each surviving ray the selection is recovered by
testing whether some position is active. -/
def RaySolutions : Prop :=
  ∀ (K : Type) (intact : K → Nat → Prop),
    (∀ (active : K × Nat → Prop),
      PowerTransmissionRule (transmissionLink intact) active ↔
        ∀ k n, active (k, n) ↔ (∃ m, active (k, m)) ∧ intactTail (intact k) n) ∧
    ∀ (selected : K → Prop),
      PowerTransmissionRule (transmissionLink intact)
        (fun x => selected x.1 ∧ intactTail (intact x.1) x.2) ∧
      ∀ k, (∃ n, selected k ∧ intactTail (intact k) n) ↔
        selected k ∧ ∃ n, intactTail (intact k) n

/-- Any upstream cut forces a position off in every solution. The all-off
solution is unique pointwise exactly when no ray has an intact tail, which
holds in particular when there is a cut at or above every position. -/
def CutEffects : Prop :=
  ∀ (K : Type) (intact : K → Nat → Prop),
    (∀ (active : K × Nat → Prop),
      PowerTransmissionRule (transmissionLink intact) active →
      ∀ k n m, n ≤ m → ¬ intact k m → ¬ active (k, n)) ∧
    ((∀ (active : K × Nat → Prop),
      PowerTransmissionRule (transmissionLink intact) active →
        ∀ x, ¬ active x) ↔ ∀ k n, ¬ intactTail (intact k) n) ∧
    ((∀ k n, ∃ m, n ≤ m ∧ ¬ intact k m) →
      ∀ (active : K × Nat → Prop),
        PowerTransmissionRule (transmissionLink intact) active → ∀ x, ¬ active x)

def ActivityClassification : Prop :=
  RaySolutions ∧ CutEffects

/-- Countably many intact rays admit an activity profile missed by any
natural-number-indexed catalogue of total activity profiles. -/
def CountableCatalogueMisses : Prop :=
  ∀ (catalogue : Nat → Nat × Nat → Prop),
    ∃ active : Nat × Nat → Prop,
      PowerTransmissionRule (transmissionLink (fun _ _ => True)) active ∧
      ∀ i, ¬ (active (i, 0) ↔ catalogue i (i, 0))

end TruthCore.Causality.ParallelPowerTransmission
