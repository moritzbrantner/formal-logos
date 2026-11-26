module

public import TruthCore.Causality.FiniteReserveOdds
public import TruthCore.Causality.SupplierAuditCertificates

/-! Exact prefix records of complete supplier lists on a fixed natural-number
roster. The finite rival ranges over sourced depths on that same roster. -/

@[expose] public section
noncomputable section
namespace TruthCore.Causality.SupplierAuditLikelihood

open TruthCore.Causality.SupplierAudit
open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Causality.FiniteReserveOdds (geometricPrior)
open TruthCore.Causality.PostCutStore (prefixSum)

/-- Audit recipients zero through length minus one along the endless chain. -/
def PrefixMatches (length : ℕ) (supplies : ℕ → ℕ → Prop) : Prop :=
  (auditFrame id (Set.Iio length)).access endless supplies

/-- The next audited recipient, at the end of the matching prefix, has an empty list. -/
def TerminalMatches (depth : ℕ) (supplies : ℕ → ℕ → Prop) : Prop :=
  PrefixMatches depth supplies ∧ ∀ supplier, ¬ supplies supplier depth

/-- For deterministic sourced worlds, sum the fixed conditional finite-class
prior over worlds that match the actual prefix record. -/
def depthLikelihood (prior : ℕ → ℝ) (length : ℕ) : ℝ := by
  classical
  exact ∑' depth : ℕ, if PrefixMatches length (sourced depth) then prior depth else 0

/-- Conditional likelihood in the sourced class, with a positive denominator
required for its interpretation. The numerator counts worlds matching both records. -/
def conditionalDepthLikelihood (prior : ℕ → ℝ) (new observed : ℕ) : ℝ := by
  classical
  exact (∑' depth : ℕ, if PrefixMatches new (sourced depth) ∧
    PrefixMatches observed (sourced depth) then prior depth else 0) /
    depthLikelihood prior observed

/-- Exact compatibility, finite-terminal discrimination, and the comparison
of prefix weights for the endless world and the mixture of sourced worlds. -/
def PrefixComparison : Prop :=
  (∀ length depth, PrefixMatches length (sourced depth) ↔ length ≤ depth) ∧
  (∀ length, PrefixMatches length endless ∧ PrefixMatches length (sourced length) ∧
    RootAncestor length 0 (sourced length)) ∧
  (∀ observed depth, TerminalMatches observed (sourced depth) ↔ depth = observed) ∧
  (∀ observed, ¬ TerminalMatches observed endless) ∧
  (∀ length, ∃ prior : ℕ → ℝ, (∀ depth, 0 ≤ prior depth) ∧ HasSum prior 1 ∧
    depthLikelihood prior length = 1) ∧
  (∀ prior : ℕ → ℝ, (∀ depth, 0 ≤ prior depth) → HasSum prior 1 →
    (∀ length, depthLikelihood prior length = 1 - prefixSum prior length) ∧
    ∀ (finiteWeight endlessWeight factor : ℝ), 0 < finiteWeight → 0 < endlessWeight →
      0 < factor → ∃ start : ℕ, ∀ length ≥ start,
        factor * (finiteWeight * depthLikelihood prior length) < endlessWeight) ∧
  (HasSum geometricPrior 1 ∧ (∀ depth, 0 < geometricPrior depth) ∧
    ∀ length,
      depthLikelihood geometricPrior length = (1 / 2 : ℝ) ^ length ∧
      0 < depthLikelihood geometricPrior length ∧
      ∀ finiteWeight endlessWeight : ℝ, 0 < finiteWeight → 0 < endlessWeight →
        ¬ ∀ factor : ℝ, 0 < factor →
          factor * (finiteWeight * depthLikelihood geometricPrior length) ≤ endlessWeight)

/-- A match to a shorter record is already implied by the longer one. For an
extension, nested records give a ratio of likelihoods instead of a fresh trial. -/
def PrefixConditioning : Prop :=
  (∀ (prior : ℕ → ℝ) new observed, new ≤ observed → 0 < depthLikelihood prior observed →
    conditionalDepthLikelihood prior new observed = 1) ∧
  (∀ (prior : ℕ → ℝ) new observed, observed ≤ new → 0 < depthLikelihood prior observed →
    conditionalDepthLikelihood prior new observed =
      depthLikelihood prior new / depthLikelihood prior observed) ∧
  (∀ (prior : ℕ → ℝ) new observed (finiteWeight endlessWeight : ℝ), observed ≤ new →
    0 < depthLikelihood prior observed → 0 < depthLikelihood prior new →
    0 < finiteWeight →
    endlessWeight / (finiteWeight * depthLikelihood prior observed) /
        conditionalDepthLikelihood prior new observed =
      endlessWeight / (finiteWeight * depthLikelihood prior new))

end TruthCore.Causality.SupplierAuditLikelihood
