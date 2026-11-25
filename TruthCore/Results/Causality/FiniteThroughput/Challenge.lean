import TruthCore.Causality.FiniteThroughput

open scoped ENNReal
open Relation
namespace TruthCore.Results.Causality.FiniteThroughput
open TruthCore.Causality
open TruthCore.Causality.FiniteThroughput

theorem returnOrNetExport : ReturnOrNetExport := by
  sorry

theorem groundedExerciseAtTransfer (cut : ReturnOrNetExport) : GroundedExerciseAtTransfer := by
  sorry

open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete ActualRoot)
open RootPositiveIntellectWill (ActualRootExistsAt)

theorem actualRootOfLedger {W B : Type} (m : Profile W B) (w : W)
    (flow : {x // ActualConcrete m w x} → {x // ActualConcrete m w x} → ℝ≥0∞)
    (cut : ReturnOrNetExport) (oneWay : FiniteOneWayTransfer flow)
    (covered : GroundedExportCovered m w flow) : ActualRootExistsAt m w := by
  sorry

theorem ledgerExistenceCriterion (cut : ReturnOrNetExport) : LedgerExistenceCriterion := by
  sorry

end TruthCore.Results.Causality.FiniteThroughput
