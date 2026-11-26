import TruthCore.Causality.SelectedConeSupply
import TruthCore.Causality.MathlibBridges
import TruthCore.Results.Causality.SelectedConeRegress.Solution
import TruthCore.Results.Causality.SelectedSourcePath.Solution
import TruthCore.Results.Causality.FiniteThroughput.Solution
import TruthCore.Results.Causality.ReceiptMatching.Solution
import Mathlib.Order.WellFounded

open scoped ENNReal

namespace TruthCore.Results.Causality.SelectedConeSupply
open TruthCore.Causality (FiniteCausalPath finiteCausalPath_iff_reflTransGen)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.FiniteThroughput
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.ReceiptMatching
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.SelectedConeSupply
open TruthCore.Causality.SelectedSourcePath
open TruthCore.Causality.WorldSourceRegress (SourcePath overlap)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic.RootDescent (acc_of_map acc_of_subtype)

theorem sourcePath_of_receiptExit (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (sender receiver : E → {b // ActualConcrete m w b})
    (deficit : UnmatchedUpstream) (covered : GroundedCanMatch m w sender receiver)
    (exit : SelectedReceiptExit m w x sender receiver) :
    HasSelectedSourcePath m w x := by
  sorry

theorem sourcePath_of_throughputExit (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (flow : {b // ActualConcrete m w b} → {b // ActualConcrete m w b} → ℝ≥0∞)
    (cut : ReturnOrNetExport) (covered : GroundedExportCovered m w flow)
    (exit : SelectedThroughputExit m w x flow) :
    HasSelectedSourcePath m w x := by
  sorry

end TruthCore.Results.Causality.SelectedConeSupply
