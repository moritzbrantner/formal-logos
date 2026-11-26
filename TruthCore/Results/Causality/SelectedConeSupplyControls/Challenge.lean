import TruthCore.Causality.SelectedConeSupply
import TruthCore.Results.Causality.SelectedConeSupply.Solution
import TruthCore.Causality.MathlibBridges
import TruthCore.Results.Causality.SelectedConeRegress.Solution
import TruthCore.Results.Causality.SelectedSourcePath.Solution
import TruthCore.Results.Causality.FiniteThroughput.Solution
import TruthCore.Results.Causality.ReceiptMatching.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
import Mathlib.Order.WellFounded
import Mathlib.Data.Nat.Cast.WithTop

open scoped ENNReal

namespace TruthCore.Results.Causality.SelectedConeSupplyControls
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
open TruthCore.Results.Causality.SelectedConeSupply (sourcePath_of_receiptExit)
open TruthCore.Causality.SelectedSourcePath
open TruthCore.Causality.WorldSourceRegress (SourcePath overlap)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic.RootDescent (acc_of_map acc_of_subtype)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

theorem coneWalkCriterion : ConeWalkCriterion := by
  sorry

theorem coneWellFounded_iff_localAcyclic_and_noInjectiveRegress (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) :
    ConeWellFounded m w x.val ↔
      (coneGraph m w x.val).NoCycles ∧ NoAnchoredConcreteGroundingRegress m w x := by
  sorry

theorem natRank_of_sourcePath_and_oneStep (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (path : HasSelectedSourcePath m w x) (forks : SelectedForksJoinInOneStep m w x) :
    HasNatRank (coneGraph m w x.val) := by
  sorry

theorem sourcePath_and_oneStep_fail_on_rankedFork :
    HasNatRank splitFork ∧ SourcePath splitFork 2 ∧ ¬ ForksJoinInOneStep splitFork := by
  sorry

theorem wellFoundedCone_withoutNatRank :
    ConeWellFounded topProfile () ⊤ ∧ ¬ HasNatRank (coneGraph topProfile () ⊤) := by
  sorry

/-- Both aligned ledgers book the same one real ground edge of the model
while omitting the ray edges. They yield a source path and leave a regress
in the very same cone at the very same recipient. -/
theorem alignedLedgers_allowAnchoredRegress :
    ContingentAt rayProfile.ontic true rayTip.val ∧
    SelectedReceiptExit rayProfile true rayTip raySender rayReceiver ∧
    GroundedCanMatch rayProfile true raySender rayReceiver ∧
    SelectedThroughputExit rayProfile true rayTip rayFlow ∧
    GroundedExportCovered rayProfile true rayFlow ∧
    HasSelectedSourcePath rayProfile true rayTip ∧
    AnchoredConcreteGroundingRegress rayProfile true rayTip := by
  sorry

theorem wellFounded_of_natRank (G : Graph N) (ranked : HasNatRank G) : WellFounded G.edge := by
  sorry

open TruthCore.Latin.Aquinas.SummaTheologiae
  (NoInfinitePerSeEfficientCauseSeriesReading)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NecessityCausedAmongNecessaries NoInfiniteRegressInCausedNecessariesReading)

/-- Both applications are on the represented cone carrier. Each relation
needs its own edge-inclusion proof. -/
theorem perSeRegressExcluded_on_cone {W B T : Type} {m : Profile W B} {w : W}
    {recipient : B} (wf : ConeWellFounded m w recipient)
    (causesAsCaused causesNecessity : {b // Cone m w recipient b} → {b // Cone m w recipient b} → Prop)
    (possible : (T → Prop) → Prop) (isAt : {b // Cone m w recipient b} → T → Prop)
    (perSeEdge : ∀ ⦃y x⦄, causesAsCaused y x → m.grounds w y.val x.val)
    (necessityEdge : ∀ ⦃y x⦄, NecessityCausedAmongNecessaries possible isAt causesNecessity y x →
      m.grounds w y.val x.val) :
    NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused ∧
      NoInfiniteRegressInCausedNecessariesReading possible isAt causesNecessity := by
  sorry

end TruthCore.Results.Causality.SelectedConeSupplyControls
