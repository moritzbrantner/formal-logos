import TruthCore.Causality.PurityCriteria
import TruthCore.Results.Causality.ImpersonalFoundationJoint.Solution
import TruthCore.Results.Causality.RootPerfectionIntellect.Solution

namespace TruthCore.Results.Causality.PurityCriteria

open TruthCore.Causality.PurityCriteria
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.ImpersonalFoundationJoint
  (GoodGeneral ActualRootFavouringIsGoodGeneral OneFavouringRealization)
open TruthCore.Causality.RootPerfectionIntellect (ExclusionFreeAdmissible PureRequiresNoPureLack)
open TruthCore.Causality.RootPerfectionExclusion (ActualProfile UnexplainedAbsence)
open TruthCore.Logic (ExcludedMiddle)

/-! ## A. The standard route to horn A's conclusion -/

/-- Horn A's conclusion `7fca65ec` without the admissible family, joint
compossibility, the purity of good-generality or one-favouring realization.
Let `r` be an actual root and `favours φ` one of its determinations. Actual roots
have no represented limiting principle, so by the RootPurity bridge `favours φ`
is pure. By the loss and arbitrariness bridges (and excluded middle), `φ` makes
exactly the verdicts of the standard `good`. Betterness varies within an
end-realization class, so the standard itself is good-general, and a profile with
exactly its verdicts is good-general at the same witness. The distinct simply
prior being of the limiting principle is the frame's `PriorSimply`. -/
theorem actualRootFavouringIsGoodGeneralFromStandard {W B T R D P S X Z : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (hEM : ExcludedMiddle)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hPurity : UnlimitedDeterminationsArePure Composite F.PriorSimply essence esse Has Pure)
    (hLoss : MissingVerdictIsImpure Pure favours good)
    (hBacked : UnbackedVerdictIsImpure Pure favours good)
    (hVaries : BetternessVariesWithinEndClass good fitOf Present) :
    ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present := by
  sorry

/-! ## Symmetric alternatives -/

/-! ## D. Two favourings and their union -/

/-! ## B. The enumerative rule overgeneralizes -/

/-! ## C. Tensed omniscience and immutability -/

/-! ## Controls -/

open TruthCore.Causality.PurityCriteria.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok noInputs hasSrc personalSrc dNatureSrc purePos pureNoGG roots gg anyFamily)
open TruthCore.Results.Causality.ImpersonalFoundationJoint
  (ggBetter dNatureFactors notGGdNature dNatureNeBetter factorsThroughNotGoodGeneral)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootPerfectionExclusion.Control (composite rep)

theorem standardControls : StandardControls := by
  sorry

theorem standardRelativity : StandardRelativity := by
  sorry

theorem refinementCondemnsGoodTracking : RefinementCondemnsGoodTracking := by
  sorry

end TruthCore.Results.Causality.PurityCriteria
