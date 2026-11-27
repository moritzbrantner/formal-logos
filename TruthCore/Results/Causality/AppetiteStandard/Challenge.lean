import TruthCore.Causality.AppetiteStandard
import TruthCore.Results.Causality.PurityCriteria.Solution

namespace TruthCore.Results.Causality.AppetiteStandard

open TruthCore.Causality.AppetiteStandard
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral ActualRootFavouringIsGoodGeneral)
open TruthCore.Causality.PurityCriteria
  (ValueStandardOrder BetternessVariesWithinEndClass MissesVerdict UnbackedVerdict
    MissingValueVerdictIsImpure UnbackedValueVerdictIsImpure)
open TruthCore.Causality.GoodFavouring (Tracks OriginalFinalityForGood)
open TruthCore.Logic (ExcludedMiddle)

/-! ## The formal-object route to horn A's conclusion -/

/-- Horn A's conclusion `7fca65ec` from the per-bearer standard and the object
premise. Let `r` be an actual root and `favours φ` one of its determinations.
Actual roots have no represented limiting principle (its distinct simply prior
being is the frame's `PriorSimply`), so by the RootPurity bridge `favours φ` is
pure. By the per-bearer bridge a pure favouring makes exactly the verdicts of its
formal object for `r`, and by the object premise that object is the value order `v`
(STANDARD_OF_FAVOURING_1). Betterness varies within an end-realization class, so
`φ` favours `x` over `y` at the witness scenario and not at the other scenario of
the same end-realization class: `φ` is good-general. Neither the per-bearer
bridge nor the object premise mentions whether the favouring is a natural or a
rational appetite. -/
theorem actualRootFavouringIsGoodGeneralFromFormalObject {W B T R D P S X Z : Type}
    (F : CausalityFrame W B T R) (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) (Composite : B → Prop) (essence esse : B → P)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (obj : B → TruthCore.Causality.GoodFavouring.Profile S X → S → X → X → Prop)
    (v : ValueStandardOrder S X) (fitOf : S → Z) (Present : S → X → Prop)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essence esse)
    (hPurity : UnlimitedDeterminationsArePure Composite F.PriorSimply essence esse Has Pure)
    (hOwn : PureFavouringTracksItsObject Pure Has favours obj)
    (hObj : ActualRootFavouringObjectIsValue m w Has favours obj v)
    (hVaries : BetternessVariesWithinEndClass v fitOf Present) :
    ActualRootFavouringIsGoodGeneral m w Has favours v.better fitOf Present := by
  sorry

/-! ## Mode: the fixer law and determination to one end (Lean-only) -/

/-! ## Object: per-bearer and common-value forms (Lean-only) -/

/-! ## Finite controls -/

open TruthCore.Causality.AppetiteStandard.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok noInputs hasSrc personalSrc dNatureSrc purePos pureNoGG roots criterion appSource
    appNone)
open TruthCore.Causality.PurityCriteria.Control (purity varies generalFor chanceSrc pureChance)
open TruthCore.Results.Causality.ImpersonalFoundationJoint (ggBetter dNatureFactors notGGdNature
  dNatureNeBetter)

theorem appetiteGrid : AppetiteGrid := by
  sorry

theorem formalObjectControls : FormalObjectControls := by
  sorry

end TruthCore.Results.Causality.AppetiteStandard
