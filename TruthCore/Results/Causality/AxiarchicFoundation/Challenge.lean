import TruthCore.Causality.AxiarchicFoundation
import TruthCore.Results.Causality.ImpersonalFoundationJoint.Solution

namespace TruthCore.Results.Causality.AxiarchicFoundation

open TruthCore.Causality.AxiarchicFoundation
open TruthCore.Causality.GoodFavouring (BecauseOfGoodness)
open TruthCore.Causality.ImpersonalFoundationJoint (GoodGeneral GoodGeneralFavouringIsApprehension)
open TruthCore.Logic (ExcludedMiddle)

/-! ## The nowhere horn -/

/-! ## The criterion from the individuation premises -/

/-- The cognition criterion, derived. Let `b` have a good-general favouring
determination `favours φ`: for some scenario `s` and pair `x`, `y`, at least one
not a present input, `φ` depends on value with end content fixed, so in
particular `φ s x y`. Item realization and irreflexivity make the stand-ins of
`x` and `y` distinct (the nowhere horn is excluded). Take the non-present one,
`z`. By excluded middle its stand-in is contained in `b`, or produced by `b`, or
independent of `b`; the own-favouring bridge excludes the independent realm and
the source-of-differences bridge the merely produced one, so it is contained. The
containment-recognition bridge then makes it a content about `z` that `b`
apprehends. -/
theorem goodGeneralFavouringIsApprehensionOfIndividuation {B D S X Z C : Type}
    (Has : B → D → Prop) (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → S → C → C → Prop) (Contains Produces : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hRecog : ContainedStandInIsApprehended Has favours good fitOf Present stand Contains About
      Apprehends) :
    GoodGeneralFavouringIsApprehension Has favours good fitOf Present About Apprehends := by
  sorry

/-! ## Controls -/

open TruthCore.Causality.AxiarchicFoundation.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder)
open TruthCore.Causality.ImpersonalFoundationJoint.Control
  (Det favTok hasSrc personalSrc noInputs gg)

/-- The individuation trilemma on one carrier (see `AxiarchicControls`). -/
theorem axiarchicControls : AxiarchicControls := by
  sorry

end TruthCore.Results.Causality.AxiarchicFoundation
