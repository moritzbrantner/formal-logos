import TruthCore.Causality.PossibiliaContent
import TruthCore.Results.Causality.AxiarchicFoundation.Solution

namespace TruthCore.Results.Causality.PossibiliaContent

open TruthCore.Causality.PossibiliaContent
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.AxiarchicFoundation
open TruthCore.Causality.ImpersonalFoundationJoint
  (GoodGeneral GoodGeneralFavouringIsApprehension ActualRootFavouringIsGoodGeneral
    ActualRootsHaveOwnFavouring ActualRootsApprehendThroughGoodGeneralFavouring)
open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence (ConstitutivelySimple)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Results.Causality.AxiarchicFoundation (favouredIndividuated)

/-! ## The shared demand, derived -/

/-- THE SHARED DEMAND. A constitutively simple bearer whose good-general
favouring has only non-present candidates has a stand-in that is in it without
being a real constituent of it. Realization and irreflexivity give two distinct
stand-ins, the two locus bridges put both in the bearer, and simplicity forbids
both being real. The theorem holds whatever the bearer is: it binds the personal
source (its ideas cannot be a real plurality) and the rival (its modes or powers
cannot be) alike. -/

/-! ## The root criterion from conceptualism about non-real being -/

/-- The root cognition criterion, derived. An actual root `r` has a good-general
favouring. Roots are constitutively simple and no candidate is a present input,
so (`simpleBearerHasNonRealStandIn`) some candidate's stand-in is in `r` without
being a real constituent of it. The conceptualist premise makes `r` apprehend it,
and the content premise makes it about its candidate. -/
theorem simpleRootGoodGeneralFavouringIsApprehension {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (stand : B → X → C) (rel : B → TruthCore.Causality.GoodFavouring.Profile S X → S → C → C → Prop)
    (Contains Produces RealConstituent : B → C → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hEM : ExcludedMiddle)
    (hReal : FavouringRealizedOnItems Has favours stand rel)
    (hIrr : FavouringIrreflexive Has favours)
    (hOwn : NoIndependentStandIn Has favours Present stand Contains Produces)
    (hNotMade : NoMerelyProducedStandIn Has favours Present stand Contains Produces)
    (hSimple : RootsConstitutivelySimple m w RealConstituent)
    (hNoPresent : NoPresentCandidates Present)
    (hNRA : NonRealContainmentIsApprehension Contains RealConstituent Apprehends)
    (hAbout : NonRealStandInIsAbout Has favours Present stand Contains RealConstituent About) :
    RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present About Apprehends := by
  sorry

/-- Strength order: the cognition criterion implies its restriction to actual
roots. -/
theorem rootCriterionOfCriterion {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hCriterion : GoodGeneralFavouringIsApprehension Has favours good fitOf Present About
      Apprehends) :
    RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present About Apprehends := by
  sorry

/-- The root criterion in place of the cognition criterion: commitment (e) in
its weakest favouring form and the good-generality of root favouring give every
actual root apprehension through good-general favouring. -/
theorem actualRootsApprehendFromRootCriterion {W B D S X Z C : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop)
    (favours : TruthCore.Causality.GoodFavouring.Profile S X → D)
    (good : S → X → X → Prop) (fitOf : S → Z) (Present : S → X → Prop)
    (About : C → X → Prop) (Apprehends : B → C → Prop)
    (hGeneral : ActualRootFavouringIsGoodGeneral m w Has favours good fitOf Present)
    (hFavouring : ActualRootsHaveOwnFavouring m w Has favours)
    (hRootCriterion : RootGoodGeneralFavouringIsApprehension m w Has favours good fitOf Present
      About Apprehends) :
    ActualRootsApprehendThroughGoodGeneralFavouring m w Has favours good fitOf Present About
      Apprehends := by
  sorry

/-! ## Lean-only: relocation probe

The conceptualist premise restricted to the root route
(`NonRealStandInYieldsApprehension`) is equivalent to the root criterion given
the other premises; the general premise is strictly stronger than the root
criterion given them (`rootCriterionWithoutConceptualism`). -/

/-! ## Controls -/

open TruthCore.Causality.PossibiliaContent.Control
open TruthCore.Causality.AxiarchicFoundation.Control
open TruthCore.Causality.SelectionScope (Outcome)
open TruthCore.Causality.GoodFavouring.Model (Scenario fits better fitOrder)
open TruthCore.Causality.ImpersonalFoundationJoint.Control (Det favTok hasSrc personalSrc noInputs)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)

end TruthCore.Results.Causality.PossibiliaContent
