import TruthCore.Explanation.BruteContingencyParity
import TruthCore.Results.Explanation.StoppingPoints.Solution

/-! Brute contingency and the parity of brute-existence demands: two further
support options for B2 on the shared frame, the contingent-only weakening of
the local existence PSR, the parity argument, and laws and models. Analyst
formulations; attribution deferred. -/

namespace TruthCore.Results.Explanation.BruteContingencyParity
open TruthCore.Explanation.BruteContingencyParity
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FirstMoverNecessity (ContingentHasDistinctEsseCause
  ContingentHasDistinctEsse groundProfile)
open TruthCore.Causality.FirstMoverNecessity.Model (bruteFirst conserved allConcrete
  noneConcrete noGround xGroundsF mk fContingent noCause noPrior xCausesF xPriorF)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.GradedSupportFoundation (ActualGroundIsDistinctEsseCause)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.NoBruteExistence (NoBruteExistenceAt)
open TruthCore.Explanation.PSRStrength (Arena Access Contingent Explained
  IrreflexiveContingent basic everywhere ofModel)
open TruthCore.Explanation.PSRSelfApplication (Stance BruteAt Uniform Selective Restricted)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- B2 from reasons for existence: a being `x` contingent at `w` has some reason
`r` for its existence (local existence PSR for contingents); the being `r` is
about is not `x` (BX1); so it causes `x`'s esse (BX2), and it is a distinct
CAUSE_2 of `x`'s esse. -/
theorem esseCauseFromExistenceReasons {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W)
    (hPSR : NoBruteContingentExistenceAt (reasonModel F ex) w)
    (hSelf : ContingentExistenceNotSelfExplained (reasonModel F ex) w)
    (hSource : ExistenceReasonSourceCausesEsse F (reasonModel F ex) w) :
    ContingentHasDistinctEsseCause F w := by
  sorry

/-- B2 from the selected-grounding closure: a being `x` contingent at `w` is
concrete (interface), so the closure gives it an actual concrete ground `y`
at `w`; the existing ground-to-cause bridge makes `y` distinct from `x` and a
cause of its esse. -/
theorem esseCauseFromGroundingClosure {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hConcrete : ContingentsConcrete F concrete w)
    (hClosure : EveryContingentGroundedAt (groundProfile F concrete grounds) w)
    (hBridge : ActualGroundIsDistinctEsseCause (groundProfile F concrete grounds) w
      F.CausesIn F.esse) :
    ContingentHasDistinctEsseCause F w := by
  sorry

/-- The parity argument: if the stance's ontic demand is uniform in `k`, it
requires a reason why `t` obtains, and `t` and `o` agree on `k`, then it
requires a reason why `o` obtains; meeting its demand, it cannot accept `o` as a
brute contingent truth. -/
theorem parity {W B F : Type} (S : WhyStance F) (k : F → Prop) (A : Arena W B F)
    (w : W) (t o : F)
    (hUniform : FeatureUniform S k) (hReq : RequiresWhyFor S t)
    (hShare : ShareFeature k t o) :
    ExcludesBruteRival S A w o := by
  sorry

/-! ## Laws and models -/

theorem b2SupportControls : B2SupportControls := by
  sorry

/-! ## The parity map -/

/-- Unfold the scene and decide it by cases. -/
local macro "scene" : tactic => `(tactic| (
  simp only [ShareFeature, PositedWithoutReason, atheistReading, theistReading, naturalist,
    manyBrute, bruteBase, natureBase, bruteGod, theist, contingentGod, picture, contingentRow,
    pnone, basic, everywhere, ptbl, Explained, HoldsBruteRival, WhyHonors,
    WhyHonorsNecessitating, RequiresWhyFor, FeatureUniform, Selective, Restricted, whyView,
    idle, existence, godOnly, evidential, symmetric, uniformRejector, baseNaturalist,
    theistStance, contingentOnlyTheist, wstance, natAccepts, natCore, BruteAt, Contingent,
    Access, IrreflexiveContingent, ofModel, reasonModel, bruteFirst, mk, fContingent,
    noReasons, UnexplainedAre, UnnecessitatedAre, observation,
    TruthCore.Explanation.PSRStrength.Factive,
    TruthCore.Explanation.PSRSelfApplication.Supported,
    TruthCore.Explanation.PSRSelfApplication.Honors,
    TruthCore.Explanation.PSRSelfApplication.demandNorm,
    TruthCore.Logic.SelfApplication.Norm.Holds, pfact_forall, pfact_exists] <;>
  simp [Bool.forall_bool, reason_exists]))

theorem parityMap : ParityMap := by
  sorry

end TruthCore.Results.Explanation.BruteContingencyParity
