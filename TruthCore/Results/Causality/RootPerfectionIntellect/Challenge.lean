import TruthCore.Causality.RootPerfectionIntellect
import TruthCore.Results.Causality.WholePowerPerfection.Solution
import TruthCore.Results.Causality.ActualAncestralSource.Solution
import TruthCore.Results.Causality.RootPerfectionExclusion.Solution

namespace TruthCore.Results.Causality.RootPerfectionIntellect

open TruthCore.Causality.RootPerfectionIntellect
open TruthCore.Causality.RootPerfectionIntellect.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple)
open TruthCore.Causality.PureActRoot
  (ActualRootHasEveryPureDetermination ActualRootDeterminationsArePure)
open TruthCore.Causality.WholePowerPerfection (UnlimitedIsOwnBeing)
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
  (WisdomSelfCapacity SelfCapacityExercisedOrPotent TrueSelfApprehensionGrounded
    IntrinsicSelfKnowledge)
open TruthCore.Causality.NecessaryFirstBeing (NecessaryActualFirstPureActAt)
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Causality.RootPerfectionExclusion
  (ActualProfile RootProfilesAdmissible PureExtensionsAdmissible PureDeterminationsAdmissible)
open TruthCore.Causality.RootPerfectionExclusion.Control (roots has isPure)
open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination PairwiseAdmitted effect)
open TruthCore.Case.Catholicism (GodHasIntellect)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Causality.Frame (CausalityFrame)

/-! ## A. From every pure perfection to intellect -/

/-- Step one. At an actual root without a represented limiting principle
(`a30c5963`), the open `UnlimitedIsOwnBeing` makes the root its own being.
Every pure perfection at actual roots (`fe67d766`) and the purity of `wisdom`
give the root `wisdom`. The three open WisdomSelfUnderstanding bridges and the
root's pure act then give intrinsic self-knowledge. The proof is the existing
`actualRootSelfKnowledgeFromWisdom`, unchanged. The whole-power premises of the
q.4 a.2 route (`d164b1ff`, `c4fb87a6`) are not used: `fe67d766` replaces
them, so any producer of `fe67d766` feeds this step. Simple priority is the
shared frame's `F.PriorSimply` (PRIOR_1, #1784); the respects of `InPotency`
are the frame's respects. The legacy theorem is instantiated at the frame's
field, with no adapter needed. -/
theorem pureActRootsKnowThemselvesFromPurity {W B T P D C R : Type}
    (F : CausalityFrame W B T R)
    (m : Profile W B) (w : W) (Composite : B → Prop)
    (essenceOf esseOf : B → P) (OwnBeing : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (wisdom : D) (About Correct : C → B → Prop)
    (CanApprehend Apprehends CognitivelyGrounded : B → C → Prop)
    (InPotency : B → R → Prop) (understanding : R)
    (hNoLimits : ActualRootsWithoutLimitingPrinciple m w Composite F.PriorSimply essenceOf
      esseOf)
    (hOwn : UnlimitedIsOwnBeing Composite F.PriorSimply essenceOf esseOf OwnBeing)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPureWisdom : WisdomIsPure Pure wisdom)
    (hSelfCapacity : WisdomSelfCapacity OwnBeing Has wisdom About Correct CanApprehend)
    (hExercise : SelfCapacityExercisedOrPotent OwnBeing About CanApprehend Apprehends
      InPotency understanding)
    (hGrounding : TrueSelfApprehensionGrounded OwnBeing About Correct Apprehends
      CognitivelyGrounded) :
    PureActRootsKnowThemselves m w About Correct Apprehends CognitivelyGrounded InPotency := by
  sorry

/-- Step two. Some actual first root at `w` is PURE_ACT_1 (`593d7307`). Finite
grounding reach (`75974d26`) makes every GOD_4 that same root
(`namedRootOfReach`). Step one gives it intrinsic self-knowledge, and the open
recognition bridge gives HAS_INTELLECT_1. Simple priority (in "first") is the
shared frame's `F.PriorSimply`. -/
theorem godHasIntellectFromRootPerfection {W B T C R : Type} (F : CausalityFrame W B T R)
    (m : Profile W B) (w : W)
    (InPotency : B → R → Prop) (IsGod HasIntellect : B → Prop)
    (About Correct : C → B → Prop) (Apprehends CognitivelyGrounded : B → C → Prop)
    (hFirst : NecessaryActualFirstPureActAt m w F.PriorSimply InPotency)
    (hReach : GodReachesActualConcreta m w IsGod)
    (hKnow : PureActRootsKnowThemselves m w About Correct Apprehends CognitivelyGrounded
      InPotency)
    (hRecognition : GodIntrinsicSelfKnowledgeIsIntellect IsGod HasIntellect About Correct
      Apprehends CognitivelyGrounded) :
    GodHasIntellect IsGod HasIntellect := by
  sorry

/-! ## B. Constitutive admissibility

The registered derivations use only the sufficiency direction
`ExclusionFreeAdmissible`. Under it and `PureRequiresNoPureLack` every profile of
pure determinations is admissible, so the conclusions hold with room to spare.
`premisesIffStructural` and `sufficiencyPremisesIffAllPure` show what the premise
pairs amount to once the requirement relation is free: they relocate joint
compossibility into requirement form; they add no structural content beyond
downward closure (member grounding) and the localization of incompatibility in a
member, which lives in the intended reading of `RequiresLack`. -/

/-- Member grounding (strong) gives its sufficiency direction (weak). -/
theorem exclusionFreeAdmissibleOfMemberGrounding {D : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hGround : MemberGroundedAdmissibility Admissible RequiresLack) :
    ExclusionFreeAdmissible Admissible RequiresLack := by
  sorry

/-- Certified difference: member grounding is its sufficiency direction plus
its necessity direction. Premise-free and constructive. -/
theorem mgOverSufficiencyExact : MGOverSufficiencyExact := by
  sorry

/-- Joint compossibility `500d0e2d` from the sufficiency direction and the
purity premise. The insertion law's admissibility hypotheses are not used. -/
theorem jointCompossibilityOfExclusionFreeAdmissibility {D : Type}
    (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure) :
    PureExtensionsAdmissible Admissible Pure := by
  sorry

/-- Admissibility of each pure determination `ee287fd3`: its singleton is
exclusion-free. -/
theorem pureAdmissibleOfExclusionFreeAdmissibility {D : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure) :
    PureDeterminationsAdmissible Admissible Pure := by
  sorry

/-- Admissibility of each actual root's profile `0a9d3a40`, given that every
determination of an actual root is pure (`3b39e0ba`). -/
theorem rootProfilesAdmissibleOfExclusionFreeAdmissibility {W B D : Type} (m : Profile W B)
    (w : W) (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure)
    (hRootPure : ActualRootDeterminationsArePure m w Has Pure) :
    RootProfilesAdmissible m w Admissible Has := by
  sorry

/-! ## Finite controls -/

open TruthCore.Causality.RootPerfectionExclusion.Control (composite prior rep)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff limitingIff rootsIff)

/-- Step one: a positive witness and, for each of its seven premises, an
assignment on the same carrier where that premise fails, the six others hold
and the conclusion fails. The rows vary only which relations are populated.
In the exercise row the source can apprehend its own content, does not, and is
in potency in no respect: this is a model only because `InPotency` is the
independently supplied POTENCY_2. -/
theorem stepOneControls :
    -- positive witness
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      capacity True True True ∧ exercise True True True ∧ grounding True True True ∧
      knows False True True) ∧
    -- `a30c5963` fails: the source is composite and not its own being
    (¬ roots True ∧ ownUnlimited True False ∧ every True True ∧ wisdomPure True ∧
      capacity False True False ∧ exercise False False False ∧ grounding False False False ∧
      ¬ knows False False False) ∧
    -- `26e8e6ed` fails: an unlimited source that is not its own being
    (roots False ∧ ¬ ownUnlimited False False ∧ every True True ∧ wisdomPure True ∧
      capacity False True False ∧ exercise False False False ∧ grounding False False False ∧
      ¬ knows False False False) ∧
    -- `fe67d766` fails: wisdom is pure and the root lacks it
    (roots False ∧ ownUnlimited False True ∧ ¬ every False True ∧ wisdomPure True ∧
      capacity True False False ∧ exercise True False False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- purity fails: wisdom is not pure and the root lacks it
    (roots False ∧ ownUnlimited False True ∧ every False False ∧ ¬ wisdomPure False ∧
      capacity True False False ∧ exercise True False False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- `WisdomSelfCapacity` fails: wisdom without a self-directed capacity
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      ¬ capacity True True False ∧ exercise True False False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- `SelfCapacityExercisedOrPotent` fails: a dormant self-directed capacity
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      capacity True True True ∧ ¬ exercise True True False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- `TrueSelfApprehensionGrounded` fails: correct apprehension without grounding
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      capacity True True True ∧ exercise True True True ∧ ¬ grounding True True False ∧
      ¬ knows False True False) := by
  sorry

/-- Step two: a positive witness and, for each of its four premises, an
assignment on the same carrier where that premise fails, the three others hold
and GOD_4 HAS_INTELLECT_1 fails. In the reach row GOD_4 names the effect, which
is not an ancestor of the root. In the first-root row the root is in potency,
so step one holds vacuously. -/
theorem stepTwoControls :
    (first False ∧ reach true ∧ knows False True True ∧ recognition true True True True ∧
      godIntellect true True) ∧
    (¬ first True ∧ reach true ∧ knows True False False ∧ recognition true False False False ∧
      ¬ godIntellect true False) ∧
    (first False ∧ ¬ reach false ∧ knows False True True ∧ recognition false True True True ∧
      ¬ godIntellect false True) ∧
    (first False ∧ reach true ∧ ¬ knows False False False ∧
      recognition true False False False ∧ ¬ godIntellect true False) ∧
    (first False ∧ reach true ∧ knows False True True ∧ ¬ recognition true False True True ∧
      ¬ godIntellect true False) := by
  sorry

/-- Constitutive-admissibility controls on the #1970 determinations, stated
for the sufficiency direction `ExclusionFreeAdmissible` that the registered
derivations use. Each row names the requirement relation, the family and which
premise fails:

1. positive witness: only the nonpure `limiter` requires a lack (of `noesis`);
   member grounding (hence sufficiency), the purity premise and joint
   compossibility hold, and the root with every pure determination has an
   admissible profile;
2. the triple family with no requirement: sufficiency fails (an irreducibly
   holistic prohibition), the purity premise holds, joint compossibility fails;
3. the SAME triple family with `noesis` requiring the joint lack of `a` and
   `b`: member grounding and sufficiency hold, the purity premise fails, joint
   compossibility fails;
4. and 5. the family without `noesis`, with no requirement (sufficiency fails)
   or with `noesis` requiring its own lack (purity fails): pure admissibility
   fails;
6. the root's profile with the nonpure `limiter` and `noesis`: member grounding
   and purity hold, root purity and root-profile admissibility fail;
7. the all-pure root profile in the triple family: root purity holds and
   root-profile admissibility fails;
8. strictness: with every profile admissible and `noesis` requiring its own
   lack, sufficiency holds and member grounding fails. -/
theorem constitutiveControls :
    (MemberGroundedAdmissibility (ExclusionFree limiterExcludesNoesis) limiterExcludesNoesis ∧
      ExclusionFreeAdmissible (ExclusionFree limiterExcludesNoesis) limiterExcludesNoesis ∧
      PureRequiresNoPureLack limiterExcludesNoesis isPure ∧
      PureExtensionsAdmissible (ExclusionFree limiterExcludesNoesis) isPure ∧
      rootPure TruthCore.Causality.SourceIntellectControls.ProfileControls.pure ∧
      rootAdm (ExclusionFree limiterExcludesNoesis)
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) ∧
    (¬ ExclusionFreeAdmissible bruteTriple noRequirement ∧
      PureRequiresNoPureLack noRequirement isPure ∧
      ¬ PureExtensionsAdmissible bruteTriple isPure) ∧
    (MemberGroundedAdmissibility bruteTriple noesisExcludesPair ∧
      ExclusionFreeAdmissible bruteTriple noesisExcludesPair ∧
      ¬ PureRequiresNoPureLack noesisExcludesPair isPure ∧
      PairwiseAdmitted bruteTriple ∧
      ¬ PureExtensionsAdmissible bruteTriple isPure) ∧
    (¬ ExclusionFreeAdmissible noNoesis noRequirement ∧
      ¬ PureDeterminationsAdmissible noNoesis isPure) ∧
    (ExclusionFreeAdmissible noNoesis noesisSelfExcluding ∧
      ¬ PureRequiresNoPureLack noesisSelfExcluding isPure ∧
      ¬ PureDeterminationsAdmissible noNoesis isPure) ∧
    (ExclusionFreeAdmissible (ExclusionFree limiterExcludesNoesis) limiterExcludesNoesis ∧
      PureRequiresNoPureLack limiterExcludesNoesis isPure ∧
      ¬ rootPure (insert Determination.limiter effect) ∧
      ¬ rootAdm (ExclusionFree limiterExcludesNoesis) (insert Determination.limiter effect)) ∧
    (rootPure TruthCore.Causality.SourceIntellectControls.ProfileControls.pure ∧
      ¬ rootAdm bruteTriple TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) ∧
    (ExclusionFreeAdmissible anyProfile noesisSelfExcluding ∧
      ¬ MemberGroundedAdmissibility anyProfile noesisSelfExcluding) := by
  sorry

/-- Strictness of member grounding over its sufficiency direction: with every
profile admissible and `noesis` requiring its own lack, the sufficiency
direction holds and member grounding fails. -/
theorem strictSeparates : StrictSeparates := by
  sorry

end TruthCore.Results.Causality.RootPerfectionIntellect
