import TruthCore.Ethics.Euthyphro
import TruthCore.Ethics.EuthyphroDilemma

/-!
# Euthyphro modal test: results

Analyst formulation; attribution deferred. See `TruthCore.Ethics.Euthyphro`.
-/

namespace TruthCore.Results.Ethics.Euthyphro

open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
open TruthCore.Logic
open TruthCore.Ethics.Euthyphro
open TruthCore.Ethics.EuthyphroDilemma

/-- Strength order: supervenience of goodness on the natural base across the
family gives invariance of base goodness under nature-fixed approval variation. -/
theorem invarianceFromSupervenience {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s)
    (hSupervenes : GoodnessSupervenes m) : GoodnessInvariantUnderApprovalVariation m := by
  sorry

/-- Euthyphro core: if base goodness is invariant under nature-fixed variation
and the assessor's approvals differ in some nature-fixed profile, approval does
not coextend with goodness throughout the nature-fixed profiles. -/
theorem approvalNotGroundFromInvariance {f : Frame} {s : DefinitionSpace f}
    (m : ProfileFamily s)
    (hInvariant : GoodnessInvariantUnderApprovalVariation m)
    (hVaries : ApprovalVariesWithNaturesFixed m) : ApprovalDoesNotGround m := by
  sorry

/-- With the rigidity bridge, the modal failure becomes failure of the named
extensional approval account in the base profile. -/
theorem approvalFailsFromNotGround {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s)
    (hNotGround : ApprovalDoesNotGround m)
    (hTransfer : ApprovalCorrectnessTransfers m) : ApprovalAccountFails s := by
  sorry

/-- The divine-command theorist's price: a command theory on which approval
coextends with goodness in every nature-fixed profile, and which accepts
invariance, must hold that the assessor's approvals are fixed by the natures. -/
theorem dctGroundPrice {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s)
    (hGround : ApprovalGroundsAcrossNatureFixed m)
    (hInvariant : GoodnessInvariantUnderApprovalVariation m) : ApprovalsFixedByNatures m := by
  sorry

/-- Strength order: extensional failure of the approval account gives the weak
disjunctive premise. -/
theorem approvalFailsWeakens {f : Frame} (s : DefinitionSpace f)
    (hFails : ApprovalAccountFails s) : ApprovalFailsOrCoincidesWithDue s := by
  sorry

/-- Strength order: coextension of the approval and due-actuality accounts gives
the weak disjunctive premise. -/
theorem approvalCoincidesWeakens {f : Frame} (s : DefinitionSpace f)
    (hCoincides : ApprovalCoincidesWithDue s) : ApprovalFailsOrCoincidesWithDue s := by
  sorry

/-- The correct-support elimination needs only the weak approval premise: the
approval account may be correct, provided it then coextends with due actuality. -/
theorem dueFromWeakApprovalPremise (f : Frame) (s : DefinitionSpace f)
    (hSupport : CorrectAccountSupport s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalFailsOrCoincidesWithDue s) :
    DueActualityThesis f := by
  sorry

theorem controls : Controls := by
  sorry

/-! ## Is the dilemma exhaustive? -/

/-- Coverage of the dilemma: with excluded middle, distinctness of goodness from
God and his nature, and dependence on God of other distinct things only through
his approval, goodness is an independent standard or constituted by approval. -/
theorem hornsCoverFromDistinctness (d : DependenceFrame) (hExcludedMiddle : ExcludedMiddle)
    (hDistinct : GoodnessDistinctFromGod d)
    (hThrough : DistinctDependenceThroughApproval d) : HornsCover d := by
  sorry

/-- Identity reply: if goodness is God's nature, God is his nature, God's
approving depends on that nature and dependence is asymmetric, neither horn
holds. Simplicity is used only against horn 1; asymmetry and approval
following nature only against horn 2. -/
theorem neitherHornFromIdentity (d : DependenceFrame)
    (hIdentity : GoodnessIsDivineNature d) (hSimple : GodIsOwnNature d)
    (hFollows : ApprovalFollowsNature d) (hAsymmetric : DependenceAsymmetric d) :
    NeitherHorn d := by
  sorry

theorem dilemmaControls : DilemmaControls := by
  sorry

end TruthCore.Results.Ethics.Euthyphro
