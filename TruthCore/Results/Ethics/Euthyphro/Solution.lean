module

public import TruthCore.Ethics.Euthyphro
public import TruthCore.Ethics.EuthyphroDilemma

/-!
# Euthyphro modal test: results

Analyst formulation; attribution deferred. See `TruthCore.Ethics.Euthyphro`.
-/

@[expose] public section

namespace TruthCore.Results.Ethics.Euthyphro

open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
open TruthCore.Logic
open TruthCore.Ethics.Euthyphro
open TruthCore.Ethics.EuthyphroDilemma

/-- Strength order: supervenience of goodness on the natural base across the
family gives invariance of base goodness under nature-fixed approval variation. -/
theorem invarianceFromSupervenience {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s)
    (hSupervenes : GoodnessSupervenes m) : GoodnessInvariantUnderApprovalVariation m :=
  fun v hv => hSupervenes m.base v hv

/-- Euthyphro core: if base goodness is invariant under nature-fixed variation
and the assessor's approvals differ in some nature-fixed profile, approval does
not coextend with goodness throughout the nature-fixed profiles. -/
theorem approvalNotGroundFromInvariance {f : Frame} {s : DefinitionSpace f}
    (m : ProfileFamily s)
    (hInvariant : GoodnessInvariantUnderApprovalVariation m)
    (hVaries : ApprovalVariesWithNaturesFixed m) : ApprovalDoesNotGround m := by
  intro hGround
  obtain ⟨v, hv, hDiffer⟩ := hVaries
  apply hDiffer
  intro x p
  exact (hGround m.base (fun _ _ => Iff.rfl) x p).symm.trans
    ((hInvariant v hv x p).trans (hGround v hv x p))

/-- With the rigidity bridge, the modal failure becomes failure of the named
extensional approval account in the base profile. -/
theorem approvalFailsFromNotGround {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s)
    (hNotGround : ApprovalDoesNotGround m)
    (hTransfer : ApprovalCorrectnessTransfers m) : ApprovalAccountFails s := by
  intro hCorrect
  apply hNotGround
  apply hTransfer
  intro x p
  exact (m.baseGood x p).trans
    ((hCorrect x p).trans ((s.approvalMeaning x p).trans (m.baseApproves x p).symm))

/-- The equivalence behind the divine-command theorist's price: under approval
as ground over the nature-fixed profiles, base-goodness invariance holds exactly
when the assessor's approvals are fixed by the natures. -/
theorem groundedInvarianceEquivalence {f : Frame} {s : DefinitionSpace f}
    (m : ProfileFamily s) (hGround : ApprovalGroundsAcrossNatureFixed m) :
    GroundedInvarianceNeedsNatureFixedApproval m := by
  have hBase := hGround m.base (fun _ _ => Iff.rfl)
  constructor
  · intro hInvariant v hv x p
    exact (hBase x p).symm.trans ((hInvariant v hv x p).trans (hGround v hv x p))
  · intro hFixed v hv x p
    exact (hBase x p).trans ((hFixed v hv x p).trans (hGround v hv x p).symm)

/-- The divine-command theorist's price: a command theory on which approval
coextends with goodness in every nature-fixed profile, and which accepts
invariance, must hold that the assessor's approvals are fixed by the natures. -/
theorem dctGroundPrice {f : Frame} {s : DefinitionSpace f} (m : ProfileFamily s)
    (hGround : ApprovalGroundsAcrossNatureFixed m)
    (hInvariant : GoodnessInvariantUnderApprovalVariation m) : ApprovalsFixedByNatures m :=
  (groundedInvarianceEquivalence m hGround).1 hInvariant

/-- Strength order: extensional failure of the approval account gives the weak
disjunctive premise. -/
theorem approvalFailsWeakens {f : Frame} (s : DefinitionSpace f)
    (hFails : ApprovalAccountFails s) : ApprovalFailsOrCoincidesWithDue s :=
  Or.inl hFails

/-- Strength order: coextension of the approval and due-actuality accounts gives
the weak disjunctive premise. -/
theorem approvalCoincidesWeakens {f : Frame} (s : DefinitionSpace f)
    (hCoincides : ApprovalCoincidesWithDue s) : ApprovalFailsOrCoincidesWithDue s :=
  Or.inr hCoincides

/-- The correct-support elimination needs only the weak approval premise: the
approval account may be correct, provided it then coextends with due actuality. -/
theorem dueFromWeakApprovalPremise (f : Frame) (s : DefinitionSpace f)
    (hSupport : CorrectAccountSupport s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalFailsOrCoincidesWithDue s) :
    DueActualityThesis f := by
  obtain ⟨d, _, hDescribes, hNamed⟩ := hSupport hCorrect
  have toThesis : CorrectAccount s s.dueAccount → DueActualityThesis f :=
    fun h x p => (h x p).trans (s.dueMeaning x p)
  rcases hNamed with hDue | hFeat | hAppr
  · exact toThesis (fun x p => (hDescribes x p).trans (hDue x p))
  · exact absurd (fun x p => (hDescribes x p).trans (hFeat x p)) hFeature
  · have hApprCorrect : CorrectAccount s s.approvalAccount :=
      fun x p => (hDescribes x p).trans (hAppr x p)
    rcases hApproval with hFails | hCoincides
    · exact absurd hApprCorrect hFails
    · exact toThesis (fun x p => (hApprCorrect x p).trans (hCoincides x p))

theorem exactSpace_approvalCorrect : ¬ ApprovalAccountFails exactSpace :=
  fun h => h (fun _ _ => Iff.rfl)

theorem knife_existence_good : artifactGood .knife .existence := ⟨trivial, trivial⟩

theorem knife_not_counterweight : (Bearer.knife = Bearer.counterweight) → False :=
  fun h => Bearer.noConfusion h

theorem controls : Controls := by
  refine ⟨?robust, ?stable, ?equivalence, ?rigid, ?adamsPrice, ?divine, ?human, ?coincident, ?voluntarist, ?adams⟩
  case robust =>
    intro f s m hRobust w v hSame x p
    exact (hRobust w x p).trans
      (⟨fun ⟨d, h⟩ => ⟨d, (hSame x p).1 h⟩, fun ⟨d, h⟩ => ⟨d, (hSame x p).2 h⟩⟩ :
        (Due f x p ∧ m.hasAt w x p) ↔ (Due f x p ∧ m.hasAt v x p)) |>.trans (hRobust v x p).symm
  case stable =>
    intro f s m
    constructor
    · intro hInvariant a v
      exact (hInvariant v.1 v.2 a.1 a.2).symm
    · intro hStable v hv x p
      exact (hStable (x, p) ⟨v, hv⟩).symm
  case equivalence =>
    intro f s m hGround
    exact groundedInvarianceEquivalence m hGround
  case rigid =>
    intro f s m hRigid hTransfer
    obtain ⟨hBase, hInvariant, hVaries⟩ := hRigid
    exact approvalNotGroundFromInvariance m hInvariant hVaries (hTransfer hBase)
  case adamsPrice =>
    intro f s m c hTheory hVaries hInvariant
    obtain ⟨hObligation, _⟩ := hTheory
    obtain ⟨v, hv, hDiffer⟩ := hVaries
    exact hDiffer fun a =>
      (hObligation m.base a).symm.trans ((hInvariant v hv a).trans (hObligation v a))
  case divine =>
    have hRobust : RobustDueAccount divineFamily := fun _ _ _ => Iff.rfl
    have hSupervenes : GoodnessSupervenes divineFamily :=
      fun w v hSame x p =>
        (hRobust w x p).trans
          ((⟨fun ⟨d, h⟩ => ⟨d, (hSame x p).1 h⟩, fun ⟨d, h⟩ => ⟨d, (hSame x p).2 h⟩⟩ :
            (Due (artifactWithGood false) x p ∧ divineFamily.hasAt w x p) ↔
              (Due (artifactWithGood false) x p ∧ divineFamily.hasAt v x p)).trans
            (hRobust v x p).symm)
    have hFixed : ApprovalsFixedByNatures divineFamily :=
      fun v hv => hSupervenes divineFamily.base v hv
    have hAdmissibleDue : exactSpace.admissible .due := fun h => Proposal.noConfusion h
    refine ⟨hRobust, hSupervenes, fun _ _ _ _ => Iff.rfl, hFixed,
      fun ⟨v, hv, hDiffer⟩ => hDiffer (hFixed v hv), exactSpace_approvalCorrect,
      fun _ _ => Iff.rfl, Or.inr (fun _ _ => Iff.rfl),
      fun _ => ⟨.due, hAdmissibleDue, fun _ _ => Iff.rfl, Or.inl (fun _ _ => Iff.rfl)⟩,
      ⟨.due, hAdmissibleDue, fun _ _ => Iff.rfl⟩, ?_, fun _ _ => Iff.rfl⟩
    intro h
    exact ((h .knife .mass).2 trivial).1
  case human =>
    have hInvariant : GoodnessInvariantUnderApprovalVariation humanFamily :=
      fun _ _ _ _ => Iff.rfl
    have hVaries : ApprovalVariesWithNaturesFixed humanFamily :=
      ⟨true, fun _ _ => Iff.rfl, fun h =>
        knife_not_counterweight ((h .knife .existence).2 knife_existence_good).1⟩
    have hTransfer : ApprovalCorrectnessTransfers humanFamily := fun h =>
      absurd ((h .knife .existence).1 knife_existence_good).1 knife_not_counterweight
    have hNot := approvalNotGroundFromInvariance humanFamily hInvariant hVaries
    exact ⟨hInvariant, hVaries, hTransfer, hNot,
      approvalFailsFromNotGround humanFamily hNot hTransfer, fun h =>
        knife_not_counterweight ((h .knife .existence).2 knife_existence_good).1⟩
  case coincident =>
    have hInvariant : GoodnessInvariantUnderApprovalVariation coincidentFamily :=
      fun _ _ _ _ => Iff.rfl
    have hVaries : ApprovalVariesWithNaturesFixed coincidentFamily :=
      ⟨true, fun _ _ => Iff.rfl, fun h =>
        knife_not_counterweight ((h .knife .existence).1 knife_existence_good).1⟩
    refine ⟨hInvariant, hVaries,
      approvalNotGroundFromInvariance coincidentFamily hInvariant hVaries, ?_,
      exactSpace_approvalCorrect, ⟨fun _ _ => Iff.rfl, hInvariant, hVaries⟩⟩
    intro hTransfer
    have hGround := hTransfer (fun _ _ => Iff.rfl)
    exact knife_not_counterweight
      ((hGround true (fun _ _ => Iff.rfl) .knife .existence).1 knife_existence_good).1
  case voluntarist =>
    refine ⟨⟨true, fun _ _ => Iff.rfl, fun h =>
        knife_not_counterweight ((h .knife .existence).1 knife_existence_good).1⟩,
      fun _ _ _ _ => Iff.rfl, ?_⟩
    intro hInvariant
    exact knife_not_counterweight
      ((hInvariant true (fun _ _ => Iff.rfl) .knife .existence).1 knife_existence_good).1
  case adams =>
    have hTheory : ModifiedCommandTheory adamsLayer :=
      ⟨fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
    have hVaries : CommandVariesWithNaturesFixed adamsLayer :=
      ⟨true, fun _ _ => Iff.rfl, fun h => Deed.noConfusion ((h .rite).1 trivial)⟩
    refine ⟨hTheory, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, hVaries, ?_⟩
    intro hInvariant
    obtain ⟨v, hv, hDiffer⟩ := hVaries
    exact hDiffer fun a =>
      (hTheory.1 adamsFamily.base a).symm.trans ((hInvariant v hv a).trans (hTheory.1 v a))

/-! ## Is the dilemma exhaustive? -/


/-- Coverage of the dilemma: with excluded middle, distinctness of goodness from
God and his nature, and dependence on God of other distinct things only through
his approval, goodness is an independent standard or constituted by approval. -/
theorem hornsCoverFromDistinctness (d : DependenceFrame) (hExcludedMiddle : ExcludedMiddle)
    (hDistinct : GoodnessDistinctFromGod d)
    (hThrough : DistinctDependenceThroughApproval d) : HornsCover d := by
  rcases hExcludedMiddle (d.goodness = d.approval) with hEq | hNe
  · exact Or.inr (Or.inr hEq)
  rcases hExcludedMiddle (d.DependsFor d.goodness d.god) with hDep | hNoDep
  · exact Or.inr (Or.inl (hThrough _ hDistinct.1 hDistinct.2 hNe hDep))
  · exact Or.inl ⟨hDistinct.1, hNoDep⟩

/-- Identity reply: if goodness is God's nature, God is his nature, God's
approving depends on that nature and dependence is asymmetric, neither horn
holds. Simplicity is used only against horn 1; asymmetry and approval
following nature only against horn 2. -/
theorem neitherHornFromIdentity (d : DependenceFrame)
    (hIdentity : GoodnessIsDivineNature d) (hSimple : GodIsOwnNature d)
    (hFollows : ApprovalFollowsNature d) (hAsymmetric : DependenceAsymmetric d) :
    NeitherHorn d := by
  refine ⟨fun hIndependent => hIndependent.1 (hIdentity.trans hSimple), ?_⟩
  rintro (hDep | hEq)
  · have hNatureDep : d.DependsFor d.nature d.approval := by
      rw [hIdentity] at hDep
      exact hDep
    exact hAsymmetric _ _ hFollows hNatureDep
  · have hSame : d.approval = d.nature := hEq.symm.trans hIdentity
    have hSelf : d.DependsFor d.nature d.nature := by
      have h := hFollows
      unfold ApprovalFollowsNature at h
      rw [hSame] at h
      exact h
    exact hAsymmetric _ _ hSelf hSelf

theorem dilemmaControls : DilemmaControls := by
  refine ⟨?relocation, ?collapse, ?identity, ?exemplar, ?nonSimple, ?voluntarist,
    ?contingent, ?property⟩
  case relocation =>
    intro n hIdentity hNecessary ⟨w, v, hDiffer⟩
    exact hDiffer ((hIdentity w).trans ((hNecessary w v).trans (hIdentity v).symm))
  case collapse =>
    intro p hGod hUniversal hProperty
    rw [hGod, hUniversal]
    exact hProperty
  case identity =>
    have hId : GoodnessIsDivineNature identityFrame := rfl
    have hSimple : GodIsOwnNature identityFrame := rfl
    have hFollows : ApprovalFollowsNature identityFrame := ⟨rfl, rfl⟩
    have hAsym : DependenceAsymmetric identityFrame := by
      intro x y ⟨_, hy⟩ ⟨hy', _⟩
      exact Item.noConfusion (hy.symm.trans hy')
    refine ⟨hId, hSimple, hFollows, hAsym, ?_, fun h => h.1 rfl,
      neitherHornFromIdentity identityFrame hId hSimple hFollows hAsym⟩
    intro x _ _ hApproval ⟨hx, _⟩
    exact absurd hx hApproval
  case exemplar =>
    refine ⟨⟨fun h => Item.noConfusion h, fun h => Item.noConfusion h⟩,
      ⟨Or.inl rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro x y ⟨_, hy⟩ ⟨hy', _⟩
      rcases hy' with h | h
      · exact Item.noConfusion (hy.symm.trans h)
      · exact Item.noConfusion (hy.symm.trans h)
    · intro h
      have hStandard := h .standard (fun h => Item.noConfusion h) (fun h => Item.noConfusion h)
        (fun h => Item.noConfusion h) ⟨Or.inr rfl, rfl⟩
      exact Item.noConfusion hStandard.2
    · refine ⟨fun hIndependent => hIndependent.2 ⟨Or.inr rfl, rfl⟩, ?_⟩
      rintro (⟨_, h⟩ | h)
      · exact Item.noConfusion h
      · exact Item.noConfusion h
  case nonSimple =>
    refine ⟨rfl, ⟨rfl, rfl⟩, ?_, fun h => Item.noConfusion h,
      ⟨fun h => Item.noConfusion h, fun ⟨h, _⟩ => Item.noConfusion h⟩⟩
    intro x y ⟨_, hy⟩ ⟨hy', _⟩
    exact Item.noConfusion (hy.symm.trans hy')
  case voluntarist =>
    refine ⟨⟨fun h => Item.noConfusion h, fun h => Item.noConfusion h⟩, ?_,
      Or.inl ⟨rfl, Or.inl rfl⟩⟩
    intro x _ _ _ ⟨hx, _⟩
    exact ⟨hx, Or.inl rfl⟩
  case contingent =>
    exact ⟨fun _ => rfl, fun h => Bool.noConfusion (h true false),
      ⟨true, false, fun h => Bool.noConfusion h⟩⟩
  case property =>
    exact ⟨rfl, fun h => Item.noConfusion h, rfl, fun h => Item.noConfusion h⟩


end TruthCore.Results.Ethics.Euthyphro
