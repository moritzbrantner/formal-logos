module

public import TruthCore.Causality.IntentionalUnity
public import TruthCore.Results.Causality.ImitabilityPlurality.Solution

@[expose] public section

namespace TruthCore.Results.Causality.IntentionalUnity

open TruthCore.Causality.IntentionalUnity
open TruthCore.Causality.ImitabilityGrounding
  (FactPriorityAsymmetricAt FactPriorityTransitiveAt)
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Causality.IntentionalExemplarExtension.ObjectiveEminence
  (ConstitutivelySimple)

private theorem pathToEdge {W B F : Type} {I : Arena W B F} {w : W}
    (hTrans : FactPriorityTransitiveAt I w) {p q : F}
    (h : Relation.TransGen (I.explains w) p q) : I.explains w p q := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact hTrans _ _ _ ih h

/-- Posterior specifications exclude distinct real realizers only under the
explicit constitutive-priority bridge; complete coverage then gives simplicity. -/
theorem posteriorConstitutionLaws : PosteriorConstitutionLaws := by
  intro W B C A F I w real b whole eligible realize specification target
    hAsym hTrans hPosterior hContribute
  have hCollapse : ∀ c ∈ eligible, real b (realize c) → realize c = whole := by
    intro c hc hReal
    classical
    by_contra hDistinct
    have hForward := pathToEdge hTrans (hPosterior c hc)
    exact (TruthCore.Explanation.PriorityOmission.priorExcludesSelfAndPosterior
      (fun f h => hAsym f f h h)
      (fun {p q r} h₁ h₂ => hTrans p q r h₁ h₂) hForward).2
        (hContribute c hc hReal hDistinct)
  refine ⟨hCollapse, ?_⟩
  intro hCover a d ha hd
  obtain ⟨c, hc, hec⟩ := hCover a ha
  obtain ⟨e, he, hee⟩ := hCover d hd
  have hcWhole := hCollapse c hc (hec.symm ▸ ha)
  have heWhole := hCollapse e he (hee.symm ▸ hd)
  exact hec.symm.trans (hcWhole.trans (heWhole.symm.trans hee))

/-- Simplicity, intrinsic realization and complete token individuation yield
at most one operation at the same bearer and exercise, using the earlier law. -/
theorem localOperationUnityLaws : LocalOperationUnityLaws := by
  intro W B T R O E A K w occurs bearer exercise real realize b e
    hSimple hIntrinsic hComplete
  refine TruthCore.Results.Causality.ImitabilityPlurality.identityAndRankingLaws.1
    B {o // OperationAt K w occurs bearer exercise b e o} A real b
    (fun o => realize o.val) hSimple ?_ ?_
  · intro o
    exact hIntrinsic o.val o.property
  · intro a d hRealizer
    apply Subtype.ext
    apply hComplete
    exact Prod.ext (a.property.2.2.1.trans d.property.2.2.1.symm)
      (Prod.ext (a.property.2.2.2.trans d.property.2.2.2.symm) hRealizer)

section Priority

open TruthCore.Causality.IntentionalUnity.Control

private theorem ltAsymmetric : FactPriorityAsymmetricAt (arena Nat.lt) () :=
  fun _ _ h h' => Nat.lt_asymm h h'

private theorem ltTransitive : FactPriorityTransitiveAt (arena Nat.lt) () :=
  fun _ _ _ h h' => Nat.lt_trans h h'

private theorem gtAsymmetric : FactPriorityAsymmetricAt (arena (fun p q => q < p)) () :=
  fun _ _ h h' => Nat.lt_asymm h h'

private theorem gtTransitive : FactPriorityTransitiveAt (arena (fun p q => q < p)) () :=
  fun _ _ _ h h' => Nat.lt_trans h' h

private theorem simpleWhole : ConstitutivelySimple simpleReal true := by
  intro a b ha hb
  exact ha.2.trans hb.2.symm

private theorem twoNotSimple : ¬ ConstitutivelySimple twoReal true := by
  intro h
  have h01 : (0 : Nat) = 1 := h 0 1 ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩
  exact (by decide : (0 : Nat) ≠ 1) h01

private theorem manyNotSimple : ¬ ConstitutivelySimple manyReal true := by
  intro h
  have h01 : (0 : Nat) = 1 := h 0 1 rfl rfl
  exact (by decide : (0 : Nat) ≠ 1) h01

private theorem posterior :
    PosteriorSpecificationsAt (arena Nat.lt) () Set.univ specification 0 := by
  intro n _
  apply Relation.TransGen.single
  change 0 < n + 2
  omega

private theorem commonContribution (rel : Nat → Nat → Prop)
    (real : Bool → Nat → Prop) :
    DistinctRealizersContributeAt (arena rel) () real true 0
      Set.univ commonRealizer specification 0 := by
  intro n _ _ hDistinct
  exact (hDistinct rfl).elim

private theorem simpleCoverage :
    RealizersCoverConstituents simpleReal true Set.univ commonRealizer := by
  intro a ha
  exact ⟨0, Set.mem_univ _, ha.2.symm⟩

private theorem splitCoverage :
    RealizersCoverConstituents twoReal true Set.univ splitRealizer := by
  intro a ha
  rcases ha.2 with h | h
  · exact ⟨0, Set.mem_univ _, by simpa [splitRealizer] using h.symm⟩
  · exact ⟨1, Set.mem_univ _, by simpa [splitRealizer] using h.symm⟩

private theorem posteriorWhole : PosteriorWhole := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, (fun _ => ⟨rfl, rfl⟩), posterior,
    commonContribution Nat.lt simpleReal, simpleCoverage, simpleWhole⟩
  · intro n
    unfold specification
    omega
  · intro n
    change n + 2 ≠ 0 ∧ n + 2 ≠ 1
    exact ⟨by omega, by omega⟩

private theorem omitCoverage : OmitCoverage := by
  refine ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, posterior,
    commonContribution Nat.lt twoReal, ?_, twoNotSimple⟩
  intro h
  obtain ⟨n, _, hn⟩ := h 1 ⟨rfl, Or.inr rfl⟩
  exact (by decide : (0 : Nat) ≠ 1) hn

private theorem omitContribution : OmitContribution := by
  refine ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, posterior,
    splitCoverage, ?_, twoNotSimple⟩
  intro h
  have hBack := h 1 (Set.mem_univ _) (by simp [twoReal, splitRealizer])
    (by simp [splitRealizer])
  exact Nat.not_lt_zero _ hBack

private theorem omitPosteriority : OmitPosteriority := by
  refine ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, ?_, splitCoverage,
    ?_, twoNotSimple⟩
  · intro n _ _ _
    change 0 < n + 2
    omega
  · intro h
    have hBack := pathToEdge gtTransitive (h 0 (Set.mem_univ _))
    exact Nat.not_lt_zero _ hBack

private theorem differentExplanandum : DifferentExplanandum := by
  intro n
  change 0 < n + 2 ∧ n + 2 < n + 3 ∧ 0 < n + 3 ∧ ¬ n + 2 < 0
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem existingAccounts : ExistingAccounts.Application := by
  have hBoth := TruthCore.Results.Causality.ImitabilityPlurality.intrinsicGroundingControls
  obtain ⟨_, hNoncognitive, hCognitive, _⟩ := hBoth
  have hAccount : ∀ personal,
      TruthCore.Causality.ImitabilityPlurality.PositiveControl.SourceBasedAccount personal
        TruthCore.Causality.ImitabilityPlurality.PositiveControl.values := by
    intro personal
    cases personal
    · exact hNoncognitive
    · exact hCognitive
  intro personal v
  obtain ⟨_, _, _, _, _, hMode, _, _, _, hPriority, _, _, _⟩ := hAccount personal
  let I := TruthCore.Causality.ImitabilityPlurality.PositiveControl.arena personal
    TruthCore.Causality.ImitabilityPlurality.PositiveControl.values
  have hPosterior : PosteriorSpecificationsAt I v Set.univ
      TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact.mode
      TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact.nature :=
    fun o _ => Relation.TransGen.single (hMode v o).2
  have hContribute : DistinctRealizersContributeAt I v
      TruthCore.Causality.PossibiliaContent.Control.realBlob true
      TruthCore.Causality.AxiarchicFoundation.Control.Item.blob Set.univ
      TruthCore.Causality.ImitabilityPlurality.Control.realizer
      TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact.mode
      TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact.nature := by
    intro o _ _ hDistinct
    exact (hDistinct rfl).elim
  have hCover : RealizersCoverConstituents
      TruthCore.Causality.PossibiliaContent.Control.realBlob true Set.univ
      TruthCore.Causality.ImitabilityPlurality.Control.realizer := by
    intro a ha
    exact ⟨TruthCore.Causality.SelectionScope.Outcome.c, Set.mem_univ _, ha.2.symm⟩
  refine ⟨hPosterior, hContribute, hCover, ?_⟩
  exact (posteriorConstitutionLaws Bool Bool TruthCore.Causality.SelectionScope.Outcome
    TruthCore.Causality.AxiarchicFoundation.Control.Item
    TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact I v
    TruthCore.Causality.PossibiliaContent.Control.realBlob true
    TruthCore.Causality.AxiarchicFoundation.Control.Item.blob Set.univ
    TruthCore.Causality.ImitabilityPlurality.Control.realizer
    TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact.mode
    TruthCore.Causality.ImitabilityPlurality.PositiveControl.Fact.nature
    (hPriority v).1 (hPriority v).2 hPosterior hContribute).2 hCover

/-- Countable priority witnesses, omitted semantic bridges and application
to both existing restored source-based accounts in their exact earlier scope. -/
theorem priorityControls : Control.PriorityControls := by
  refine ⟨?_, ⟨rfl, rfl⟩, ltAsymmetric, ltTransitive, gtAsymmetric,
    gtTransitive, posteriorWhole, omitCoverage, omitContribution,
    omitPosteriority, differentExplanandum, existingAccounts⟩
  intro rel
  exact ⟨fun _ _ => Iff.rfl, fun _ _ _ _ => ⟨trivial, trivial⟩⟩

end Priority

section Operations

open TruthCore.Causality.IntentionalUnity.Control

private theorem selected (n : Nat) :
    OperationAt frame () occurs bearer exercise true () n :=
  ⟨trivial, trivial, rfl, rfl⟩

private theorem localTokensNotSubsingleton :
    ¬ Subsingleton {o // OperationAt frame () occurs (bearer : Nat → Bool) exercise true () o} := by
  intro h
  have h01 : (0 : Nat) = 1 := congrArg Subtype.val
    (h.elim ⟨0, selected 0⟩ ⟨1, selected 1⟩)
  exact (by decide : (0 : Nat) ≠ 1) h01

private theorem realizationComplete : OperationProfileComplete (bearer : Nat → Bool) exercise id := by
  intro a b h
  exact congrArg (fun p : Bool × Unit × Nat => p.2.2) h

private theorem arbitraryObjects : ArbitraryObjects := by
  intro C selectedObjects
  refine ⟨⟨trivial, trivial, rfl, rfl⟩, ?_, ?_, ?_, fun _ => Iff.rfl⟩
  · intro a b _
    exact Subsingleton.elim a b
  · intro _ _
    exact ⟨rfl, rfl⟩
  · intro _ _
    rfl

private theorem repeatedOperations : RepeatedOperations := by
  have hComplete : OperationProfileComplete (bearer : Nat → Bool) id whole := by
    intro a b h
    exact congrArg (fun p : Bool × Nat × Nat => p.2.1) h
  have hIntrinsic : ∀ n, IntrinsicOperationRealizersAt frame () occurs
      (bearer : Nat → Bool) id simpleReal whole true n :=
    fun _ _ _ => ⟨rfl, rfl⟩
  refine ⟨hComplete, (fun _ => ⟨trivial, trivial, rfl, rfl⟩), hIntrinsic,
    ?_, (fun _ _ _ => Iff.rfl), Or.inl rfl, Or.inr rfl, ?_⟩
  · intro n
    exact localOperationUnityLaws Unit Bool Unit Unit Nat Nat Nat frame ()
      occurs bearer id simpleReal whole true n simpleWhole (hIntrinsic n) hComplete
  · intro h
    exact (by decide : (0 : Nat) ≠ 1) (h.elim 0 1)

private theorem omitOperationIndividuation : OmitOperationIndividuation := by
  refine ⟨(fun _ _ => ⟨rfl, rfl⟩), ?_, localTokensNotSubsingleton⟩
  intro h
  have h01 : (0 : Nat) = 1 := h (show
    (bearer (0 : Nat), exercise (0 : Nat), whole (0 : Nat)) =
      (bearer (1 : Nat), exercise (1 : Nat), whole (1 : Nat)) from rfl)
  exact (by decide : (0 : Nat) ≠ 1) h01

private theorem omitIntrinsicRealization : OmitIntrinsicRealization := by
  refine ⟨realizationComplete, ?_, localTokensNotSubsingleton⟩
  intro h
  have hOne := h 1 (selected 1)
  exact (by decide : (1 : Nat) ≠ 0) hOne.2

private theorem omitSubjectSimplicity : OmitSubjectSimplicity :=
  ⟨manyNotSimple, fun _ _ => rfl, realizationComplete, localTokensNotSubsingleton⟩

/-- Arbitrary object carriers, repeated operations and populated omissions
separate object incidence from operation identity and subject simplicity. -/
theorem operationControls : Control.OperationControls := by
  refine ⟨simpleWhole, ⟨rfl, rfl⟩, manyNotSimple, arbitraryObjects, ?_,
    repeatedOperations, omitOperationIndividuation, omitIntrinsicRealization,
    omitSubjectSimplicity⟩
  intro n
  exact ⟨Set.mem_univ n, by omega⟩

end Operations

end TruthCore.Results.Causality.IntentionalUnity
