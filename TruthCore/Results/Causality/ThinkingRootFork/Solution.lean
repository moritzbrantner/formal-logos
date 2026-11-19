module

public import TruthCore.Causality.ThinkingRootFork
public import TruthCore.Results.Logic.CogitoSubject.Solution

/-! The two literal horns share *one* root witness. Only the positive horn
descends, and it descends through distinct thinkers rather than every ground.
The modal upgrade applies to that same endpoint. All metaphysical bridges
remain hypotheses; in particular no God-existence theorem is used. -/

@[expose] public section

namespace TruthCore.Results.Causality.ThinkingRootFork

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ThinkingRootFork
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

variable {W B Episode : Type}

/-- An actual concrete ground path starts at an actual concrete source. -/
theorem actualOfPositiveGroundPath (m : Profile W B) (w : W) {c x : B}
    (hPath : Relation.TransGen (ActualConcreteGround m w) c x) :
    ActualConcrete m w c := by
  obtain ⟨_, hFirst, _⟩ := Relation.TransGen.head'_iff.mp hPath
  exact ⟨hFirst.1, hFirst.2.1⟩

/-- Compose a strict ground path with the selected ancestor cone. -/
theorem ancestorOfPositiveGroundPath (m : Profile W B) (w : W) {c x : B}
    (hPath : Relation.TransGen (ActualConcreteGround m w) c x) :
    ∀ {selected}, GroundAncestor m w x selected → GroundAncestor m w c selected := by
  induction hPath with
  | single hEdge =>
    intro selected hAnc
    exact Relation.ReflTransGen.head hEdge hAnc
  | tail _ hEdge ih =>
    intro selected hAnc
    exact ih (Relation.ReflTransGen.head hEdge hAnc)

/-- The existing full actual-concrete-ground accessibility implies the new
restricted thinker-accessibility, by Mathlib's accessibility of TransGen.
The reverse direction is *not* claimed by this proof. -/
theorem thinkingAccessibleOfConcreteAcc (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (b : B)
    (hAcc : Acc (ActualConcreteGround m w) b) :
    Acc (ThinkerPredecessor m w Occurs Bears) b := by
  exact Subrelation.accessible (fun h => h.2.2) hAcc.transGen

/-- Existing Cogito grounding accessibility supplies the new accessibility
premise with the *same* profile, thought predicates, selected world and bearer. -/
theorem oldAccessibilitySuppliesThinkingAccessibility (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOld : ThinkerGroundingAccessible m Occurs Bears w) :
    ThinkingBearerPredecessorAccessible m w Occurs Bears := by
  intro b e he hb
  exact thinkingAccessibleOfConcreteAcc m w Occurs Bears b (hOld b e he hb)

/-- The older all-concrete-ancestor anti-brute premise implies the new
contingent-*thinker* restriction. The converse needs separate finite controls. -/
theorem oldGroundingSuppliesThinkingGrounding (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOld : ThinkerAncestryGrounded m Occurs Bears w) :
    ThinkingBearerConeContingentGrounded m w Occurs Bears := by
  intro b e he hb x hCone _ hCont
  exact hOld b e x he hb hCone.2 hCone.1.1 hCone.1.2 hCont

/-- The **literal negative** horn excludes every actual concrete ground of a
thinking cone member, but only under the stated no-fresh-thinker premise. -/
theorem noPIsActualRoot (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected x : B)
    (hCone : Cone m w selected x) (hThink : Thinks Occurs Bears x)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hNoP : ¬ P m w Occurs Bears x) : ActualRoot m w x := by
  refine ⟨hCone.1, ?_⟩
  intro y hy
  exact hNoP (hNoFresh x hCone hThink ⟨y, hy⟩)

/-- A *contingent* selected thinker cannot occupy the negative horn when both
local grounding premises hold. The literal P/¬P cases remain complementary,
but they need not each be compatible with additional case assumptions. -/
theorem contingentBearerHasP (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hGrounded : ConeContingentThinkersGrounded m w Occurs Bears selected)
    (hCont : ContingentAt m.ontic w selected) : P m w Occurs Bears selected := by
  have hCone : Cone m w selected selected :=
    ⟨hActual, Relation.ReflTransGen.refl⟩
  obtain ⟨y, hy⟩ := hGrounded selected hCone hThink hCont
  exact hNoFresh selected hCone hThink ⟨y, hy⟩

/-- `P` supplies a strictly earlier *thinking* ancestor and `¬P` terminates
at an actual thinking ground-root. `Acc` is only for the thinker relation:
nonthinking ancestors may form cycles. The same endpoint is retained along
the finite concrete ancestry chain. -/
theorem thinkingRootOfAccessible (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hAcc : Acc (ThinkerPredecessor m w Occurs Bears) selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hEM : ExcludedMiddle) :
    ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
      ActualRoot m w n := by
  have walk : ∀ x, Acc (ThinkerPredecessor m w Occurs Bears) x →
      Cone m w selected x → Thinks Occurs Bears x →
      ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
        ActualRoot m w n := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hCone hThinks
      rcases hEM (P m w Occurs Bears x) with hP | hNoP
      · obtain ⟨c, hc⟩ := hP
        exact ih c hc
          ⟨actualOfPositiveGroundPath m w hc.2.2,
            ancestorOfPositiveGroundPath m w hc.2.2 hCone.2⟩ hc.2.1
      · exact ⟨x, hThinks, hCone.2,
          noPIsActualRoot m w Occurs Bears selected x hCone hThinks hNoFresh hNoP⟩
  exact walk selected hAcc ⟨hActual, Relation.ReflTransGen.refl⟩ hThink

/-- The **same** terminal thinker is necessary if contingent thinking members
of this selected cone always have an actual concrete ground. Without that
anti-brute assumption the root could remain contingent. -/
theorem necessaryThinkingRootOfSelected (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hAcc : Acc (ThinkerPredecessor m w Occurs Bears) selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hGrounded : ConeContingentThinkersGrounded m w Occurs Bears selected)
    (hEM : ExcludedMiddle) :
    NecessaryThinkingRootOf m w Occurs Bears selected := by
  obtain ⟨n, hnThink, hnAnc, hnRoot⟩ :=
    thinkingRootOfAccessible m w Occurs Bears selected hActual hThink hAcc hNoFresh hEM
  have hnCont : ¬ ContingentAt m.ontic w n := by
    intro hCont
    obtain ⟨y, hy⟩ := hGrounded n ⟨hnRoot.1, hnAnc⟩ hnThink hCont
    exact hnRoot.2 y hy
  have hnNec : NecessaryAt m.ontic w n := by
    intro v hv
    rcases hEM (m.ontic.ExistsAt v n) with he | hne
    · exact he
    · exact (hnCont ⟨hnRoot.1.2, v, hv, hne⟩).elim
  exact ⟨n, hnThink, hnAnc, hnRoot, hnNec⟩

/-- Existing Cogito subjecthood and its separate actuality/concreteness
bridges supply the starting thinker. The ancestry premises are scoped to the
selected occurring-thought bearer, not to arbitrary beings in the carrier. -/
theorem necessaryThinkingRootOfThought (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkingBearerPredecessorAccessible m w Occurs Bears)
    (hNoFresh : ThinkingBearerConeNoFresh m w Occurs Bears)
    (hGrounded : ThinkingBearerConeContingentGrounded m w Occurs Bears)
    (hEM : ExcludedMiddle) :
    NecessaryThinkingRootOfThought m w Occurs Bears := by
  obtain ⟨b, e, he, hb⟩ :=
    TruthCore.Results.Logic.CogitoSubject.thinkingSubjectOfThought
      Occurs Bears hOccurs hBearer
  exact ⟨b, e, he, hb,
    necessaryThinkingRootOfSelected m w Occurs Bears b
      ⟨hConcrete b e he hb, hExists b e he hb⟩
      ⟨e, he, hb⟩ (hAcc b e he hb) (hNoFresh b e he hb)
      (hGrounded b e he hb) hEM⟩

/-- A selected thinker-root remains the *same witness* of the older complete
actual-cone result. This is a projection, not a second ancestry argument. -/
theorem selectedNecessaryRootOfThinkingRoot (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (h : NecessaryThinkingRootOf m w Occurs Bears selected) :
    NecessaryRootAncestor m w selected := by
  obtain ⟨n, _, hAnc, hRoot, hNec⟩ := h
  exact ⟨n, ⟨hRoot.1, hAnc⟩, hNec, hRoot.2⟩

/-- The new result strengthens, rather than silently replacing, the older
Cogito concrete-root statement: it retains its b/e/n and adds thinkerhood. -/
theorem existingConcreteRootOfThinkingRoot (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (h : NecessaryThinkingRootOfThought m w Occurs Bears) :
    NecessaryConcreteRootAncestorOfThinker m Occurs Bears w := by
  obtain ⟨b, e, he, hb, n, _, hAnc, hRoot, hNec⟩ := h
  exact ⟨b, e, n, he, hb, hAnc, hRoot.1.1, hRoot.1.2, hNec, hRoot.2⟩

end TruthCore.Results.Causality.ThinkingRootFork
