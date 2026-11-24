module

public import TruthCore.Causality.ThinkingRootFork
public import TruthCore.Results.Logic.CogitoSubject.Solution
public import TruthCore.Latin.Aquinas.DeEnte.RootInterface
public import TruthCore.Causality.UnderivedRootRoute
public import TruthCore.Results.Causality.DirectEsseRootGodExistence.Solution
public import TruthCore.Logic.RootDescent

/-! The two literal horns share *one* root witness. Only the positive horn
descends, and it descends through distinct thinkers rather than every ground.
The modal upgrade applies to that same endpoint. All metaphysical bridges
remain hypotheses. The registered theorem `necessaryThinkingRootOfThought`
uses no God-existence theorem; only the ordinary helper
`directEsseGodOfNecessaryThinkingRoot` below invokes
`DirectEsseRootGodExistence.godOfRoot`, under that consumer's explicit
premises, and it is not a registered result. -/

@[expose] public section

namespace TruthCore.Results.Causality.ThinkingRootFork

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ThinkingRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge (SimplyPriorIsActualConcreteGround EsseCauseIsActualConcreteGround)
open TruthCore.Causality.NecessarilyUnderived (PresentEsseSupport)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.RootDescent (acc_exists_unmarked)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

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

/-- Conversely, any actual G-root is P-free for the **same** mediate G+ sense:
a nonempty path into it would end with a forbidden incoming G edge. This
requires neither thinkerhood nor no-fresh-thinker. -/
theorem noPOfActualRoot (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (x : B)
    (hRoot : ActualRoot m w x) : ¬ P m w Occurs Bears x := by
  intro hp
  obtain ⟨c, hc⟩ := hp
  obtain ⟨y, _, hy⟩ := Relation.TransGen.tail'_iff.mp hc.2.2
  exact hRoot.2 y hy

/-- One *direct* existing thinking supporter in the profile's same `grounds`
relation is a mediate thinking predecessor. The existing Cogito concreteness
bridge suffices: `PresentEsseSupport` already supplies the source's actuality,
so the more general `ActualSupportersConcrete` is unnecessary here. The
converse can fail when a nonthinking intermediate ground lies on the path,
unless another direct thinking supporter coexists; no checked model of that
failure is supplied here. -/
theorem directThinkingSupportImpliesP (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (x : B)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hDirect : ∃ c, c ≠ x ∧ Thinks Occurs Bears c ∧
      PresentEsseSupport m.ontic m.grounds w c x) :
    P m w Occurs Bears x := by
  obtain ⟨c, hcNe, ⟨e, he, hb⟩, hcSupport⟩ := hDirect
  exact ⟨c, hcNe, ⟨e, he, hb⟩,
    Relation.TransGen.single ⟨hConcrete c e he hb, hcSupport.1, hcSupport.2⟩⟩

/-- Exact local root alignment: for an actual thinking member of the selected
cone, `¬P` is equivalent to actual G-rootness *if* the no-fresh-thinker bridge
holds. Outside this scope, only `ActualRoot → ¬P` is unconditional. -/
theorem thinkingConeRootIffNoP (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected x : B)
    (hCone : Cone m w selected x) (hThink : Thinks Occurs Bears x)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected) :
    ActualRoot m w x ↔ ¬ P m w Occurs Bears x := by
  constructor
  · exact noPOfActualRoot m w Occurs Bears x
  · exact noPIsActualRoot m w Occurs Bears selected x hCone hThink hNoFresh

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
  obtain ⟨n, ⟨hCone, hThinks⟩, hNoP⟩ := acc_exists_unmarked
    (P := fun x => Cone m w selected x ∧ Thinks Occurs Bears x) (Mark := P m w Occurs Bears)
    (fun _ _ => hEM _)
    (fun _ ⟨hCone, _⟩ ⟨c, hc⟩ => ⟨c, hc, ⟨actualOfPositiveGroundPath m w hc.2.2,
      ancestorOfPositiveGroundPath m w hc.2.2 hCone.2⟩, hc.2.1⟩)
    hAcc ⟨⟨hActual, Relation.ReflTransGen.refl⟩, hThink⟩
  exact ⟨n, hThinks, hCone.2,
    noPIsActualRoot m w Occurs Bears selected n hCone hThinks hNoFresh hNoP⟩

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

/-- Spell out the endpoint requested by the literal fork: one and the same
actual necessary *thinking* ancestor n satisfies ¬P(n). The existing root
predicate already contains the stronger selected-relation absence fact. -/
theorem necessaryThinkingRootHasNoP (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (h : NecessaryThinkingRootOf m w Occurs Bears selected) :
    ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
      ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧ ¬ P m w Occurs Bears n := by
  obtain ⟨n, hThink, hAnc, hRoot, hNec⟩ := h
  exact ⟨n, hThink, hAnc, hRoot, hNec, noPOfActualRoot m w Occurs Bears n hRoot⟩

/-- Existing underived-root transport upgrades the *same thinker* from
selected-G rootness to absence of existing supporters in `m.grounds` at every
world. This is still not an assertion about every conceivable dependence
relation; the present-support and concreteness bridges are explicit. -/
theorem underivedThinkingRootOfSelected (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hThinking : NecessaryThinkingRootOf m w Occurs Bears selected)
    (hPresent : TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent m w)
    (hConcrete : TruthCore.Causality.UnderivedRootRoute.ActualSupportersConcrete m w) :
    ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
      TruthCore.Causality.UnderivedRootRoute.UnderivedRootAt m w n := by
  obtain ⟨n, hnThink, hnAnc, hnRoot, hnNec⟩ := hThinking
  exact ⟨n, hnThink, hnAnc,
    TruthCore.Causality.UnderivedRootRoute.underivedOfNecessaryRoot
      m w hPresent hConcrete n hnRoot hnNec⟩

/-- Alignment to the already defined De ente root interface requires
*at-most-one actual root of this very same grounding profile and world*.
It transfers thinkerhood and de-re necessity to the De ente source; neither
the De ente interface nor the thinker fork proves root uniqueness on its own. -/
theorem deEnteFirstSourceThinksOfRootUniqueness {P R : Type}
    (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hThinking : NecessaryThinkingRootOf m w Occurs Bears selected)
    (hSource : TruthCore.Latin.Aquinas.DeEnte.DeEnteFirstSourceIsActualRootAt m w p)
    (hAtMost : TruthCore.Latin.Aquinas.DeEnte.AtMostOneActualRootAt m w) :
    ∃ n, Thinks Occurs Bears n ∧ ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
      p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
      (∀ c, ¬ TruthCore.Latin.Aquinas.DeEnte.ActualEsseCause p c n) := by
  obtain ⟨n, hnThink, _, hnRoot, hnNec⟩ := hThinking
  obtain ⟨s, hsRoot, hsAct, hsId, hsUncaused, _⟩ := hSource
  have hEq : n = s := hAtMost n s hnRoot hsRoot
  subst s
  exact ⟨n, hnThink, hnRoot, hnNec, hsAct, hsId, hsUncaused⟩

/-- The *same* necessary thinking G-root can feed the existing direct-esse
`godOfRoot` consumer. The extra simply-prior bridge converts G-rootness to
first-being status; the causal/perfection and nominal God bridges stay explicit.
No whole-roster foundation or uniqueness hypothesis is imported here, and
none of these downstream premises is proved by the P/¬P fork itself. -/
theorem directEsseGodOfNecessaryThinkingRoot {Respect : Type}
    (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hThinking : NecessaryThinkingRootOf m w Occurs Bears selected)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
      ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
      IsFirstBeing PriorSimply n ∧ IsGod n := by
  obtain ⟨n, hnThink, hnAnc, hnRoot, hnNec⟩ := hThinking
  have hnFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact False.elim (hnRoot.2 y (hPrior y n hNe hy))
  have hnGod :=
    TruthCore.Results.Causality.DirectEsseRootGodExistence.godOfRoot
      m w InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod
      n hnRoot hnFirst hEM hGenus hExisting hEsse hApproach
      hBeing hTransfer hNoComponent hFull
  exact ⟨n, hnThink, hnAnc, hnRoot, hnNec, hnFirst, hnGod⟩

/-- The new result strengthens, rather than silently replacing, the older
Cogito concrete-root statement: it retains its b/e/n and adds thinkerhood. -/
theorem existingConcreteRootOfThinkingRoot (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (h : NecessaryThinkingRootOfThought m w Occurs Bears) :
    NecessaryConcreteRootAncestorOfThinker m Occurs Bears w := by
  obtain ⟨b, e, he, hb, n, _, hAnc, hRoot, hNec⟩ := h
  exact ⟨b, e, n, he, hb, hAnc, hRoot.1.1, hRoot.1.2, hNec, hRoot.2⟩

end TruthCore.Results.Causality.ThinkingRootFork
