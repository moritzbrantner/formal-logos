module

public import TruthCore.Causality.EsseCausePriority

@[expose] public section

namespace TruthCore.Results.Causality.EsseCausePriority
open TruthCore.Causality.EsseCausePriority
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority
  ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.CreatureSenses (CausedEsseIsHad)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Causality.ComponentFirstness
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The composition of #1604: a distinct cause `c` of the esse of an actual
concretum `x` is, by the esse-cause bridge, a concrete ground of `x` existing at
`w`; both are then actual concreta related by grounding, so by the
grounding-to-priority bridge `c` is simply prior to `x`. No dependence or
separability premise. -/
theorem actualEsseCausePriority {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) (PriorSimply : B → B → Prop)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hPrior : ActualGroundingIsSimplePriority m w PriorSimply) :
    ActualEsseCausePriority m w CausesIn esse PriorSimply := by
  intro c x hne hx hCause
  obtain ⟨hConc, hExists, hGround⟩ := hEsse c x hne hx hCause
  exact hPrior c x ⟨hConc, hExists⟩ hx hGround

/-- The actuality antecedent discharged: an effect of a cause of esse has esse
(`CausedEsseIsHad`), hence exists at `w` and is concrete in the profile, so the
scoped priority applies to it. Reuses `actualEsseCausePriority`'s conclusion as
a premise. -/
theorem distinctEsseCausePriority {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop)
    (hScoped : ActualEsseCausePriority m w CausesIn esse PriorSimply)
    (hHad : CausedEsseIsHad CausesIn InAct esse)
    (hExist : ActOfEsseSufficesForExistenceAt m.ontic InAct esse w)
    (hConc : EsseInReIsConcrete m InAct esse) :
    DistinctEsseCausePriority CausesIn esse PriorSimply := by
  intro c x hne hCause
  have hAct : InAct x esse := hHad c x hCause
  exact hScoped c x hne ⟨hConc x hAct, hExist x hAct⟩ hCause

/-- The q.3 a.1 conclusion from composition, with the cause-to-efficient bridge
and efficient-cause priority replaced by distinct-esse-cause priority: a first
being in act in some respect and in potency in another would be composite, so it
would have a distinct cause of its esse, which is prior to it, against
firstness. -/
theorem firstBeingNoPotencyOfEssePriority {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply := by
  intro f hFirst r hPot
  obtain ⟨s, hAct⟩ := hInAct f hFirst
  obtain ⟨c, hDistinct, hCauses⟩ := hCause f (hComposite f r s hAct hPot)
  exact hDistinct (hFirst c (hPrior c f hDistinct hCauses))

/-- The first-being version of act priority from the same four premises, by
`firstBeingNoPotencyOfEssePriority`: it holds vacuously. -/
theorem weakOfEssePriority {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  intro f hFirst r hPot
  exact absurd hPot (firstBeingNoPotencyOfEssePriority InAct InPotency PriorSimply Composite
    CausesIn esse hInAct hComposite hCause hPrior f hFirst r)

/-- "No component is the first being" with efficient-cause priority replaced by
distinct-esse-cause priority. A component supposed first is in potency in some
respect, against act priority at a first being and non-overlap, or participated,
so it has a distinct cause of its esse, which is prior to it, against
firstness. The participation premise is the cause-of-being reading
`Round2Grounding.ParticipatedEsseHasDistinctCause` (the same body as
`ComponentFirstness.ParticipatedHasOtherCause`), so one cause-of-perfection
relation at esse runs through the whole argument. -/
theorem noComponentFirstOfEssePriority {B R : Type} (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hWeak : FirstBeingActPriority InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedEsseHasDistinctCause Participated CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  intro p x hComponent hFirst
  rcases hKinds p x hComponent with ⟨r, hPotency⟩ | hPart
  · obtain ⟨y, hAct, hPriorY⟩ := hWeak p hFirst r hPotency
    have hEq : y = p := hFirst y hPriorY
    subst hEq
    exact hNotBoth y r ⟨hAct, hPotency⟩
  · obtain ⟨c, hDistinct, hCause⟩ := hParticipated p hPart
    exact hDistinct (hFirst c (hPrior c p hDistinct hCause))

/-! ## Controls -/

/-- The batch controls. -/
theorem controls : TruthCore.Causality.EsseCausePriority.Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Witness
    refine ⟨?_, ?_, ⟨trivial, trivial⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · intro c x _ _ h
      obtain ⟨hc, hx, _⟩ := h
      exact ⟨trivial, trivial, rfl, hc, hx⟩
    · intro a b _ _ h
      exact ⟨h.2.1, h.2.2⟩
  · -- OmitEsseGround
    refine ⟨fun _ _ _ _ h => h.elim, fun h => ?_⟩
    exact h true false Bool.noConfusion ⟨trivial, trivial⟩ ⟨rfl, rfl, rfl⟩
  · -- OmitGroundingPriority
    refine ⟨?_, fun h => ?_⟩
    · intro c x _ _ h
      obtain ⟨hc, hx, _⟩ := h
      exact ⟨trivial, trivial, rfl, hc, hx⟩
    · exact h true false Bool.noConfusion ⟨trivial, trivial⟩ ⟨rfl, rfl, rfl⟩
  · -- ScopeWitness
    refine ⟨fun _ _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial, ?_, ?_⟩
    · intro c x _ _ h
      obtain ⟨hc, hx, _⟩ := h
      exact ⟨trivial, trivial, rfl, hc, hx⟩
    · intro a b _ _ h
      exact ⟨h.2.1, h.2.2⟩
  · -- OmitCausedEsseIsHad
    refine ⟨fun _ _ _ hx _ => hx.1.elim, fun _ h => h.elim, fun _ h => h.elim, fun h => ?_⟩
    exact h true false Bool.noConfusion ⟨rfl, rfl, rfl⟩
  · -- NotEfficientPriority
    refine ⟨fun c x hne h => hne (h.1.trans h.2.1.symm), fun h => ?_⟩
    exact h true true true ⟨rfl, rfl, rfl⟩


/-! ## C3/¬C3: full priority-bundle interpretation tests (#1616, #1801) -/

namespace InertialNecessaryOrigin

open TruthCore.Causality.EsseCausePriority.InertialNecessaryOrigin
open TruthCore.Causality.ConcurrentCessation.C3ActualWorld
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryConcreteRouteBridge (NecessaryActualRootAt)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory

private theorem noConcurrentGiving :
    ¬ ConcurrentlyActualized history C3ActualWorld.originGiving
      ConcurrentActualization.Control.falseReceived := by
  intro h
  obtain ⟨g, hg⟩ := h true false 2 () (by rfl) (by simp [history])
  simp [C3ActualWorld.originGiving] at hg

/-- The nine non-grounding clauses of the ten-source-premise #1614 bundle
hold for every selected grounding/priority interpretation satisfying the
explicit two elementary interpretation contracts. No new support option. -/
private theorem sourcePremisesOfGrounding (m : Profile Bool Bool)
    (priority : Bool → Bool → Prop)
    (hg : ActualGroundingIsSimplePriority m true priority)
    (hOntic : m.ontic = history.ontic)
    (hConcrete : ∀ x, m.concrete x) :
    SourcePremises m (frame priority) := by
  unfold SourcePremises
  refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c x _
    rfl
  · intro x _
    rw [hOntic]
    simp [history]
  · intro x _
    exact hConcrete x
  · intro f _
    exact ⟨true, rfl⟩
  · intro x r s _ hp
    exact hp.1
  · intro x hc
    have hx : x = false := hc
    subst x
    refine ⟨true, by decide, ?_⟩
    simp [frame, causes, C3ActualWorld.originFrame,
      C3ActualWorld.frame, SustainingCausation.Control.trueCausesFalse]
  · intro p x hp
    exact Or.inr hp.1
  · intro x r ⟨ha, hp⟩
    have hTrue : r = true := ha
    have hFalse : r = false := hp.2
    cases r <;> simp_all
  · intro x hp
    have hx : x = false := hp
    subst x
    refine ⟨true, by decide, ?_⟩
    simp [frame, causes, C3ActualWorld.originFrame,
      C3ActualWorld.frame, SustainingCausation.Control.trueCausesFalse]

/-- An underived actual necessary origin is compatible with an actually
contingent received-esse effect that persists without present being-giving.
The chosen actual-ground edge is read as historical ancestry, not as
a productive ground. -/
theorem necessaryOriginWithoutConservation :
    NecessaryOriginWithoutConservation := by
  unfold NecessaryOriginWithoutConservation
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, noConcurrentGiving, ?_⟩
  · intro v x
    cases v <;> cases x <;> simp [history, C3ActualWorld.history]
  · intro v x n hp
    change x = true ∨ (v = true ∧ x = false ∧ 1 ≤ n) at hp
    change x = true ∨ (v = true ∧ x = false ∧ 1 ≤ n + 1)
    rcases hp with hSource | ⟨hv, hx, hn⟩
    · exact Or.inl hSource
    · exact Or.inr ⟨hv, hx, by omega⟩
  · refine ⟨true, ⟨⟨by trivial, by simp [ancestral, history]⟩, ?_⟩, ?_⟩
    · intro y hy
      simp [ActualConcreteGround, ancestral,
        C3ActualWorld.withGround] at hy
    · intro v _
      simp [ancestral, history]
  · intro x _ _ hCont
    cases x with
    | false =>
        refine ⟨true, by trivial, by simp [ancestral, history], ?_⟩
        simp [ancestral, C3ActualWorld.withGround]
    | true =>
        rcases hCont with ⟨_, v, _, hAbs⟩
        simp [ancestral, history] at hAbs
  · refine ⟨by simp [history], ⟨false, by trivial, by simp [history]⟩⟩
  · refine ⟨1, ⟨by simp [history], ?_⟩,
      by simp [C3ActualWorld.originGiving]⟩
    intro s hs hp
    simp [history] at hp
    omega
  · intro v c x t hg
    rcases hg with ⟨_, hc, _, _⟩
    change c = true ∨ (v = true ∧ c = false ∧ 1 ≤ t)
    exact Or.inl hc
  · intro hs
    have hh := hs true true false (by decide)
      (by simp [ancestralFrame, frame, causes,
        C3ActualWorld.originFrame, C3ActualWorld.frame,
        SustainingCausation.Control.trueCausesFalse])
      ⟨1, by simp [history]⟩
    have h := hh.2 2 (by simp [history])
    simp [C3ActualWorld.originGiving] at h

/-- Complete #1614 source-input omission for `cb1cdea9`: all remaining
ten source premises are jointly true; the intermediate priority and
downstream first-being/component conclusions genuinely fail. This test does
not independently establish the truth of those philosophical premises. -/
theorem fullSourceOmission : FullSourceOmission := by
  unfold FullSourceOmission
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply sourcePremisesOfGrounding withoutGround Control.noPrior
    · intro a b _ _ hg
      exact hg.elim
    · rfl
    · intro x
      trivial
  · intro hb
    have h := hb true false (by decide)
      (by simp [ActualConcrete, withoutGround, ancestral, history])
      (by simp [strictFrame, frame, causes, C3ActualWorld.originFrame,
        C3ActualWorld.frame, SustainingCausation.Control.trueCausesFalse])
    exact h.2.2
  · intro hp
    exact hp true false (by decide)
      (by simp [ActualConcrete, withoutGround, ancestral, history])
      (by simp [strictFrame, frame, causes, C3ActualWorld.originFrame,
        C3ActualWorld.frame, SustainingCausation.Control.trueCausesFalse])
  · intro hp
    exact hp true false (by decide)
      (by simp [strictFrame, frame, causes, C3ActualWorld.originFrame,
        C3ActualWorld.frame, SustainingCausation.Control.trueCausesFalse])
  · intro hp
    obtain ⟨y, _, hPrior⟩ :=
      hp false (by intro y hy; exact hy.elim) false
        (by simp [potency, ActPriorityAtFirst.Control.stonePotency])
    exact hPrior.elim
  · intro hp
    have hh := hp false (by intro y hy; exact hy.elim) false
    exact hh (by simp [potency, ActPriorityAtFirst.Control.stonePotency])
  · intro hp
    have hh := hp false true
      (by simp [component, ComponentFirstness.Control.comp])
    exact hh (by intro y hy; exact hy.elim)

/-- A historical-ancestry reading of the ground/priority relation makes
the full positive #1614 source bundle and the priority results compatible
with absent concurrent giving. The explicit interpretation, not the
unregistered helper, bears the philosophical burden. -/
theorem ancestorRouteWithoutConservation :
    AncestorRouteWithoutConservation := by
  unfold AncestorRouteWithoutConservation
  have hGround : ActualGroundingIsSimplePriority
      ancestral true ancestralFrame.PriorSimply := by
    intro a b _ _ hg
    simpa [ancestralFrame, frame, Control.prior, ancestral,
      C3ActualWorld.withGround] using hg
  have hSources : SourcePremises ancestral ancestralFrame := by
    exact sourcePremisesOfGrounding ancestral Control.prior
      hGround rfl (by intro x; trivial)
  have hBridge : EsseCauseIsActualConcreteGround
      ancestral true ancestralFrame.CausesIn ancestralFrame.esse := by
    intro c x _ _ hc
    rcases hc with ⟨_, hh⟩
    rcases hh with ⟨rfl, rfl⟩
    simp [ActualConcreteGround, ancestral, history,
      C3ActualWorld.withGround]
  have hActual : ActualEsseCausePriority ancestral true
      ancestralFrame.CausesIn ancestralFrame.esse
      ancestralFrame.PriorSimply :=
    actualEsseCausePriority ancestral true ancestralFrame.CausesIn
      ancestralFrame.esse ancestralFrame.PriorSimply hBridge hGround
  have hDistinct : DistinctEsseCausePriority
      ancestralFrame.CausesIn ancestralFrame.esse
      ancestralFrame.PriorSimply :=
    distinctEsseCausePriority ancestral true act ancestralFrame.CausesIn
      ancestralFrame.esse ancestralFrame.PriorSimply hActual
      hSources.2.1 hSources.2.2.1 hSources.2.2.2.1
  obtain ⟨hG, hHad, hExist, hConc, hSome, hComposite, hUnit,
    hKinds, hNotBoth, hParticipated⟩ := hSources
  have hFirst : FirstBeingIsInNoWayInPotencyReading
      potency ancestralFrame.PriorSimply :=
    firstBeingNoPotencyOfEssePriority act potency ancestralFrame.PriorSimply
      composite ancestralFrame.CausesIn ancestralFrame.esse
      hSome hComposite hUnit hDistinct
  have hWeak : FirstBeingActPriority act potency ancestralFrame.PriorSimply :=
    weakOfEssePriority act potency ancestralFrame.PriorSimply
      composite ancestralFrame.CausesIn ancestralFrame.esse
      hSome hComposite hUnit hDistinct
  have hNoComponent : NoComponentIsFirstBeingReading
      component ancestralFrame.PriorSimply :=
    noComponentFirstOfEssePriority component ancestralFrame.PriorSimply
      act potency participated ancestralFrame.CausesIn ancestralFrame.esse
      hKinds hWeak hNotBoth hParticipated hDistinct
  exact ⟨⟨hG, hHad, hExist, hConc, hSome, hComposite, hUnit,
    hKinds, hNotBoth, hParticipated⟩, hBridge, hActual, hDistinct,
    hFirst, hNoComponent, noConcurrentGiving⟩

end InertialNecessaryOrigin

end TruthCore.Results.Causality.EsseCausePriority
