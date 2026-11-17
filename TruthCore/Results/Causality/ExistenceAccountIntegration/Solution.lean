module
public import TruthCore.Causality.ExistenceAccountIntegration
@[expose] public section
namespace TruthCore.Results.Causality.ExistenceAccountIntegration
open TruthCore.Causality.ExistenceAccountIntegration
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived

/-- Preserve the actual exemplar, rather than exchange ∀∃ with ∃∀. -/
theorem necessaryConcrete {W B : Type} (m : Profile W B) (p : RealityProfile B) (w : W)
    (hActual : ActualConcreteProfile m p w)
    (hPopulation : NecessaryProfilePopulation m p w)
    (hUnique : MostRealUnique p) : NecessaryConcreteAt m w := by
  obtain ⟨n, hc, he, hp⟩ := hActual
  refine ⟨n, hc, he, ?_⟩
  intro v hv
  obtain ⟨y, hy, hyp⟩ := hPopulation v hv
  have hn : n = y := hUnique n y hp hyp
  exact hn.symm ▸ hy

/-- The disputed necessity-to-profile inclusion is indispensable to this
particular same-witness support argument. No excluded middle is needed:
a putative supporter becomes the target itself and contradicts well-foundedness. -/
theorem sameWitnessUnderived {W B : Type} (m : Profile W B) (p : RealityProfile B)
    (support : W → B → B → Prop) (w : W)
    (hActual : ActualConcreteProfile m p w)
    (hPopulation : NecessaryProfilePopulation m p w)
    (hUnique : MostRealUnique p)
    (hIdentify : NecessaryIsMostReal m.ontic p w)
    (hWF : WellFoundedPresentEsseSupport m.ontic support w)
    (hLift : NecessaryPredecessorLifting m.ontic support w) :
    UnderivedConcreteProfile m p support w := by
  obtain ⟨n, hc, he, hp⟩ := hActual
  have hn : NecessaryAt m.ontic w n := by
    intro v hv
    obtain ⟨y, hy, hyp⟩ := hPopulation v hv
    exact (hUnique n y hp hyp).symm ▸ hy
  refine ⟨n, hc, he, hp, hn, ?_⟩
  intro v source hSource hEdge
  obtain ⟨hSourceNecessary, hActualEdge⟩ := hLift v source n hn hSource hEdge
  have hSame : source = n := hUnique source n (hIdentify source hSourceNecessary) hp
  subst source
  have noSelf : ∀ x, Acc (PresentEsseSupport m.ontic support w) x →
      ¬ PresentEsseSupport m.ontic support w x x := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hxx
      exact ih x hxx hxx
  exact noSelf n (hWF.apply n) hActualEdge

/-- Explicit specialization of the support parameter; no relation dictionary
is inferred from a name or from reference-graph connectivity. -/
theorem groundingConsumer {W B : Type} (m : Profile W B) (p : RealityProfile B) (w : W)
    (h : UnderivedConcreteProfile m p m.grounds w) :
    TruthCore.Causality.NecessaryConcreteUnderived.NecessaryConcreteUnderivedAt m w := by
  obtain ⟨n, hc, he, _, hn, hNo⟩ := h
  exact ⟨n, hc, he, hn, fun v a _ ha => hNo v a ha⟩

theorem populationControls : PopulationControls := by
  unfold PopulationControls ActualConcreteProfile NecessaryProfilePopulation
    MostRealUnique MostReal NecessaryConcreteAt NecessaryAt fixture reality
    TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.DeDicto
    TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.alternatingFrame
    TruthCore.Isabelle.AFP.GoedelGod.Box
  simp [Bool.forall_bool]

theorem supportControls : SupportControls := by
  have hEmpty : WellFoundedPresentEsseSupport
      (fixture (fun _ x => x = false)).ontic (fun _ _ _ => False) false :=
    ⟨fun b => Acc.intro b (fun _ h => h.2.elim)⟩
  have hOther : WellFoundedPresentEsseSupport
      (fixture (fun _ _ => True)).ontic otherSupport false := by
    constructor
    intro b
    cases b with
    | false =>
      constructor
      intro a ha
      have hA : a = true := ha.2.1
      subst a
      constructor
      intro c hc
      exact Bool.noConfusion hc.2.2
    | true =>
      constructor
      intro a ha
      exact Bool.noConfusion ha.2.2
  unfold SupportControls
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, hEmpty, ?_, ?_⟩ <;>
      simp [ActualConcreteProfile, NecessaryProfilePopulation, MostRealUnique,
        NecessaryIsMostReal, NecessaryPredecessorLifting, PresentEsseSupport,
        UnderivedConcreteProfile, NoExistingSupportAt, NecessaryAt, MostReal,
        fixture, reality, TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.DeDicto,
        TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.alternatingFrame,
        TruthCore.Isabelle.AFP.GoedelGod.Box]
  · refine ⟨?_, ?_, ?_, ?_, hOther, ?_, ?_, ?_⟩ <;>
      simp [ActualConcreteProfile, NecessaryProfilePopulation, MostRealUnique,
        NecessaryIsMostReal, NecessaryPredecessorLifting, PresentEsseSupport,
        UnderivedConcreteProfile, NoExistingSupportAt, NecessarilyUnderived,
        NecessaryAt, MostReal, fixture, reality, otherSupport,
        TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.DeDicto,
        TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.alternatingFrame,
        TruthCore.Isabelle.AFP.GoedelGod.Box, Bool.forall_bool]

end TruthCore.Results.Causality.ExistenceAccountIntegration
