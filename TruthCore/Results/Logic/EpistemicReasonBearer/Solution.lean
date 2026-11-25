module

public import TruthCore.Logic.EpistemicReasonBearer

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonBearer

open TruthCore.Logic.EpistemicReasonBearer TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.GlobalThesisBoundaries TruthCore.Logic.EpistemicUnderminers
open TruthCore.German.Kant.CosmologicalInference TruthCore.Causality.ExistenceActuality
open TruthCore.Ontology.ConcreteAbstract TruthCore.Logic.CogitoConcrete

theorem reasonsFromWarrant (f : ReliabilityFrame) (Reason : f.Agent → f.Content → Prop)
    (hBelief : SomeJustifiedBelief f.accepts f.warranted)
    (hNeeds : AcceptedWarrantNeedsBasis f) (hCounts : SurvivingBasisGivesReason f Reason) :
    ThereAreEpistemicReasons Reason := by
  obtain ⟨a, p, ha, hw⟩ := hBelief
  obtain ⟨b, hs, hu⟩ := hNeeds a p ha hw
  exact ⟨a, p, hCounts a b p hs hu⟩

/-- If a specified basis is undercut for this subject, a warranted acceptance
under the necessity condition has a distinct surviving basis for that content. -/
theorem otherBasis (f : ReliabilityFrame) (a : f.Agent) (p : f.Content) (bad : f.Basis)
    (ha : f.accepts a p) (hw : f.warranted a p) (hNeeds : AcceptedWarrantNeedsBasis f)
    (hBad : f.undercuts a bad) :
    ∃ b, b ≠ bad ∧ f.supports a b p ∧ ¬ f.undercuts a b := by
  obtain ⟨b, hs, hu⟩ := hNeeds a p ha hw
  exact ⟨b, fun e => hu (e ▸ hBad), hs, hu⟩

theorem populationFromReasons {A P W B R : Type} (Reason : A → P → Prop)
    (rep : A → B) (m : Ontic W B) (InAct : B → R → Prop) (esse : R) (w : W)
    (hReasons : ThereAreEpistemicReasons Reason)
    (hPresent : ReasonBearerPresentAt Reason rep m w) (hEsse : ExistingInActAt m InAct esse w) :
    InhabitedConcreteAt m (HasEsseInRe InAct esse) w := by
  obtain ⟨a, p, ha⟩ := hReasons
  have hp := hPresent a p ha
  exact ⟨rep a, hEsse (rep a) hp, hp⟩

theorem warrantControls : WarrantControls := by
  unfold WarrantControls
  constructor
  · exact ⟨fun ⟨_, _, h, _⟩ => h,
      ⟨(), true, false, Or.inr ⟨rfl, Or.inr rfl⟩, fun h => Bool.false_ne_true h.1⟩⟩
  constructor
  · refine ⟨⟨(), true, rfl, Or.inr (Or.inr rfl)⟩, ?_, fun _ _ h => h⟩
    intro a p _ _
    exact ⟨false, Or.inr ⟨rfl, Or.inr rfl⟩, fun h => Bool.false_ne_true h.1⟩
  · refine ⟨⟨(), true, rfl, Or.inr (Or.inr rfl)⟩, fun _ _ _ h _ => h, ?_⟩
    intro h
    obtain ⟨_, hs, _⟩ := h () true rfl (Or.inr (Or.inr rfl))
    exact hs

theorem standpointControl : StandpointControl := by
  exact ⟨⟨(), (), trivial⟩, fun _ _ _ => rfl, fun _ _ => trivial,
    fun ⟨_, _, h⟩ => Bool.false_ne_true h⟩

end TruthCore.Results.Logic.EpistemicReasonBearer
