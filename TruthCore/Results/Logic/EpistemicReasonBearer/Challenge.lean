import TruthCore.Logic.EpistemicReasonBearer

namespace TruthCore.Results.Logic.EpistemicReasonBearer

open TruthCore.Logic.EpistemicReasonBearer TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.GlobalThesisBoundaries TruthCore.Logic.EpistemicUnderminers
open TruthCore.German.Kant.CosmologicalInference TruthCore.Causality.ExistenceActuality
open TruthCore.Ontology.ConcreteAbstract TruthCore.Logic.CogitoConcrete

theorem reasonsFromWarrant (f : ReliabilityFrame) (Reason : f.Agent → f.Content → Prop)
    (hBelief : SomeJustifiedBelief f.accepts f.warranted)
    (hNeeds : AcceptedWarrantNeedsBasis f) (hCounts : SurvivingBasisGivesReason f Reason) :
    ThereAreEpistemicReasons Reason := by
  sorry

/-- If a specified basis is undercut for this subject, a warranted acceptance
under the necessity condition has a distinct surviving basis for that content. -/
theorem otherBasis (f : ReliabilityFrame) (a : f.Agent) (p : f.Content) (bad : f.Basis)
    (ha : f.accepts a p) (hw : f.warranted a p) (hNeeds : AcceptedWarrantNeedsBasis f)
    (hBad : f.undercuts a bad) :
    ∃ b, b ≠ bad ∧ f.supports a b p ∧ ¬ f.undercuts a b := by
  sorry

theorem populationFromReasons {A P W B R : Type} (Reason : A → P → Prop)
    (rep : A → B) (m : Ontic W B) (InAct : B → R → Prop) (esse : R) (w : W)
    (hReasons : ThereAreEpistemicReasons Reason)
    (hPresent : ReasonBearerPresentAt Reason rep m w) (hEsse : ExistingInActAt m InAct esse w) :
    InhabitedConcreteAt m (HasEsseInRe InAct esse) w := by
  sorry

theorem warrantControls : WarrantControls := by
  sorry

theorem standpointControl : StandpointControl := by
  sorry

end TruthCore.Results.Logic.EpistemicReasonBearer
