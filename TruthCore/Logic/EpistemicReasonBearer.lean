module

public import TruthCore.Logic.EpistemicUnderminers
public import TruthCore.Logic.GlobalThesisBoundaries
public import TruthCore.Causality.ExistenceActuality
public import TruthCore.Ontology.ConcreteAbstract
public import TruthCore.Logic.CogitoConcrete

@[expose] public section

namespace TruthCore.Logic.EpistemicReasonBearer

open GlobalThesisBoundaries EpistemicUnderminers EpistemicReasons
open TruthCore.German.Kant.CosmologicalInference

/-- Apply the existing local necessity-of-support condition to the contents
actually accepted by each subject. Externalist warrant may reject this input. -/
def AcceptedWarrantNeedsBasis (f : ReliabilityFrame) : Prop :=
  ∀ a p, f.accepts a p → WarrantNeedsUndefeatedSupport f a p

/-- A surviving available supporting basis counts pro tanto for its subject
and content in the selected thin relation. No duty of assent is required. -/
def SurvivingBasisGivesReason (f : ReliabilityFrame) (Reason : f.Agent → f.Content → Prop) : Prop :=
  ∀ a b p, f.supports a b p → ¬ f.undercuts a b → Reason a p

/-- Selected-world application. The representation of a subject to whom a
reason is actually available exists there. A hypothetical subject's evidence
profile by itself does not satisfy this requirement. -/
def ReasonBearerPresentAt {A P W B : Type} (Reason : A → P → Prop)
    (rep : A → B) (m : Ontic W B) (w : W) : Prop :=
  ∀ a p, Reason a p → m.ExistsAt w (rep a)

/-- Use the existing independent-support control. Withhold all assent while
keeping the surviving bases, or retain warrant and change its interpretation
in the thin attribution. In a third profile warrant lacks a surviving basis. -/
def WarrantControls : Prop :=
    let f := reliabilityControl true true true
    let silent := { f with accepts := fun _ _ => False }
    (¬ SomeJustifiedBelief silent.accepts silent.warranted ∧
      ThereAreEpistemicReasons (UndefeatedSupport silent)) ∧
    (SomeJustifiedBelief f.accepts f.warranted ∧ AcceptedWarrantNeedsBasis f ∧
      EpistemicNihilism (fun (_ : f.Agent) (_ : f.Content) => False)) ∧
    (let ext := { f with supports := fun _ _ _ => False }
     SomeJustifiedBelief ext.accepts ext.warranted ∧
       SurvivingBasisGivesReason ext (fun _ _ => False) ∧ ¬ AcceptedWarrantNeedsBasis ext)

open TruthCore.Causality.ExistenceActuality TruthCore.Ontology.ConcreteAbstract CogitoConcrete

/-- One subject has a reason evaluated at a different world. Esse at every
existent is respected, yet the selected world has no individual. -/
def StandpointControl : Prop :=
    let m : Ontic Bool Unit := ⟨⟨Eq⟩, fun w _ => w = true, fun _ _ _ => False⟩
    let r : Unit → Unit → Prop := fun _ _ => True
    ThereAreEpistemicReasons r ∧ ReasonBearerPresentAt r id m true ∧
      ExistingInActAt m (fun _ (_ : Unit) => True) () false ∧
      ¬ InhabitedConcreteAt m (HasEsseInRe (fun _ (_ : Unit) => True) ()) false

end TruthCore.Logic.EpistemicReasonBearer
