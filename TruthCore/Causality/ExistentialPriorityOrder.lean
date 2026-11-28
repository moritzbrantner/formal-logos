module

public import TruthCore.Causality.ExistentialSelfActualization
public import TruthCore.Logic.Regress

/-! Analyst formulations for the existing mixed-token self-production route.
The original inputs Occurs, bearer and produces already fix the exercise
profile. The shared CausalityFrame has neither exercise tokens nor production
of existence by an exercise. No frame primitive or priority sense is added. -/

@[expose] public section

namespace TruthCore.Causality.ExistentialPriorityOrder

open TruthCore.Causality.ExistentialSelfActualization
open TruthCore.Logic.Regress

/-- The least edge relation required by BearerPrior and ProductPrior, with
their original occurrence guards. The two orientations distinguish edge kinds
within the mixed carrier; neither component is assigned a historical sense. -/
def RequiredEdge {B E : Type} (Occurs : E → Prop) (bearer : E → B)
    (produces : E → B → Prop) : Sum B E → Sum B E → Prop
  | .inl x, .inr a => Occurs a ∧ bearer a = x
  | .inr a, .inl x => Occurs a ∧ produces a x
  | .inl _, .inl _ | .inr _, .inr _ => False

/-- OPEN application premise: on this very exercise profile, the required
mixed edges have no nonempty finite closed walk. -/
def RequiredEdgesAcyclic {B E : Type} (Occurs : E → Prop) (bearer : E → B)
    (produces : E → B → Prop) : Prop :=
  (Graph.mk (RequiredEdge Occurs bearer produces)).NoCycles

/-- Existence of some strict partial order extending only the required edges.
Additional semantic constraints on Prior would need a separate test. -/
def CommonStrictOrder {B E : Type} (Occurs : E → Prop) (bearer : E → B)
    (produces : E → B → Prop) : Prop :=
  ∃ Prior, BearerPrior Occurs bearer Prior ∧ ProductPrior Occurs produces Prior ∧
    IrreflexivePriority Prior ∧ TransitivePriority Prior

/-- Acyclicity exactly characterizes the common strict extension problem. -/
def ExactExtensionCriterion : Prop :=
  ∀ (B E : Type) (Occurs : E → Prop) (bearer : E → B) (produces : E → B → Prop),
    CommonStrictOrder Occurs bearer produces ↔ RequiredEdgesAcyclic Occurs bearer produces

/-- One bearer, one occurring act of that bearer, production at the only pair. -/
def SplitPriorityControl : Prop :=
  ∃ bearer : Unit → Unit, ∃ Left Right : Sum Unit Unit → Sum Unit Unit → Prop,
    BearerPrior (fun _ => True) bearer Left ∧
    ProductPrior (fun _ => True) (fun _ _ => True) Right ∧
    IrreflexivePriority Left ∧ TransitivePriority Left ∧
    IrreflexivePriority Right ∧ TransitivePriority Right ∧
    ¬ NoSelfProduction (fun _ => True) bearer (fun _ _ => True) ∧
    IrreflexivePriority (RequiredEdge (fun _ => True) bearer (fun _ _ => True)) ∧
    ¬ TransitivePriority (RequiredEdge (fun _ => True) bearer (fun _ _ => True)) ∧
    ¬ CommonStrictOrder (fun _ => True) bearer (fun _ _ => True)

/-- Two bearers and two occurring acts. Each act produces only the other
bearer. Direct self-production is absent, yet no common strict order exists. -/
def ReciprocalProductionControl : Prop :=
  NoSelfProduction (fun _ : Bool => True) id (· ≠ ·) ∧
    ¬ CommonStrictOrder (fun _ : Bool => True) id (· ≠ ·)

end TruthCore.Causality.ExistentialPriorityOrder
