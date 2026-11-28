module

public import TruthCore.Causality.StructuralCausalModel
public import TruthCore.Causality.CounterfactualDependence
public import TruthCore.Causality.Frame
public import TruthCore.Causality.InterventionTransitivity
public import TruthCore.Explanation.MechanismInterventionParity
public import TruthCore.Explanation.PairedInterventions

/-! Adapters preserve the semantics of the supplied interfaces. Frame-level
causation remains an input, and the Boolean examples concern variables,
not the existence or production of their concrete bearers. -/

@[expose] public section

namespace TruthCore.Causality.StructuralCausalModel

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.WorldSourceRegress (Actual actualGraph)
open TruthCore.Causality.InterventionTransitivity (Variable inputGraph)

variable {U A W B T R : Type}

/-- Put structural equations on the existing actual-node graph at one world.
Both the causal links and actuality come from the frame's ontology; the
equations and well-foundedness are supplied separately. -/
def onActualGraph (F : CausalityFrame W B T R) (w : W)
    [Finite (Actual F.history.ontic w)]
    (wf : WellFounded (actualGraph F.history.ontic w).edge)
    (equation : (v : Actual F.history.ontic w) → U →
      ({p : Actual F.history.ontic w // F.history.ontic.Causes w p.val v.val} → A) → A) :
    Model (Actual F.history.ontic w) U A :=
  ⟨⟨(actualGraph F.history.ontic w).edge⟩, wf, equation⟩

section Counterfactual

open TruthCore.Causality.CounterfactualDependence
  (interventionSelection intervention_hasSelection_iff intervention_would_iff)
open TruthCore.Modal.CounterfactualSelection (HasSelection Would)

variable {V : Type} [Finite V]

/-- Candidate valuation world with context fixed and endogenous values
recomputed. The starting context is supplied, so no inference of context
from the starting valuation is performed. -/
def responseWorld (m : Model V U A) (s : Setting V A) (w : U × (V → A)) :
    U × (V → A) :=
  (w.1, m.response w.1 s)

/-- A forced value gives a nonempty selection for its event. At that
antecedent the existing counterfactual semantics evaluates Q in the unique
recomputed outcome. World here means context and valuation. -/
theorem selection_forced (m : Model V U A) (s : Setting V A) (w : U × (V → A))
    {v : V} {a : A} (h : s v = some a) (Q : Set (U × (V → A))) :
    let select := interventionSelection (responseWorld m s)
    let event : Set (U × (V → A)) := {w' | w'.2 v = a}
    HasSelection select w event ∧ (Would select w event Q ↔ responseWorld m s w ∈ Q) := by
  dsimp only
  have success : responseWorld m s w ∈ {w' : U × (V → A) | w'.2 v = a} :=
    m.response_forced w.1 s h
  exact ⟨(intervention_hasSelection_iff _ _ _).mpr success,
    intervention_would_iff _ _ _ Q success⟩

end Counterfactual

def rank : Variable → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

theorem xy : inputGraph.edge .x .y := Or.inl ⟨rfl, rfl⟩
theorem xz : inputGraph.edge .x .z := Or.inr (Or.inl ⟨rfl, rfl⟩)
theorem yz : inputGraph.edge .y .z := Or.inr (Or.inr ⟨rfl, rfl⟩)

instance : Finite Variable := by
  apply Finite.of_injective rank
  intro p v h
  cases p <;> cases v <;> simp_all [rank]

/-- Reuse the exact declared graph of InterventionTransitivity. -/
def three (x : U → Bool) (y : U → Bool → Bool) (z : U → Bool → Bool → Bool) :
    Model Variable U Bool where
  graph := ⟨inputGraph.edge⟩
  acyclic := Subrelation.wf (r := fun p v => rank p < rank v)
    (by rintro p v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide)
    (measure (fun v => (rank v).val)).wf
  equation v u parent := match v with
    | .x => x u
    | .y => y u (parent ⟨.x, xy⟩)
    | .z => z u (parent ⟨.x, xz⟩) (parent ⟨.y, yz⟩)

open TruthCore.Explanation.MechanismInterventionParity (override)

private theorem override_eq (b : Bool) (s : Option Bool) : override b s = s.getD b := by
  cases s <;> rfl

/-- Closed form of the recursive three-equation solution at any setting. -/
theorem three_response (x : U → Bool) (y : U → Bool → Bool) (z : U → Bool → Bool → Bool)
    (u : U) (s : Setting Variable Bool) :
    (three x y z).response u s =
      let a := override (x u) (s .x)
      let b := override (y u a) (s .y)
      fun v => match v with
        | .x => a
        | .y => b
        | .z => override (z u a b) (s .z) := by
  symm
  apply ((three x y z).intervene s).eq_solve u
  intro v
  cases v <;> simp [Model.intervene, three, override_eq]

namespace BinaryButFor

def lift (m : InterventionTransitivity.Model) : Model Variable Unit Bool :=
  three (fun _ => m.actualX) (fun _ => m.f) (fun _ => m.g)

theorem natural (m : InterventionTransitivity.Model) : (lift m).solve () = m.actual := by
  rw [← Model.response_natural, lift, three_response]
  funext v
  cases v <;> rfl

theorem surgery (m : InterventionTransitivity.Model) (v : Variable) (b : Bool) :
    (lift m).response () (setOne v b) = m.intervene v b := by
  rw [lift, three_response]
  cases v <;> rfl

theorem butFor_iff (m : InterventionTransitivity.Model) (a b : Variable) :
    InterventionTransitivity.ButFor m a b ↔
      a ≠ b ∧
        (lift m).response () (setOne a (!((lift m).solve () a))) b ≠ (lift m).solve () b := by
  rw [natural, surgery]
  exact ⟨fun h => ⟨h.distinct, h.changed⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Declared ancestry survives in the cancellation model although flipping
the actual X leaves Z unchanged. -/
theorem ancestry_without_butFor :
    Relation.TransGen (lift InterventionTransitivity.cancellation).graph.Adj .x .z ∧
      InterventionTransitivity.ButFor InterventionTransitivity.cancellation .x .y ∧
      InterventionTransitivity.ButFor InterventionTransitivity.cancellation .y .z ∧
      ¬ InterventionTransitivity.ButFor InterventionTransitivity.cancellation .x .z := by
  refine ⟨(Relation.TransGen.single xy).tail yz, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  intro h
  exact h.changed rfl

end BinaryButFor

namespace Mechanism

open TruthCore.Explanation

def setting (s : MechanismInterventionParity.Setting) : Setting Variable Bool
  | .x => s.setA
  | .y => s.setB
  | .z => none

def readout (v : Variable → Bool) : MechanismInterventionParity.Observation := ⟨v .x, v .y, v .z⟩

def responsive : Model Variable MechanismInterventionParity.TwoState Bool :=
  three MechanismInterventionParity.TwoState.first (fun s _ => s.second) (fun _ a b => a && b)

def background : Model Variable MechanismInterventionParity.TwoState Bool :=
  three MechanismInterventionParity.TwoState.first (fun s _ => s.second) (fun s _ _ => s.first && s.second)

theorem responsive_matches (u : MechanismInterventionParity.TwoState) (s : MechanismInterventionParity.Setting) :
    readout (responsive.response u (setting s)) = MechanismInterventionParity.pluralRun u s := by
  rw [responsive, three_response]
  rfl

theorem background_matches (u : MechanismInterventionParity.TwoState) (s : MechanismInterventionParity.Setting) :
    readout (background.response u (setting s)) = MechanismInterventionParity.idleRun u s := by
  rw [background, three_response]
  rfl

/-- Matched natural reports and a single-channel contrast. The selected
earlier input remains true in both models and the current channel is set
false in both. The output differs. See the research note for the separate
interpretation of these variables as parts of a persistence test. -/
theorem single_channel_contrast :
    (∀ u, readout (responsive.response u (setting MechanismInterventionParity.natural)) =
      readout (background.response u (setting MechanismInterventionParity.natural))) ∧
    (let cut := setting ⟨none, some false⟩
     readout (responsive.response ⟨true, true⟩ cut) = ⟨true, false, false⟩ ∧
     readout (background.response ⟨true, true⟩ cut) = ⟨true, false, true⟩) := by
  constructor
  · intro u
    rw [responsive_matches, background_matches]
    rfl
  · dsimp only
    rw [responsive_matches, background_matches]
    exact ⟨rfl, rfl⟩

end Mechanism

namespace Paired

open TruthCore.Explanation.PairedInterventions (paired)
open TruthCore.Logic.AtomismIndependence (Triple Index coordinate)

/-- Run the existing paired-toggle response for the selected report. X and Y
are the two switches. Z is a report chosen in the exogenous context. -/
def toggle : Model Variable (Triple × Index) Bool :=
  three (fun _ => false) (fun _ _ => false) (fun (u, i) left right =>
    coordinate (paired u left right) i)

theorem toggle_matches (u : Triple) (i : Index) (left right : Bool) :
    toggle.response (u, i) (Mechanism.setting ⟨some left, some right⟩) .z =
      coordinate (paired u left right) i := by
  rw [toggle, three_response]
  rfl

end Paired

end TruthCore.Causality.StructuralCausalModel
