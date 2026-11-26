import TruthCore.Causality.FirstMoverNecessity
import TruthCore.Causality.NecessarySupportCoverage

namespace TruthCore.Results.Causality.FirstMoverUnderived

open TruthCore.Case.Catholicism (IsFirstUnmovedMover)
open TruthCore.Causality.FirstMoverNecessity
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.NecessaryConcreteUnderived (NecessaryConcreteUnderivedAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessarySupportCoverage (NecessarySupportActuallyCovered)
open TruthCore.Causality.NecessarySupportCoverage.Control (uncoveredEdge)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing PureAct)

/-- The same mover keeps all the properties in the actual-root premise and has
no incoming concrete support at any admitted world. -/
theorem sameMoverUnderived {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W)
    (hMover : FirstMoverNecessaryFirstRootAt F MovedIn InPotency concrete grounds w)
    (hCoverage : NecessarySupportActuallyCovered (groundProfile F concrete grounds) w) :
    ∃ f, IsFirstUnmovedMover MovedIn F.MovesIn f ∧
      ActualRoot (groundProfile F concrete grounds) w f ∧
      NecessaryAt F.history.ontic w f ∧ IsFirstBeing F.PriorSimply f ∧ PureAct InPotency f ∧
      ∀ v a, concrete a → F.history.ontic.ExistsAt v a → ¬ grounds v a f := by
  sorry

/-- The modal spine's underivedness node, on the mover's own grounding profile. -/
theorem underivedOfFirstMoverRoot {W B T R : Type} (F : CausalityFrame W B T R)
    (MovedIn InPotency : B → R → Prop) (concrete : B → Prop)
    (grounds : W → B → B → Prop) (w : W)
    (hMover : FirstMoverNecessaryFirstRootAt F MovedIn InPotency concrete grounds w)
    (hCoverage : NecessarySupportActuallyCovered (groundProfile F concrete grounds) w) :
    NecessaryConcreteUnderivedAt (groundProfile F concrete grounds) w := by
  sorry

/-- The uncovered-edge model with motion added. The sole first mover is an
actual necessary root, with incoming support at the other world. A different
bearer satisfies the existential underivedness endpoint. -/
theorem uncoveredFirstMoverControl :
    ∃ F : CausalityFrame Bool Bool Unit Bool,
      FirstMoverNecessaryFirstRootAt F Model.movedIn Model.movedPotency
        uncoveredEdge.concrete uncoveredEdge.grounds false ∧
      ¬ NecessarySupportActuallyCovered
        (groundProfile F uncoveredEdge.concrete uncoveredEdge.grounds) false ∧
      NecessaryConcreteUnderivedAt
        (groundProfile F uncoveredEdge.concrete uncoveredEdge.grounds) false ∧
      ¬ ∃ f, IsFirstUnmovedMover Model.movedIn F.MovesIn f ∧
        ∀ v a, uncoveredEdge.concrete a → F.history.ontic.ExistsAt v a →
          ¬ uncoveredEdge.grounds v a f := by
  sorry

end TruthCore.Results.Causality.FirstMoverUnderived
