module

public import TruthCore.Modal.ActualistContingencyRoute
public import TruthCore.Results.Modal.ActualistDomains.Solution
public import TruthCore.Results.Causality.ContingentBeingNode.Solution

@[expose] public section

namespace TruthCore.Results.Modal.ActualistContingencyRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ContingentBeingNode
  (SomeActualContingentAt EveryActualConcreteNecessaryAt)
open TruthCore.Modal.ActualistContingencyRoute
open TruthCore.Results.Modal.ActualistDomains (checks)
open TruthCore.Results.Causality.ContingentBeingNode (notEveryNecessary)

/-- Strength order: the forward transfer gives concrete NECESSARY_2 at each
world, through the library's correspondence with increasing domains. -/
theorem transferGivesConcreteNecessary {W B : Type} (m : Profile W B) (w : W)
    (hTransfer : RouteForwardTransfer m) : EveryActualConcreteNecessaryAt m w := by
  obtain ⟨forwardIffIncreasing, _, _, _⟩ := checks
  have hIncreasing := (forwardIffIncreasing W B m.ontic).mp hTransfer
  intro x _ hx v hv
  exact hIncreasing w v hv x hx

/-- The route's contingent bearer rules out the forward transfer policy: the
existing refutation of concrete necessitarianism composed with the strength
order. -/
theorem forwardTransferFails {W B : Type} (m : Profile W B) (w : W)
    (hContingent : SomeActualContingentAt m w) : NoRouteForwardTransfer m := by
  intro hTransfer
  exact notEveryNecessary m w hContingent (transferGivesConcreteNecessary m w hTransfer)

/-- The strictness controls. -/
theorem controls : Control.Strictness := by
  obtain ⟨forwardIffIncreasing, _, _, _⟩ := checks
  have hNecessary : ∀ w, EveryActualConcreteNecessaryAt Control.abstractDrop w := by
    intro w x hc _ v _
    exact Or.inl hc
  refine ⟨⟨hNecessary, ?_, fun w hContingent =>
    notEveryNecessary _ w hContingent (hNecessary w)⟩, ⟨?_, ?_⟩⟩
  · intro hTransfer
    have hThere := (forwardIffIncreasing Bool Bool Control.abstractDrop.ontic).mp
      hTransfer false true True.intro false (Or.inr rfl)
    rcases hThere with h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  · intro x _ hx v _
    rcases hx with h | h
    · exact Or.inl h
    · exact Bool.noConfusion h
  · intro hTransfer
    have hThere := (forwardIffIncreasing Bool Bool Control.concreteDrop.ontic).mp
      hTransfer false true True.intro false (Or.inr rfl)
    rcases hThere with h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h

end TruthCore.Results.Modal.ActualistContingencyRoute
