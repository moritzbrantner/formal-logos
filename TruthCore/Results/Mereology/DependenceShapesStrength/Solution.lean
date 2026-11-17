module

public import TruthCore.Mereology.DependenceShapesStrength

@[expose] public section
namespace TruthCore.Results.Mereology.DependenceShapesStrength
open TruthCore.Mereology.DependenceShapes
open TruthCore.Mereology.DependenceShapesStrength
open TruthCore.Mereology.UniversalFusionBoundary

theorem restrictedOfUnrestricted (B : Type) [PartialOrder B]
    (h : ProperExtensionality B) : CompositeExtensionality B := by
  intro x y _ _ same
  exact h x y same

theorem exactDifference : ExactDifference := by
  classical
  intro B _
  change ProperExtensionality B ↔ CompositeExtensionality B ∧ AtMostOneMinimal B
  constructor
  · intro h
    refine ⟨restrictedOfUnrestricted B h, ?_⟩
    intro x y hx hy
    apply h x y
    intro p
    exact ⟨fun hp => (hx.not_lt hp).elim, fun hp => (hy.not_lt hp).elim⟩
  · rintro ⟨restricted, minimal⟩ x y same
    by_cases hx : Composite x
    · obtain ⟨p, hp⟩ := hx
      exact restricted x y ⟨p, hp⟩ ⟨p, (same p).mp hp⟩ same
    · have hminx : IsMin x := isMin_iff_forall_not_lt.mpr
        (fun p hp => hx ⟨p, hp⟩)
      have hminy : IsMin y := isMin_iff_forall_not_lt.mpr
        (fun p hp => hx ⟨p, (same p).mpr hp⟩)
      exact minimal x y hminx hminy

end TruthCore.Results.Mereology.DependenceShapesStrength
