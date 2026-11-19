import TruthCore.Causality.FrameAdapters

/-!
Scratch demo for #1784 (shared frames). NOT a corpus result, not registered,
and it supports no premise. It shows statements from two modules stated over
one `CausalityFrame`, so that they share the frame's symbols:
`ConcurrentActualization` (time-indexed giving, `F.GivesAt`) and
`Round2Grounding` (tenseless causing of esse, `F.CausesIn`, and dependence for
being). They connect only through the explicit open bridge
`CausesOfBeingConcur`. Without it the composition fails: see `withoutBridge`.

Check with `lake env lean Scratch/causality-frame/Demo.lean`.
-/

namespace CausalityFrameDemo

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FrameAdapters

/-- Over one frame: if received esse is concurrently actualized
(ConcurrentActualization), causes of being concur with whoever gives being
(the explicit bridge), and an effect of esse depends for being on its cause
(Round2Grounding), then a distinct cause of the being of a received-esse
thing gives it being at every moment it is present, and the thing depends for
being on it. -/
theorem composed {W B T R P : Type} (F : CausalityFrame W B T R)
    (EsseReceivedIn : B → P → Prop)
    (hAct : ConcurrentlyActualized F EsseReceivedIn)
    (hBridge : CausesOfBeingConcur F)
    (hDep : EsseEffectDependsOnItsCause F) :
    ∀ v c x t z, c ≠ x → F.CausesIn c x F.esse → EsseReceivedIn x z →
      F.history.IsAt v x t → F.GivesAt v c x t ∧ F.DependsForBeing x c := by
  intro v c x t z hne hc hz ht
  obtain ⟨g, hg⟩ := hAct v x t z hz ht
  exact ⟨hBridge v c g x t hne hc hg, hDep c x hne hc⟩

/-- A frame on `Bool` beings: `true` causes the esse of `false`, but only `false`
gives itself being (intrinsic persistence power, as in
`ConcurrentActualization.Control`). -/
def selfGiving : CausalityFrame Unit Bool Nat Unit where
  history :=
    { ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True,
                 Causes := fun _ _ _ => False }
      IsAt := fun _ _ _ => True
      now := 0 }
  GivesAt := fun _ c x _ => c = false ∧ x = false
  CausesIn := fun c x _ => c = true ∧ x = false
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun x c => x = false ∧ c = true
  PriorSimply := fun _ _ => False
  esse := ()

/-- Without the bridge the composition fails: concurrent actualization and
Round2Grounding's dependence premise hold on `selfGiving`, the bridge fails,
and the cause `true` never gives `false` being. -/
theorem withoutBridge :
    ConcurrentlyActualized selfGiving (fun x (_ : Unit) => x = false) ∧
      EsseEffectDependsOnItsCause selfGiving ∧
      ¬ CausesOfBeingConcur selfGiving ∧
      ¬ selfGiving.GivesAt () true false 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v x t z hz _
    exact ⟨false, rfl, hz⟩
  · intro c x _ hc
    exact ⟨hc.2, hc.1⟩
  · intro h
    have := h () true false false 0 (by decide) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact absurd this.1 (by decide)
  · intro h
    exact absurd h.1 (by decide)

end CausalityFrameDemo
