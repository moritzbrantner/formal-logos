module

public import TruthCore.Logic.Strength.RouteSymmetryIdentity

@[expose] public section

namespace TruthCore.Results.Logic.Strength.RouteSymmetryIdentity

open TruthCore.Modal (Symmetric)
open TruthCore.Logic.Strength.RouteSymmetryIdentity (SameRouteSymmetry)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ModalSenseSupport (OnticFrameSymmetric)
open TruthCore.Logic.Strength.NecessaryFrames (RouteFrameSymmetric)

theorem sameRouteSymmetry : SameRouteSymmetry := by
  exact fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

theorem nodeDelta {W : Type} (σ : Signature) (m : Profile W σ.Being) :
    RouteFrameSymmetric σ m ↔ Symmetric m.ontic.frame := by
  exact Iff.rfl

theorem frameDelta {W : Type} (σ : Signature) (m : Profile W σ.Being) :
    OnticFrameSymmetric m ↔ Symmetric m.ontic.frame := by
  exact Iff.rfl

end TruthCore.Results.Logic.Strength.RouteSymmetryIdentity
