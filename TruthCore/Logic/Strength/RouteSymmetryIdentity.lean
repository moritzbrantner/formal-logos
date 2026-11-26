module

public import TruthCore.Logic.Strength.NecessaryFrames
public import TruthCore.Causality.ModalSenseSupport

@[expose] public section

namespace TruthCore.Logic.Strength.RouteSymmetryIdentity

open TruthCore.Modal (Symmetric)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ModalSenseSupport (OnticFrameSymmetric)
open TruthCore.Logic.Strength.NecessaryFrames (RouteFrameSymmetric)

/-- Both named deltas express B on the same selected profile's frame. -/
def SameRouteSymmetry : Prop :=
  ∀ {W : Type} (σ : Signature) (m : Profile W σ.Being),
    (RouteFrameSymmetric σ m ↔ Symmetric m.ontic.frame) ∧
    (OnticFrameSymmetric m ↔ Symmetric m.ontic.frame)

end TruthCore.Logic.Strength.RouteSymmetryIdentity
