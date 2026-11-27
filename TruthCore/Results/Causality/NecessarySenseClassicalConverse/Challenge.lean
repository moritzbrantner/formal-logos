import TruthCore.Causality.NecessarySenseFork
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.NecessarySenseClassicalConverse

open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Logic (ExcludedMiddle)

/-- Classical converse of `boxKToTertiaVia`: with excluded middle, the tertia
via's "n cannot not-be", possibility read as the frame's diamond at `w`, gives
existence of the same `n` at every world accessible from `w`. The root facts
are carried unchanged. -/
theorem tertiaViaToBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (hEM : ExcludedMiddle)
    (h : NecessaryRootTertiaVia σ m w CN) : NecessaryRootBoxK σ m w CN := by
  sorry

/-- Under excluded middle the two nodes are equivalent: the tertia via node
adds no content to the box K node and takes none away. -/
theorem tertiaViaIffBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (hEM : ExcludedMiddle) :
    NecessaryRootTertiaVia σ m w CN ↔ NecessaryRootBoxK σ m w CN := by
  sorry

end TruthCore.Results.Causality.NecessarySenseClassicalConverse
