import TruthCore.Causality.ThinkingRootFork
import TruthCore.Causality.RootPositiveIntellectWill

namespace TruthCore.Results.Causality.CogitoActualRoot

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ThinkingRootFork (NecessaryThinkingRootOfThought)
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)

/-- The Cogito route's necessary thinking root is an actual concrete root of
the selected relation at the same world: keep its rootness clause and drop
thinking, ancestry and necessity. -/
theorem actualRootOfThinkingRoot {W B Episode : Type} (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (h : NecessaryThinkingRootOfThought m w Occurs Bears) :
    ActualRootExistsAt m w := by
  sorry

end TruthCore.Results.Causality.CogitoActualRoot
