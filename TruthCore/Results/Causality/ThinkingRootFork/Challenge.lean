import TruthCore.Causality.ThinkingRootFork
import TruthCore.Results.Logic.CogitoSubject.Solution

namespace TruthCore.Results.Causality.ThinkingRootFork

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ThinkingRootFork
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

variable {W B Episode : Type}

/-- The literal P/¬P descent ends at an actual *thinking* source. -/
theorem thinkingRootOfAccessible (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hAcc : Acc (ThinkerPredecessor m w Occurs Bears) selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hEM : ExcludedMiddle) :
    ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
      ActualRoot m w n := by
  sorry

/-- The same endpoint is necessary if contingent thinkers in its cone are grounded. -/
theorem necessaryThinkingRootOfSelected (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hAcc : Acc (ThinkerPredecessor m w Occurs Bears) selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hGrounded : ConeContingentThinkersGrounded m w Occurs Bears selected)
    (hEM : ExcludedMiddle) :
    NecessaryThinkingRootOf m w Occurs Bears selected := by
  sorry

/-- Reuse Cogito subjecthood and explicit actuality to supply the first thinker. -/
theorem necessaryThinkingRootOfThought (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ∀ b e, Occurs e → Bears b e →
      Acc (ThinkerPredecessor m w Occurs Bears) b)
    (hNoFresh : ∀ b e, Occurs e → Bears b e →
      NoFreshThinkerInCone m w Occurs Bears b)
    (hGrounded : ∀ b e, Occurs e → Bears b e →
      ConeContingentThinkersGrounded m w Occurs Bears b)
    (hEM : ExcludedMiddle) :
    NecessaryThinkingRootOfThought m w Occurs Bears := by
  sorry

end TruthCore.Results.Causality.ThinkingRootFork
