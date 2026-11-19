import TruthCore.Causality.ThinkingRootFork
import TruthCore.Results.Logic.CogitoSubject.Solution

/-! The two literal horns share *one* root witness. Only the positive horn
descends, and it descends through distinct thinkers rather than every ground.
The modal upgrade applies to that same endpoint. All metaphysical bridges
remain hypotheses; in particular no God-existence theorem is used. -/

namespace TruthCore.Results.Causality.ThinkingRootFork

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ThinkingRootFork
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

variable {W B Episode : Type}

/-- `P` supplies a strictly earlier *thinking* ancestor and `¬P` terminates
at an actual thinking ground-root. `Acc` is only for the thinker relation:
nonthinking ancestors may form cycles. The same endpoint is retained along
the finite concrete ancestry chain. -/
theorem thinkingRootOfAccessible (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hAcc : Acc (ThinkerPredecessor m w Occurs Bears) selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hEM : ExcludedMiddle) :
    ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
      ActualRoot m w n := by
  sorry

/-- The **same** terminal thinker is necessary if contingent thinking members
of this selected cone always have an actual concrete ground. Without that
anti-brute assumption the root could remain contingent. -/
theorem necessaryThinkingRootOfSelected (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (selected : B)
    (hActual : ActualConcrete m w selected) (hThink : Thinks Occurs Bears selected)
    (hAcc : Acc (ThinkerPredecessor m w Occurs Bears) selected)
    (hNoFresh : NoFreshThinkerInCone m w Occurs Bears selected)
    (hGrounded : ConeContingentThinkersGrounded m w Occurs Bears selected)
    (hEM : ExcludedMiddle) :
    NecessaryThinkingRootOf m w Occurs Bears selected := by
  sorry

/-- Existing Cogito subjecthood and its separate actuality/concreteness
bridges supply the starting thinker. The ancestry premises are scoped to the
selected occurring-thought bearer, not to arbitrary beings in the carrier. -/
theorem necessaryThinkingRootOfThought (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkingBearerPredecessorAccessible m w Occurs Bears)
    (hNoFresh : ThinkingBearerConeNoFresh m w Occurs Bears)
    (hGrounded : ThinkingBearerConeContingentGrounded m w Occurs Bears)
    (hEM : ExcludedMiddle) :
    NecessaryThinkingRootOfThought m w Occurs Bears := by
  sorry

end TruthCore.Results.Causality.ThinkingRootFork
