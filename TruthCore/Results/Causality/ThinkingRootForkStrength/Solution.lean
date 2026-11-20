module

public import TruthCore.Results.Causality.ThinkingRootFork.Solution

/-! Strength-order registrations for the #1791 thinker-only fork (#1017).
Each theorem has exactly one premise, an older Cogito ancestry premise, and
concludes the narrower premise used by `necessaryThinkingRootOfThought` at the
same profile, world and thought predicates. The proofs reuse the ordinary
helpers of `ThinkingRootFork.Solution`. Strictness (that the weak version does
not entail the strong one) is not checked here. -/

@[expose] public section

namespace TruthCore.Results.Causality.ThinkingRootForkStrength

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.ThinkingRootFork

/-- Accessibility of every occurring-thought bearer for the full actual
concrete grounding relation implies its accessibility for the restricted
distinct-thinking mediate predecessor relation. -/
theorem thinkingAccessibilityOfGroundingAccessibility {W B Episode : Type}
    (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOld : ThinkerGroundingAccessible m Occurs Bears w) :
    ThinkingBearerPredecessorAccessible m w Occurs Bears :=
  TruthCore.Results.Causality.ThinkingRootFork.oldAccessibilitySuppliesThinkingAccessibility
    m w Occurs Bears hOld

/-- Grounding of every contingent actual concrete cone member of an
occurring-thought bearer implies grounding of its contingent *thinking* cone
members. -/
theorem thinkingGroundingOfAncestryGrounded {W B Episode : Type}
    (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hOld : ThinkerAncestryGrounded m Occurs Bears w) :
    ThinkingBearerConeContingentGrounded m w Occurs Bears :=
  TruthCore.Results.Causality.ThinkingRootFork.oldGroundingSuppliesThinkingGrounding
    m w Occurs Bears hOld

end TruthCore.Results.Causality.ThinkingRootForkStrength
