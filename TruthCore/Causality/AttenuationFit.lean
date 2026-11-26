module

public import TruthCore.Causality.ClosedGroundingRoots

/-! Fitting quantitative reception data on a fixed grounding profile. -/
@[expose] public section

namespace TruthCore.Causality.ClosedGroundingRoots

open BruteFoundationBoundary (Profile)
open NecessaryRootFork (ActualConcrete)
open CogitoNecessaryConcrete (ActualConcreteGround)

/-- The existential numerical profile is equivalent to countability and rootedness
of the supplier-closed collections of actual concreta, in the same world. -/
def AttenuationFitCriterion (m : Profile W B) (w : W) : Prop :=
  AttenuatedEsseReception m w ↔
    Countable {x // ActualConcrete m w x} ∧ ClosedGroundingCollectionsRooted m w

namespace FixedAmounts

/-- Both bearers are actual. The sole grounding arrow is from false to true. -/
def pair : Profile Unit Bool where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ a b => a = false ∧ b = true

abbrev Bearer := {x // ActualConcrete pair () x}
def giver : Bearer := ⟨false, trivial, trivial⟩
def recipient : Bearer := ⟨true, trivial, trivial⟩

/-- Exact compatibility of amounts specified in advance on the single-edge pair. -/
def FixedAmountCriterion : Prop :=
  ∀ P : Bearer → ℝ, (∀ x, 0 < P x) →
    ((∃ wt s q M, AttenuationLaws pair () wt s P q M) ↔ P recipient < P giver)

end FixedAmounts
end TruthCore.Causality.ClosedGroundingRoots
