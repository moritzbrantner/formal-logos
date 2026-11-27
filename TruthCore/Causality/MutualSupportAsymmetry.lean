module

public import TruthCore.Causality.GradedSupportFoundation
public import Mathlib.Order.WellFounded

@[expose] public section

namespace TruthCore.Causality.MutualSupportAsymmetry

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.GradedSupportFoundation (NoInfiniteAscentAmongNecessaryConcreta)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- Reverse comparisons are excluded on candidates selected by the classifier
and existing at every world accessible from w. -/
def NecessaryGradeAsymmetric {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ a b, m.concrete a → m.concrete b → NecessaryAt m.ontic w a →
    NecessaryAt m.ontic w b → MoreIn esse a b → ¬ MoreIn esse b a

/-- Strictness of the weakening to asymmetry. -/
def AsymmetryWithoutFoundation : Prop :=
  ∃ (m : Profile Unit Nat) (MoreIn : Unit → Nat → Nat → Prop),
    NecessaryGradeAsymmetric m () MoreIn () ∧
    ¬ NoInfiniteAscentAmongNecessaryConcreta m () MoreIn ()

end TruthCore.Causality.MutualSupportAsymmetry
