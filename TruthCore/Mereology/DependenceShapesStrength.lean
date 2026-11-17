module

public import TruthCore.Mereology.DependenceShapes
public import TruthCore.Logic.StrengthComparison

/-! Strength registration for #336's existing extensionality predicates.
The carrier and its partial order are shared by both sides. The additional
content of the unrestricted principle is uniqueness of minimal objects.
No existing predicate, sense identity or DS-3 control is changed.
-/

@[expose] public section
namespace TruthCore.Mereology.DependenceShapesStrength
open DependenceShapes
open TruthCore.Logic.StrengthComparison

/-- At most one minimal object, without asserting existence of one. -/
def AtMostOneMinimal (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, IsMin x → IsMin y → x = y

/-- No background assumption beyond the same supplied partial order. -/
def comparison (B : Type) [PartialOrder B] : ComparisonSpec where
  stronger := ProperExtensionality B
  weaker := CompositeExtensionality B
  delta := AtMostOneMinimal B

/-- Unrestricted proper-part identity adds exactly minimal-object uniqueness
 to composite-restricted identity, on each fixed domain/order. -/
def ExactDifference : Prop :=
  ∀ (B : Type) [PartialOrder B], Equivalence (comparison B)

end TruthCore.Mereology.DependenceShapesStrength
