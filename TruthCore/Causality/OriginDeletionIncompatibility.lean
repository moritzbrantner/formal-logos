module

public import TruthCore.Causality.OriginDeletion
public import TruthCore.Causality.BruteFoundationBoundary

/-!
# Worldwise deletion excludes a necessary concretum (#2103)

Analyst formulation, attribution deferred. Certificate for the typed rival
relation `e8a48d7f` (`2f055224` attacks `b19ffd92`): on one profile, read with
its own Ontic and concreteness predicate, worldwise deletion
(`OriginDeletion.WorldwiseDeletion`) and a concrete individual existing at `w`
and at every world accessible from `w` (`BruteFoundationBoundary.NecessaryConcreteAt`)
cannot both hold. A statement about the formal readings only; neither is
asserted.
-/

@[expose] public section

namespace TruthCore.Causality.OriginDeletionIncompatibility

open TruthCore.Causality.OriginDeletion (WorldwiseDeletion)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)

/-- For every profile and world, worldwise deletion on the profile's Ontic and
concreteness predicate excludes a necessary concretum at that world. -/
def DeletionExcludesNecessaryConcrete : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W),
    WorldwiseDeletion m.ontic m.concrete → ¬ NecessaryConcreteAt m w

end TruthCore.Causality.OriginDeletionIncompatibility
