module

public import TruthCore.Causality.WholeRosterFoundation
public import TruthCore.Causality.RootPositiveIntellectWill
public import TruthCore.Logic.StrengthComparison

/-! Root-supply interface (#1926, phase 2, slice 2a)

The interface is the existing `RootPositiveIntellectWill.ActualRootExistsAt`:
some actual concretum at `w` has no actual concrete ground in the profile's
selected relation `grounds w` (a root relative to that relation only,
`DEF-BRUTE-ROOT-RELATIVE-GROUNDING`; it may have a non-concrete, absent or
unmodelled explanation). Grounding, causing, priority and the other relations
stay distinct: everything here is about one selected relation `m.grounds`.

The root-supply variants of the corpus are stated without population and,
mostly, without excluded middle. They therefore do not entail root existence
by themselves (an empty world has no root). What they entail, constructively,
is `WholeRosterFoundation.WholeRosterNotTrapped`: the nonempty actual roster
is not a borrowing trap. This module records that whole-roster nontrapping is
exactly the population-conditional, double-negated form of the interface
(`WholeRosterIsInhabitedRootNotAbsent`), and certifies how root existence
differs from it: root existence adds that the actual roster is inhabited and
that root existence is stable (`InhabitedWithStableRoot`). Under explicit
excluded middle the stability conjunct holds automatically, so classically the
difference is population alone. No premise is asserted here. -/

@[expose] public section

namespace TruthCore.Causality.RootSupplyInterface

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Logic.StrengthComparison

/-- Difference of root existence over whole-roster nontrapping: some actual
concretum exists at `w`, and root existence is stable (if it is not the case
that no actual root exists, an actual root exists). The second conjunct follows
from excluded middle for this one proposition and is weaker than excluded
middle. -/
def InhabitedWithStableRoot {W B : Type} (m : Profile W B) (w : W) : Prop :=
  InhabitedConcreteAt m.ontic m.concrete w ∧
    (¬¬ ActualRootExistsAt m w → ActualRootExistsAt m w)

/-- `ActualRootExistsAt` over `WholeRosterNotTrapped`; difference: population
and stability of root existence. No background. -/
def rootExistsOverWholeRoster {W B : Type} (m : Profile W B) (w : W) : ComparisonSpec where
  stronger := ActualRootExistsAt m w
  weaker := WholeRosterNotTrapped m w
  delta := InhabitedWithStableRoot m w

/-- Exact factorization: an actual root exists iff the nonempty actual roster
is not a trap, the roster is inhabited and root existence is stable, for every
profile and world. -/
def RootExistsOverWholeRosterExact : Prop :=
  ∀ {W B : Type} (m : Profile W B) (w : W),
    ActualRootExistsAt m w ↔ WholeRosterNotTrapped m w ∧ InhabitedWithStableRoot m w

/-- Constructive reading of whole-roster nontrapping: for every profile and
world, the nonempty actual roster is not a trap iff, when the actual roster is
inhabited, it is not the case that no actual root exists. -/
def WholeRosterIsInhabitedRootNotAbsent : Prop :=
  ∀ {W B : Type} (m : Profile W B) (w : W),
    WholeRosterNotTrapped m w ↔
      (InhabitedConcreteAt m.ontic m.concrete w → ¬¬ ActualRootExistsAt m w)

end TruthCore.Causality.RootSupplyInterface
