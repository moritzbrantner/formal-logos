module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-!
Formal omission and compatibility controls for the five premises that derive
`CompositeHasAUnitingCauseReading` (result COMPOSITE-UNITING-CAUSE-FROM-UNION).
Each control is a stipulated finite interpretation of the shared vocabulary. It
shows what the encoded premises do and do not entail. It does not claim that any
interpretation is metaphysically possible, nor that a rival account is refuted.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting.Control
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-
The earlier two-component models allow the whole to count as one of its own
components. This stronger fixture is deliberately nondegenerate: 0 and 1 are
both distinct from the composite 3, and 2 is a third, distinct uniter. The
uniter efficiently acts on 3 in the (only) respect, but never causes its esse.
The relations are primitive interpretations, not a model of any historical
philosopher's positive account of constitution.
-/
def properFixtureComposite (x : Fin 4) : Prop := x = 3
def properFixtureComponent (a x : Fin 4) : Prop :=
  x = 3 ∧ (a = 0 ∨ a = 1)
def properFixtureUnites (c a b x : Fin 4) : Prop :=
  c = 2 ∧ properFixtureComponent a x ∧ properFixtureComponent b x ∧ a ≠ b
def properFixtureEfficient (c x : Fin 4) (_ : Unit) : Prop :=
  c = 2 ∧ x = 3
def properFixtureEsseCause (_ _ : Fin 4) (_ : Unit) : Prop := False

/-- Even a populated composite with two genuinely proper constituents and a
third, numerically distinct, efficient uniter does not get a cause of its esse
from the other four premises. This isolates the uniting-to-esse bridge from
mereological degeneracy. A finite interpretation is not an assertion of
metaphysical possibility or explanatory adequacy. -/
def ProperPartBridgeControl : Prop :=
  (∃ x, properFixtureComposite x) ∧
  (∀ a x, properFixtureComponent a x → a ≠ x) ∧
  CompositeHasTwoDistinctComponentsReading properFixtureComposite properFixtureComponent ∧
  DiverseUnitedOnlyThroughUnitingCauseReading properFixtureComponent properFixtureUnites ∧
  UnitingCauseIsEfficientCauseReading properFixtureUnites properFixtureEfficient ∧
  NothingIsEfficientCauseOfItselfReading properFixtureEfficient ∧
  (∃ c a b x, properFixtureUnites c a b x) ∧
  ¬ UnitingCauseCausesBeingReading properFixtureUnites properFixtureEsseCause () ∧
  ¬ CompositeHasAUnitingCauseReading properFixtureComposite properFixtureEsseCause ()

/-- For each of the five premises, some interpretation satisfies the other four
while that premise and `CompositeHasAUnitingCauseReading` both fail. In the
first, the existing fifth-proof reading (a component other than itself) still
holds. A sixth interpretation satisfies all five with a composite present. -/
def Certificate : Prop :=
  -- 1. Without two distinct components: one component other than the composite.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    ¬ CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    CompositeHasComponentOtherThanItselfReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 2. Without the uniting-cause principle: two components, no uniter.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    ¬ DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 3. Without uniter-is-efficient: the whole unites itself and causes its own
  -- being, but not efficiently.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    ¬ UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 4. Without uniter-causes-being: a distinct efficient uniter that causes
  -- nothing's being.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    ¬ UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 5. Without no-efficient-self-cause: the whole efficiently unites itself.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    ¬ NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 6. All five premises together, with a composite present.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ∃ x, Composite x) ∧
  -- 7. Proper components and a distinct efficient uniter still do not
  -- entail that this uniter causes the composite's esse.
  ProperPartBridgeControl

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting.Control
