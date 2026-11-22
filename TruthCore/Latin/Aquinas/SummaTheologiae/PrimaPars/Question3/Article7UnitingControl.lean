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
both distinct from the composite 3, and 2 is a third, distinct uniter. It has
two respects (`Bool`): esse is `true`, and `false` is a further respect of
being distinct from esse. Under the secunda-via gloss, `EfficientlyCausesIn c x r`
says that `c` is an efficient cause of `x`'s being `r`; the uniter 2 efficiently
causes 3 only in respect `false`, so it is not an efficient cause of 3's esse.
The fixture also satisfies the genus-species link from efficient causing in a
respect to `CausesIn` in that same respect, so it does not merely keep two
unlinked causal primitives apart at esse: the uniter causes 3 (efficiently, and
so also in the open `CausesIn` sense) in respect `false`, and nothing causes 3 in
respect esse. The relations are primitive interpretations, not a model of any
historical philosopher's positive account of constitution.
-/

/-- Public so that the `Fin 4` literals of the fixture below (and of its
certificate proof) elaborate with it. Core's fallback `NeZero (3 + 1)` uses
`propext`, which would break this zero-axiom result (as in
`Greek.Plato.ParticipationGrounding`; see docs/notes/lean-module-system.md). -/
instance : NeZero 4 where
  out h := Nat.noConfusion h

def properFixtureComposite (x : Fin 4) : Prop := x = 3
def properFixtureComponent (a x : Fin 4) : Prop :=
  x = 3 ∧ (a = 0 ∨ a = 1)
def properFixtureUnites (c a b x : Fin 4) : Prop :=
  c = 2 ∧ properFixtureComponent a x ∧ properFixtureComponent b x ∧ a ≠ b
/-- The esse respect of the fixture; `false` is the other, non-esse respect. -/
def properFixtureEsse : Bool := true
def properFixtureEfficient (c x : Fin 4) (r : Bool) : Prop :=
  c = 2 ∧ x = 3 ∧ r = false
def properFixtureCauses (c x : Fin 4) (r : Bool) : Prop :=
  c = 2 ∧ x = 3 ∧ r = false

/-- Even a populated composite with two genuinely proper constituents and a
third, numerically distinct, efficient uniter does not get a cause of its esse
from the other four premises. The respects differ: the uniter efficiently
causes the composite only in a non-esse respect, efficient causing in a respect
implies `CausesIn` in that same respect, and nothing causes the composite in
respect esse. This isolates the uniting-to-esse bridge from mereological
degeneracy and from a collapse of the efficient respect into esse. A finite
interpretation is not an assertion of metaphysical possibility or explanatory
adequacy. -/
def ProperPartBridgeControl : Prop :=
  (∃ x, properFixtureComposite x) ∧
  (∀ a x, properFixtureComponent a x → a ≠ x) ∧
  CompositeHasTwoDistinctComponentsReading properFixtureComposite properFixtureComponent ∧
  DiverseUnitedOnlyThroughUnitingCauseReading properFixtureComponent properFixtureUnites ∧
  UnitingCauseIsEfficientCauseReading properFixtureUnites properFixtureEfficient ∧
  NothingIsEfficientCauseOfItselfReading properFixtureEfficient ∧
  (∃ c a b x, properFixtureUnites c a b x) ∧
  properFixtureEsse ≠ false ∧
  (∀ c x r, properFixtureEfficient c x r → properFixtureCauses c x r) ∧
  (∃ c r, properFixtureEfficient c 3 r) ∧
  (¬ ∃ c, properFixtureCauses c 3 properFixtureEsse) ∧
  ¬ UnitingCauseCausesBeingReading properFixtureUnites properFixtureCauses properFixtureEsse ∧
  ¬ CompositeHasAUnitingCauseReading properFixtureComposite properFixtureCauses
    properFixtureEsse

/-- For each of the five premises, some interpretation satisfies the other four
while that premise and `CompositeHasAUnitingCauseReading` both fail. In the
first, the existing fifth-proof reading (a component other than itself) still
holds. A sixth interpretation satisfies all five with a composite present. A
seventh (`ProperPartBridgeControl`) strengthens the omission of the
uniter-to-esse premise: two proper components, a third non-self efficient uniter
acting only in a non-esse respect, and efficient causing included in `CausesIn`
in the same respect, yet no cause of the composite's esse. -/
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
