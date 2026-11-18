module

/-!
Sense carriers for the #1732 love/willing disambiguations, and the q.20 a.2
ad 3 ordered-love reading of the causal-willing step as its own proposition.

The registered `DivineLoveBridge` theorems take `WillsGoodFor` and `Loves` as
parameters. The structures below give each sense its own distinct Lean
constant (a structure field), so the senses are distinct Lean types for the
sense index. The fields are primitive: nothing here defines what they mean;
their meaning, exclusions and open bridges are stated in the definition
records. In particular `ThinLove.Loves` is not defined as willing good, and
no relation between any two carriers is asserted. Analyst formulation,
attribution deferred; see docs/notes/divine-love-goodness-bridge.md.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.DivineLoveSenses

universe u v

/-- Recipient-directed willing (`velle bonum alicui`): `WillsGoodFor g x r`,
g wills to x itself the good x has in respect r. Primitive field. -/
structure RecipientGoodWilling (Being : Sort u) (Respect : Sort v) where
  WillsGoodFor : Being → Being → Respect → Prop

/-- Ordered willing: `WillsAsOrderedTo g x y r`, g wills x's being in respect r
as ordered to y (to a rational creature or to God), without thereby willing it
to x as recipient. Primitive field. -/
structure OrderedWilling (Being : Sort u) (Respect : Sort v) where
  WillsAsOrderedTo : Being → Being → Being → Respect → Prop

/-- Thin non-passional q.20 love: `Loves g x`. Primitive field; neither
friendship nor the perfect relational love of the hiddenness challenge. -/
structure ThinLove (Being : Sort u) where
  Loves : Being → Being → Prop

/-- q.20 a.2 ad 3 ordered-love reading, a sibling of the recipient-directed
`DivineLoveBridge.CausalExistenceWilling`. For every GOD_4 g with will and
every distinct, non-rational x in act in esse whose esse g causes, g wills x's
being in esse as ordered to some y that is rational or is g itself, and does
not will that good to x as recipient. On a distinct non-rational actual effect
it contradicts the recipient-directed bridge; it says nothing about rational
creatures. Not used by any registered argument. -/
def OrderedExistenceWilling {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill Rational : Being → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (W : RecipientGoodWilling Being Respect) (O : OrderedWilling Being Respect)
    (esse : Respect) : Prop :=
  ∀ g x, IsGod g → HasWill g → x ≠ g → ¬ Rational x → InAct x esse →
    CausesIn g x esse →
      (∃ y, (Rational y ∨ y = g) ∧ O.WillsAsOrderedTo g x y esse) ∧
      ¬ W.WillsGoodFor g x esse

end TruthCore.Case.Catholicism.DivineLoveSenses
