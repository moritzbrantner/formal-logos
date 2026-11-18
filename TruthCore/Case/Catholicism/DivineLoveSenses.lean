module

public import TruthCore.Case.Catholicism.DivineLoveBridge

/-!
Sense carriers for the #1732 love/willing disambiguations, the q.20 a.2 ad 3
ordered-love reading of the causal-willing step (`OrderedExistenceWillingWeak`),
and its unattributed strong (exclusive) analyst variant
(`OrderedExistenceWilling`).

The registered `DivineLoveBridge` theorems take `WillsGoodFor` and `Loves` as
parameters. The structures below give each sense its own distinct Lean
constant (a structure field). The fields are primitive: nothing here defines
what they mean; their meaning, exclusions and open bridges are stated in the
definition records. In particular `ThinLove.Loves` is not defined as willing
good, and no relation between any two carriers is asserted. The registered
parametric theorems are tied to these carriers by instantiated corollaries in
`TruthCore.Results.Case.Catholicism.DivineLoveSenseRoute`. Analyst formulation,
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
as ordered to y (to a rational creature or to God). It neither includes nor
excludes willing that good to x as recipient. Primitive field. -/
structure OrderedWilling (Being : Sort u) (Respect : Sort v) where
  WillsAsOrderedTo : Being → Being → Being → Respect → Prop

/-- Thin non-passional q.20 love: `Loves g x`. Primitive field; neither
friendship nor the perfect relational love of the hiddenness challenge. -/
structure ThinLove (Being : Sort u) where
  Loves : Being → Being → Prop

/-- Strong (exclusive) ordered-love variant: an unattributed analyst
strengthening of q.20 a.2 ad 3, not the ad 3 reading. For every GOD_4 g with
will and every distinct, non-rational x in act in esse whose esse g causes, g
wills x's being in esse as ordered to some y that is rational or is g itself,
**and** does not will that good to x as recipient. The denial is not in ad 3;
its own motivation is the contrast of love of desire (amor concupiscentiae,
willing a thing's good for another) with love of friendship (willing good to
the beloved itself), read as exclusive for non-rational things. The q.20 a.2
body ("God loves all existing things") counts against it. On a distinct
non-rational caused actual effect it contradicts the recipient-directed
`DivineLoveBridge.CausalExistenceWilling`; it says nothing about rational
creatures. -/
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

/-- The q.20 a.2 ad 3 ordered-love reading (weak version): for every GOD_4 g
with will and every distinct, non-rational x in act in esse whose esse g
causes, g wills x's being in esse as ordered to some y that is rational or is
g itself. It neither asserts nor denies that g also wills that good to x as
recipient, so it is compatible with `DivineLoveBridge.CausalExistenceWilling`
(`WeakOrderedCompatibilityWitness`). Implied by `OrderedExistenceWilling`. -/
def OrderedExistenceWillingWeak {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill Rational : Being → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (O : OrderedWilling Being Respect) (esse : Respect) : Prop :=
  ∀ g x, IsGod g → HasWill g → x ≠ g → ¬ Rational x → InAct x esse →
    CausesIn g x esse →
      ∃ y, (Rational y ∨ y = g) ∧ O.WillsAsOrderedTo g x y esse

/-- No GOD_4 with will causes the esse of a distinct, non-rational being in act
in esse. The joint consequence of the strong ordered variant and the
recipient-directed causal-willing bridge at one `RecipientGoodWilling`. -/
def NoNonRationalCausedEffect {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill Rational : Being → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ g x, IsGod g → HasWill g → x ≠ g → ¬ Rational x → InAct x esse →
    ¬ CausesIn g x esse

namespace Sample

/-- `true` is the willing GOD_4; `false` is a distinct, non-rational being in act
that `true` causes; only `true` is rational. -/
def isGod (b : Bool) : Prop := b = true
def rational (b : Bool) : Prop := b = true
def inAct (_ : Bool) (_ : Unit) : Prop := True
def causes (g x : Bool) (_ : Unit) : Prop := g = true ∧ x = false
def willing : RecipientGoodWilling Bool Unit := ⟨fun g _ _ => g = true⟩
def ordered : OrderedWilling Bool Unit := ⟨fun g x y _ => g = true ∧ x = false ∧ y = true⟩

end Sample

open Sample in
/-- Compatibility of the weak ordered reading with the recipient-directed
bridge at one `RecipientGoodWilling`: in the two-being sample the weak
reading, `CausalExistenceWilling` at `willing.WillsGoodFor`, and a distinct,
non-rational, caused actual effect all hold, and the strong variant fails.
A finite structural interpretation, not a model of divine willing. -/
def WeakOrderedCompatibilityWitness : Prop :=
  OrderedExistenceWillingWeak isGod isGod rational inAct causes ordered () ∧
  DivineLoveBridge.CausalExistenceWilling isGod isGod inAct causes
    willing.WillsGoodFor () ∧
  isGod true ∧ false ≠ true ∧ ¬ rational false ∧ inAct false () ∧
  causes true false () ∧
  ¬ OrderedExistenceWilling isGod isGod rational inAct causes willing ordered ()

end TruthCore.Case.Catholicism.DivineLoveSenses
