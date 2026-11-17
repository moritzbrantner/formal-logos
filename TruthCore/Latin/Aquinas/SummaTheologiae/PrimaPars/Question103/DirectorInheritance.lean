module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government

/-! Analyst scope restriction of same-end inheritance. No new causal relation
or account of intentionality is introduced: the existing MovesIn and Directs
parameters remain open. Selection says some distinct actual mover preserves
direction to this same target and end, when such movers exist. It does not say
which mover, that every mover qualifies, or that it understands the end. -/

@[expose] public section
namespace TruthCore.Latin.Aquinas.SummaTheologiae.DirectorInheritance

/-- Restrict to natural-body targets and choose one direction-preserving actual
predecessor from the nonempty set of distinct movers. This is an OPEN policy,
not a definition making arbitrary enabling causes intentional instruments. -/
def SameEndMoverSelection {Being Respect End : Type}
    (NaturalBody : Being → Prop) (MovesIn : Being → Being → Respect → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ f x e, NaturalBody x → Directs f x e →
    (∃ g r, MovesIn g f r ∧ g ≠ f) →
    ∃ g r, MovesIn g f r ∧ g ≠ f ∧ Directs g x e

end TruthCore.Latin.Aquinas.SummaTheologiae.DirectorInheritance
