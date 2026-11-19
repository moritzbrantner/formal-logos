module

public import TruthCore.Modal.TemporalHistory

/-!
# The causality frame: one set of primitives for the causality family

Owner decision 2026-11-19 (#1784, `docs/decisions/2026-11-19-01-parameter-sense-tags-and-shared-frames.md`).
Modules of the causality family state their propositions over binders of their
own (`CausesIn`, `DependsForBeing`, `PriorSimply`, a `History`, a
`BeingGiving`). Two modules that mean the same relation therefore quantify over
unrelated parameters, and nothing composes their statements without restating
them. `CausalityFrame` bundles those shared primitives once. New modules of the
family take a frame as input. Older modules get adapters
(`TruthCore.Causality.FrameAdapters`) that instantiate their statements from a
frame by definitional unfolding, without a rewrite.

**Every field is a primitive.** Its meaning is stated in its doc comment and
in the definition record named there. The structure itself adds nothing: **no
relation between fields is assumed**. In particular it does not assume that
causing being (`CausesIn … esse`) is giving being at a moment (`GivesAt`), that
dependence for being is simple priority, or that moving is causing a
perfection. Each such passage remains an explicit, open bridge premise of the
argument that uses it, for example
`ConcurrentActualization.CausesOfBeingConcur` for `CausesIn` to `GivesAt`.
Senses remain distinct: each field is one sense's relation, recorded by a
parameter-level sense tag on that sense
(`senses[].lean_parameters` with `declaration` this structure and `parameter`
the field). A field with no matching sense record is untagged, which means
its sense is unknown.

It does not replace `TermSenseForks.CauseFrame` or `PriorityFrame`. Those
bundle the competing senses of one term, so that a route can be read by
cases over them. This frame bundles one selected relation per role across
terms, so that propositions from different modules use the same symbols.
Applicability of every field to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.Frame

open TruthCore.Modal.TemporalHistory (History)

/-- The shared primitives of the causality family over worlds `W`, beings `B`,
moments `T` and respects `R`. No field is constrained, and no field is related
to another. -/
structure CausalityFrame (W B T R : Type) where
  /-- The temporal history: world-relative existence (`history.ontic`), presence
  of a being at a moment of a world (`history.IsAt v x t`), and the designated
  present moment (`history.now`) (`TruthCore.Modal.TemporalHistory`). Presence is
  not existence at some time, and nothing causal follows from it. -/
  history : History W B T
  /-- `GivesAt v c x t`: in world `v`, `c` exercises causation of `x`'s being at
  moment `t` (definition 158301bc, the primitive of `SustainingCausation.BeingGiving`;
  on its strict esse-giving reading). The moment is on the effect side; it does
  not put the agent in time. Not identified with `CausesIn … esse`. -/
  GivesAt : W → B → B → T → Prop
  /-- `CausesIn c x r`: `c` is a cause of `x`'s being `r`, as fire is of the heat
  of hot things (DEF-CAUSE-OF-PERFECTION, CAUSE_2); at `r = esse` it is cause of
  being (CAUSING_AN_EFFECT_3). Tenseless. Not moving and not efficient causing. -/
  CausesIn : B → B → R → Prop
  /-- `MovesIn y x r`: `y` reduces `x` from potency to act in respect `r`, read at
  one time (DEF-MOTION-AS-REDUCTION, CAUSE_1). Not restricted to local motion or
  to bodies. Not causing a perfection. -/
  MovesIn : B → B → R → Prop
  /-- `DependsForBeing x y`: `x` would not be if `y` were not, in the sense of an
  effect's relation to its agent cause (DEF-DEPENDS-FOR-BEING,
  DEPENDENCE_FOR_BEING_VERSUS_STRICT_GROUND_1). Not temporal succession, not
  material implication, not necessitation. -/
  DependsForBeing : B → B → Prop
  /-- `PriorSimply y x`: `y` is simply (not temporally) prior to `x`
  (DEF-SIMPLE-PRIORITY, PRIOR_1). Not priority in time (PRIOR_2) or in substance
  (PRIOR_3). -/
  PriorSimply : B → B → Prop
  /-- The distinguished respect of being: `InAct x esse` says that `x` has being
  (DEF-ESSE). -/
  esse : R

end TruthCore.Causality.Frame
