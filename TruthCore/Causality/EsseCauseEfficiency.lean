module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
public import TruthCore.Latin.Aquinas.DeEnte.ExtrinsicSource

/-!
# Efficiency of causes of esse (#1633)

The shared q.3 a.4 vocabulary has one cause-of-being relation, `CausesIn c x
esse` (DEF-CAUSE-OF-PERFECTION), whose type does not fix the *mode* of
causing: an efficient (agent) cause, a formal or constitutive principle, an
exemplar or a final cause would all be written the same way. Statements that
say "efficiently caused" while binding to `CausesIn` therefore carry
efficiency only in prose. This module adds efficiency as a separate typed
relation, so that the step from "some other actual being causes x's esse" to
"some other actual being *efficiently* causes x's esse" is an explicit premise
that can fail.

* `EfficiencyProfile` extends the q.3 a.4 `Profile` (same beings, principles,
  respects, `InAct`, `CausesIn`, `essenceOf`, `esseOf`, `esse`) with one
  primitive relation `EfficientlyCausesEsse y x`: y is an efficient (agent)
  cause of x's esse, x's being proceeding from y as from an agent. It is
  tenseless, like `CausesIn`: originating and sustaining causes are both
  admitted, and no present or simultaneous causing is built in. It is **not**
  the secunda via's `EfficientlyCausesIn` (DEF-EFFICIENT-CAUSING), which is
  read here and now; relating the two is an open bridge not used here.
  It is a primitive: no definition from more basic notions is given, and no
  structural law (irreflexivity, transitivity, asymmetry, or implication of
  `CausesIn`) is assumed.
* `HasExternalEfficientEsseCause q x` (sense `CAUSING_AN_EFFECT_6`): some y
  other than x is in act as to being, causes x's esse (`CausesIn`) and does so
  efficiently. It strengthens the mode-unspecified q.3 a.4
  `HasExternalEsseCause` (`CAUSING_AN_EFFECT_2`) by one conjunct.
* `DistinctActualEsseCauseIsEfficient` is the OPEN bridge: every actual cause,
  other than x, of the esse of an actual x whose esse differs from its
  essence is an efficient cause of it. `CausingAnothersEsseIsEfficient` is its
  unrestricted version (any cause of another's esse is efficient).

Nothing here asserts either bridge. `EsseCauseEfficiencyControls` shows that
the mode-unspecified conclusions of De ente (`DistinctEsseHasOtherActualCause`)
and of q.3 a.4 (`DistinctEsseRequiresExternalCauseReading`) hold without the
efficient one in a finite interpretation with a non-efficient cause of
being. That interpretation is a structural surrogate for a formal,
constitutive or otherwise non-agent cause: `EfficientlyCausesEsse` is
unconstrained, so it shows logical independence under these predicates, not
that a non-efficient cause of esse is possible.
-/

@[expose] public section

namespace TruthCore.Causality.EsseCauseEfficiency

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Latin.Aquinas.DeEnte (DistinctEsseHasOtherActualCause)

variable {B P R : Type}

/-- The q.3 a.4 profile with a primitive, tenseless efficiency relation on
causes of esse. `EfficientlyCausesEsse y x`: y is an efficient (agent) cause
of x's esse. Primitive: its meaning, examples, exclusions and open
obligations are in the definition record, not in a Lean body. -/
structure EfficiencyProfile (Being Principle Respect : Type) extends
    Profile Being Principle Respect where
  EfficientlyCausesEsse : Being → Being → Prop

/-- `CAUSING_AN_EFFECT_6`: some being other than x, in act as to being,
causes x's esse and is an efficient cause of it. -/
def HasExternalEfficientEsseCause (q : EfficiencyProfile B P R) (x : B) : Prop :=
  ∃ y, y ≠ x ∧ q.InAct y q.esse ∧ q.CausesIn y x q.esse ∧ q.EfficientlyCausesEsse y x

/-- Every actual being whose esse differs from its essence has an external
efficient cause of its esse in act. The efficient reading of ST I q.3 a.4's
"habeat esse causatum ab alio"; analyst formulation. -/
def DistinctEsseRequiresExternalEfficientCause (q : EfficiencyProfile B P R) : Prop :=
  ∀ x, DistinctEsseAt q.toProfile x → HasExternalEfficientEsseCause q x

/-- OPEN bridge from a mode-unspecified to an efficient cause of being: for an
actual x whose esse differs from its essence, every y other than x that is in
act as to being and causes x's esse is an efficient cause of x's esse. -/
def DistinctActualEsseCauseIsEfficient (q : EfficiencyProfile B P R) : Prop :=
  ∀ x, DistinctEsseAt q.toProfile x → ∀ y, y ≠ x → q.InAct y q.esse →
    q.CausesIn y x q.esse → q.EfficientlyCausesEsse y x

/-- OPEN, unrestricted version of the bridge: whatever causes the esse of a
thing other than itself is an efficient cause of that esse. -/
def CausingAnothersEsseIsEfficient (q : EfficiencyProfile B P R) : Prop :=
  ∀ y x, y ≠ x → q.CausesIn y x q.esse → q.EfficientlyCausesEsse y x

/-! ## Finite controls

Existence claims about interpretations on `Bool` (two beings, two principles,
one respect) in which `false` actually exists with esse distinct from its
essence. Each type certifies only the listed conjuncts; the descriptions of
the particular witnesses below are of the interpretations built in the proofs,
not part of the types. -/

/-- Non-efficient cause: some interpretation satisfies the q.3 a.4 dichotomy,
no essential self-sufficiency, no self-causation, the actuality of causes of
being, the q.3 a.4 mode-unspecified conclusion and the De ente conclusion,
while both bridges and the efficient conclusion fail. (Witness in the proof:
`true`, in act, causes `false`'s esse, and nothing is an efficient cause of
anything.) -/
def NonEfficientCauseControl : Prop :=
  ∃ q : EfficiencyProfile Bool Bool Unit,
    DistinctEsseAt q.toProfile false ∧
    DistinctEsseCauseDichotomyReading q.toProfile ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading q.toProfile ∧
    (∀ x, ¬ q.CausesIn x x q.esse) ∧
    (∀ c x, q.CausesIn c x q.esse → q.InAct c q.esse) ∧
    DistinctEsseHasOtherActualCause q.toProfile ∧
    DistinctEsseRequiresExternalCauseReading q.toProfile ∧
    ¬ DistinctActualEsseCauseIsEfficient q ∧
    ¬ CausingAnothersEsseIsEfficient q ∧
    ¬ DistinctEsseRequiresExternalEfficientCause q

/-- Restricted bridge without the unrestricted one: some interpretation with an
actual distinct-esse being satisfies the restricted bridge and falsifies the
unrestricted one. (Witness in the proof: `true` efficiently causes `false`'s
esse; `false` causes `true`'s esse without being an efficient cause of it;
`true`'s esse is its essence, so the restricted bridge does not apply to it.) -/
def RestrictedBridgeOnlyControl : Prop :=
  ∃ q : EfficiencyProfile Bool Bool Unit,
    DistinctEsseAt q.toProfile false ∧
    DistinctActualEsseCauseIsEfficient q ∧
    ¬ CausingAnothersEsseIsEfficient q

/-- Nonvacuity: some interpretation with an actual distinct-esse being satisfies
every input of the two efficient-cause derivations, both bridges and the
efficient conclusion. -/
def EfficientCauseNonvacuity : Prop :=
  ∃ q : EfficiencyProfile Bool Bool Unit,
    DistinctEsseAt q.toProfile false ∧
    DistinctEsseCauseDichotomyReading q.toProfile ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading q.toProfile ∧
    DistinctEsseHasOtherActualCause q.toProfile ∧
    CausingAnothersEsseIsEfficient q ∧
    DistinctActualEsseCauseIsEfficient q ∧
    DistinctEsseRequiresExternalEfficientCause q

/-- The three controls. -/
def EsseCauseEfficiencyControls : Prop :=
  NonEfficientCauseControl ∧ RestrictedBridgeOnlyControl ∧ EfficientCauseNonvacuity

end TruthCore.Causality.EsseCauseEfficiency
