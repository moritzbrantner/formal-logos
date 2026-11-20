module

public import TruthCore.Causality.SelectedAncestry

/-!
# A literal thinker-only P/¬P fork (#1743/#1791)

Source-free, selected-world reconstruction. `G` is the *existing* actual
concrete grounding relation. For this **mediate-grounding** reading only,
`P(x)` says that a **distinct** bearer of an occurring thought precedes `x`
along a nonempty finite `G` path. This is not a claim that ordinary grounding
is existential sustenance, nor that a directly sustaining thinker exists.

`Thinks` is not world-indexed: its interpretation at the selected actual world
requires the separate Cogito existence bridge. `Acc` below restricts descent
to distinct thinking predecessors, allowing unrelated nonthinking cycles.
Neither selected-relation rootness nor accessibility-relative necessity implies
absolute underivedness, unique source identity, or God-existence.
-/

@[expose] public section

namespace TruthCore.Causality.ThinkingRootFork

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)

variable {W B Episode : Type}

/-- A bearer of some occurring thought, without yet asserting actuality. -/
def Thinks (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (x : B) : Prop :=
  ∃ e, Occurs e ∧ Bears x e

/-- One distinct thinker lies on a nonempty actual concrete ground path to `x`.
The path witnesses the *selected* mediate-grounding sense of sustenance. -/
def ThinkerPredecessor (m : Profile W B) (w : W) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (c x : B) : Prop :=
  c ≠ x ∧ Thinks Occurs Bears c ∧
    Relation.TransGen (ActualConcreteGround m w) c x

/-- The positive horn of the literal fork at `x`. -/
def P (m : Profile W B) (w : W) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (x : B) : Prop :=
  ∃ c, ThinkerPredecessor m w Occurs Bears c x

/-- Every *grounded thinking* member of the selected actual cone (one with at
least one incoming actual concrete `G` edge) has `P`: some distinct thinker
precedes it along a nonempty finite `G` path. Its immediate parents need not
think, and no intermediate concrete ground is required to think. -/
def NoFreshThinkerInCone (m : Profile W B) (w : W) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (selected : B) : Prop :=
  ∀ x, Cone m w selected x → Thinks Occurs Bears x →
    (∃ y, ActualConcreteGround m w y x) → P m w Occurs Bears x

/-- The anti-brute premise applies only to contingent *thinkers* in the cone;
an ungrounded nonthinking contingent ancestor is permitted. -/
def ConeContingentThinkersGrounded (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (selected : B) : Prop :=
  ∀ x, Cone m w selected x → Thinks Occurs Bears x →
    ContingentAt m.ontic w x → ∃ y, ActualConcreteGround m w y x

/-- For each possible Cogito bearer, thinker-only mediate ancestry is
accessible. This is not `Acc` of the full concrete grounding relation. -/
def ThinkingBearerPredecessorAccessible (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) : Prop :=
  ∀ b e, Occurs e → Bears b e →
    Acc (ThinkerPredecessor m w Occurs Bears) b

/-- Scoped no-emergence for the occurring-thought bearer chosen by Cogito. -/
def ThinkingBearerConeNoFresh (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) : Prop :=
  ∀ b e, Occurs e → Bears b e → NoFreshThinkerInCone m w Occurs Bears b

/-- Scoped modal anti-brute condition for actual *thinking* cone members. -/
def ThinkingBearerConeContingentGrounded (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) : Prop :=
  ∀ b e, Occurs e → Bears b e →
    ConeContingentThinkersGrounded m w Occurs Bears b

/-- An actual thinking ground-root of the selected being, necessary *de re*
relative to the supplied world's accessibility relation. The witness `n`
does not change when the proof upgrades rootness to necessity. -/
def NecessaryThinkingRootOf (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (selected : B) : Prop :=
  ∃ n, Thinks Occurs Bears n ∧ GroundAncestor m w n selected ∧
    ActualRoot m w n ∧ NecessaryAt m.ontic w n

/-- Existing Cogito premises pick the thinker `selected`; the remaining
hypotheses are explicit local requirements for each possible chosen bearer. -/
def NecessaryThinkingRootOfThought (m : Profile W B) (w : W)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) : Prop :=
  ∃ b e, Occurs e ∧ Bears b e ∧ NecessaryThinkingRootOf m w Occurs Bears b

end TruthCore.Causality.ThinkingRootFork
