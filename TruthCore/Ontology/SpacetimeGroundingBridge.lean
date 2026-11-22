module

public import TruthCore.Causality.SameSourceWitness
public import TruthCore.Ontology.Spatiotemporal

/-!
# Spacetime occupation and existential grounding: a conditional root connection

Analyst reconstruction; not a claim about real spacetime, Leibniz, Clarke or
relativity. This reuses the single world-indexed existential-grounding edge
`Profile.grounds`, the actual concrete predicate and the *same candidate*
in `UnderivedConcreteAt`. No new causal or grounding relation is introduced.

The substantive open bridge says that a **distinct, actual concrete occupant**
is existentially grounded by the **same actual spacetime whole**. Occupying a
geometric region, a timelike ordering, a physically permitted causal signal,
a physical existence condition and existential grounding are not synonymous.
"Existential grounding" here is only the selected `Profile.grounds` relation;
it is not the act of being (DEF-ESSE) or Aquinas' cause of esse, per the
`existence-esse-support` disambiguation.
In particular `Located` is only SPATIOTEMPORAL_2 (dimensive occupation).
The frame's `whole` need not actually exist, be concrete or be contingent:
these are separate premises. Nor must a relational or derivative account accept
the occupant-to-whole bridge.

The output concerns an unlocated necessary underived concretum, not GOD_4,
modal/world-independent space, or Boethian eternity. A later consumer must
preserve the precise *same* root witness when ascribing a God predicate.
"Unlocated" is relative to the one supplied frame `F`; `Located` is not
world-indexed, and nothing is said about other frames. The reusable entry
point is the pointwise `selectedUnlocated`: any bearer that is
`UnderivedConcreteAt m w` in the same `m`, `w` and `F` is unlocated, so a GOD_4
consumer needs only its own bearer underived there, without rethreading
`derive`.

The occupant restriction does the work. `UnrestrictedWholePriorityAt` (the
whole grounds every other actual concretum, the unrestricted whole-priority
form) is jointly inconsistent with the other three premises by the same proof
(`unrestrictedInconsistent`), so positive warrant for the located bridge cannot
simply be borrowed from unrestricted whole-priority views. `JointModel` records
that the four premises of `derive` are jointly satisfiable with a located
occupant distinct from the whole.
-/

@[expose] public section
namespace TruthCore.Ontology.SpacetimeGroundingBridge

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteUnderived
  (NecessaryConcreteUnderivedAt witnessProfile)
open TruthCore.Causality.SameSourceWitness (UnderivedConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Ontology.Spatiotemporal (Frame Located)

/-- This exact spacetime whole, not an arbitrary geometric region, is a
concrete existent at the selected world. -/
def ActualConcreteWholeAt {W B : Type} (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ActualConcrete m w F.whole

/-- The same actual spacetime whole is absent from some accessible world.
A temporal first instant and a possible physical rearrangement are not built in. -/
def ContingentWholeAt {W B : Type} (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ContingentAt m.ontic w F.whole

/-- OPEN ontological bridge: every distinct actual concrete occupant of `F`
stands in the profile's SELECTED existential-grounding relation `m.grounds` to
this very spacetime whole at the same world. This is that relation only, not
the act of being (DEF-ESSE) or a cause of esse. Location, earlier-than,
geometric cone order and efficient causation do not imply this. -/
def OccupantsDependOnWholeAt {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ∀ x, x ≠ F.whole → ActualConcrete m w x →
    Located F x → m.grounds w F.whole x

/-- ONE actual necessary underived concrete witness does not dimensively
occupy a region of the supplied frame `F` (the spacetime whose whole is named
in the premises). `Located` is not world-indexed, and nothing is said about
other frames. This does not exclude presence by power, causal relations,
or relations to temporal creatures. -/
def NecessaryUnderivedUnlocatedAt {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ∃ x, UnderivedConcreteAt m w x ∧ ¬ Located F x

/-- Unrestricted whole priority: the whole grounds EVERY other actual
concretum, located or not, in the selected `m.grounds` relation. Recorded only
as a control: with the other three premises of `derive` it is inconsistent. -/
def UnrestrictedWholePriorityAt {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ∀ x, x ≠ F.whole → ActualConcrete m w x → m.grounds w F.whole x

/-- Nonempty omission model: every candidate occupies the sole region. Its
whole (true) is contingent, while its necessary root (false) actually grounds
the whole. The reverse grounding edge required by the bridge is absent. -/
def sampleFrame : Frame Bool where
  Region := Unit
  locatedAt := fun _ _ => True
  related := fun _ _ => False
  partOf := fun _ _ => False
  whole := true

/-- On the *same* ontology profile there is a concrete actual contingent whole,
a necessary underived concrete root, a real existential-grounding edge, and
every candidate is located. Omitting the occupant-grounding bridge makes the
new conclusion fail. This is a logical countermodel, not a physical worldview. -/
def OmissionControl : Prop :=
  ActualConcreteWholeAt witnessProfile false sampleFrame ∧
  ContingentWholeAt witnessProfile false sampleFrame ∧
  NecessaryConcreteUnderivedAt witnessProfile false ∧
  witnessProfile.grounds false false true ∧
  ¬ OccupantsDependOnWholeAt witnessProfile false sampleFrame ∧
  ¬ NecessaryUnderivedUnlocatedAt witnessProfile false sampleFrame

/-- Candidates of the joint-satisfiability model: the necessary root, the
contingent spacetime whole and one located occupant distinct from the whole. -/
inductive JointBeing where
  | root
  | whole
  | occupant
  deriving DecidableEq

/-- Two worlds; the root exists at both, the whole and the occupant only at
the selected world `false`. The only grounding edge is whole-to-occupant at
`false`. -/
def jointProfile : Profile Bool JointBeing where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun w b => b = .root ∨ w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests joint satisfiability of the grounding/modal/location premises, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun w a b => w = false ∧ a = .whole ∧ b = .occupant

/-- One region, occupied by the whole and the occupant but not by the root. -/
def jointFrame : Frame JointBeing where
  Region := Unit
  locatedAt := fun x _ => x ≠ .root
  related := fun _ _ => False
  partOf := fun _ _ => False
  whole := .whole

/-- One joint model of all four premises of `derive`, with an actual concrete
occupant distinct from the whole that is located and grounded by the whole.
Structural surrogate only (`related` and `partOf` are empty); no claim that it
is an actual or physically possible spacetime. -/
def JointModel : Prop :=
  NecessaryConcreteUnderivedAt jointProfile false ∧
  ActualConcreteWholeAt jointProfile false jointFrame ∧
  ContingentWholeAt jointProfile false jointFrame ∧
  OccupantsDependOnWholeAt jointProfile false jointFrame ∧
  ∃ x, x ≠ jointFrame.whole ∧ ActualConcrete jointProfile false x ∧
    Located jointFrame x ∧ jointProfile.grounds false jointFrame.whole x

end TruthCore.Ontology.SpacetimeGroundingBridge
