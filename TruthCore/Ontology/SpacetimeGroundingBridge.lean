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
a physical existence condition and grounding of esse are not synonymous.
In particular `Located` is only SPATIOTEMPORAL_2 (dimensive occupation).
The frame's `whole` need not actually exist, be concrete or be contingent:
these are separate premises. Nor must a relational or derivative account accept
the occupant-to-whole bridge.

The output concerns an unlocated necessary underived concretum, not GOD_4,
modal/world-independent space, or Boethian eternity. A later consumer must
preserve the precise *same* root witness when ascribing a God predicate.
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

/-- OPEN ontological bridge: every distinct actual concrete occupant is
grounded for its being by this very spacetime whole, via the profile's SELECTED
existential-grounding relation at the same world. Location, earlier-than,
geometric cone order and efficient causation do not imply this. -/
def OccupantsDependOnWholeAt {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ∀ x, x ≠ F.whole → ActualConcrete m w x →
    Located F x → m.grounds w F.whole x

/-- ONE actual necessary underived concrete witness does not dimensively
occupy a region. This does not exclude presence by power, causal relations,
or relations to temporal creatures. -/
def NecessaryUnderivedUnlocatedAt {W B : Type}
    (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ∃ x, UnderivedConcreteAt m w x ∧ ¬ Located F x

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

end TruthCore.Ontology.SpacetimeGroundingBridge
