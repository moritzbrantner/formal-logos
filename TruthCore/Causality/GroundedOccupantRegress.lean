module

public import TruthCore.Causality.ConcreteExistentialSupply
public import TruthCore.Causality.FiniteRestriction
public import TruthCore.Causality.WorldSourceRegress
public import TruthCore.Ontology.NaturalismConsequences

/-! Occupant naturalism and actual concrete existential grounding at one world.
The ground of a located concretum is supplied by an open coverage premise.
Occupation, physical interaction and constitution alone supply no such edge. -/

@[expose] public section

namespace TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.FiniteBranching (successorPredecessor)
open TruthCore.Causality.NecessaryConcreteUnderived (witnessProfile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.WorldSourceRegress (AnchoredRegress)
open TruthCore.Ontology.Naturalism (ConcreteNaturalism)
open TruthCore.Ontology.Spatiotemporal (Frame Located)

variable {W B : Type}

/-- No nonempty finite return path in the selected world's actual concrete
grounding graph. -/
def ActualConcreteGroundingAcyclicAt (m : Profile W B) (w : W) : Prop :=
  (graph m w).NoCycles

/-- Every actual concrete occupant of this frame has some actual concrete
existential ground at the selected world. The ground itself may be unlocated. -/
def LocatedActualConcreteGroundedAt (m : Profile W B) (w : W) (F : Frame B) : Prop :=
  ∀ x, ActualConcrete m w x → Located F x → ∃ y, ActualConcreteGround m w y x

/-- An infinite chain of distinct actual concrete grounds starting at the
selected recipient. Its indices are link positions. -/
def AnchoredConcreteGroundingRegress (m : Profile W B) (w : W)
    (x : {x // ActualConcrete m w x}) : Prop :=
  AnchoredRegress (graph m w) x

/-- The denial of an injective grounding regress at the selected recipient. -/
def NoAnchoredConcreteGroundingRegress (m : Profile W B) (w : W)
    (x : {x // ActualConcrete m w x}) : Prop :=
  ¬ AnchoredConcreteGroundingRegress m w x

/-- A finite path from the selected recipient upstream to an unlocated actual
concrete root in the selected grounding relation. The path can have length zero
if the recipient itself is an unlocated root. -/
def UnlocatedRootPath (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x}) : Prop :=
  ∃ s : {x // ActualConcrete m w x},
    FiniteCausalPath (graph m w).edge x s ∧
      ActualRoot m w s.val ∧ ¬ Located F s.val

/-- Source path or injective regress for the same recipient. The two
possibilities can coexist. -/
def UnlocatedRootOrRegress (m : Profile W B) (w : W) (F : Frame B)
    (x : {x // ActualConcrete m w x}) : Prop :=
  UnlocatedRootPath m w F x ∨ AnchoredConcreteGroundingRegress m w x

/-! ## Two interpretations of existential grounding with the same location criterion -/

/-- Every object of the interpretation occupies the supplied sole region.
The relation, parthood and whole parameters play no role in either control. -/
def allLocatedFrame (whole : B) : Frame B where
  Region := Unit
  locatedAt := fun _ _ => True
  related := fun _ _ => False
  partOf := fun _ _ => False
  whole := whole

/-- Reuse one uniform successor rule for all actual concreta. Causes are
empty, so the control never relies on interpreting grounds as efficient causes. -/
def successorProfile : Profile Unit Nat where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  concrete := fun _ => True -- The entire selected carrier is actual concrete.
  grounds := fun _ => successorPredecessor

/-- The all-located successor interpretation meets occupant N2 and coverage
and has an acyclic injective regress starting at 0. A uniform rule for the
edges is compatible with an infinite number of distinct ground bearers. -/
def SuccessorControl : Prop :=
  ConcreteNaturalism successorProfile.ontic successorProfile.concrete (Located (allLocatedFrame 0)) () ∧
  LocatedActualConcreteGroundedAt successorProfile () (allLocatedFrame 0) ∧
  ActualConcreteGroundingAcyclicAt successorProfile () ∧
  AnchoredConcreteGroundingRegress successorProfile () ⟨0, trivial, trivial⟩

/-- Read the existing two-bearer grounding profile at false as a located
fundamental field (false) and a distinct located mode (true). The sole mode has
a ground, but the field is a root and falsifies coverage. Occupant N2 and
acyclicity hold, with no regress at the mode. This is a formal rival
interpretation, independent of any theory of which physical fields exist. -/
def FundamentalFieldControl : Prop :=
  ConcreteNaturalism witnessProfile.ontic witnessProfile.concrete
    (Located (allLocatedFrame false)) false ∧
  ActualConcreteGroundingAcyclicAt witnessProfile false ∧
  ActualConcreteGround witnessProfile false false true ∧
  ActualRoot witnessProfile false false ∧
  NoAnchoredConcreteGroundingRegress witnessProfile false ⟨true, trivial, Or.inr rfl⟩ ∧
  ¬ LocatedActualConcreteGroundedAt witnessProfile false (allLocatedFrame false)

end TruthCore.Causality.GroundedOccupantRegress
