module

public import TruthCore.Causality.NarGrafts
public import TruthCore.Causality.ConcreteExistentialSupply
public import TruthCore.Causality.ConcreteRootAccess
public import TruthCore.Causality.SourceForest
public import TruthCore.Causality.GodMaximalCausal

@[expose] public section

namespace TruthCore.Causality.ActualAncestralSource
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualRoot)
open TruthCore.Causality.CogitoNecessaryConcrete (GroundAncestor)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.SourceForest (RootedAtUniqueSource)
open TruthCore.Causality.NarDerivation.Model (chainG chainGrounds)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.PrussPowerPremises.Model (allC)

/-- One root reaches all nodes of the actual concrete grounding graph at this
world. The graph uses the profile's grounds relation at both actual endpoints. -/
def CommonActualGroundingAncestry {W B : Type} (m : Profile W B) (w : W) : Prop :=
  RootedAtUniqueSource (graph m w)

/-- A causal interpretation of the naming predicate: each being so named is a
finite grounding ancestor of every actual concretum at the chosen world.
The empty path covers the being itself. This conditional supplies no God. -/
def GodReachesActualConcreta {W B : Type} (m : Profile W B) (w : W)
    (IsGod : B → Prop) : Prop :=
  ∀ g, IsGod g → ∀ x, ActualConcrete m w x → GroundAncestor m w g x

/-- Extend the existing mediated-optimum interpretation on exactly its grounding
profile. The profile's other causal fields and the chosen world stay fixed. -/
def MediatedControl : Prop :=
  NarGrafts.Model.MediatedOptimum ∧
    RootedAtUniqueSource (graph (groundProfile chainG allC chainGrounds) false)

end TruthCore.Causality.ActualAncestralSource
