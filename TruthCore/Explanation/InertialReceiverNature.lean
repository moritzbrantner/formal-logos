module

public import TruthCore.Explanation.InducerFreePersistence
public import TruthCore.Ontology.ExistenceInEssence

@[expose] public section

namespace TruthCore.Explanation.InertialReceiverNature

open TruthCore.Causality.EsseCausePriority.InertialNecessaryOrigin (ancestralFrame history)
open TruthCore.Causality.ConcurrentCessation.C3ActualWorld (originGiving)
open TruthCore.Ontology.ExistenceInEssence (NatureEntailsExistence)

/-- Candidate origin-essentialist reading for this receiver. Its origin is
fixed if it exists, including in the sustained assignment at the same onset. -/
def originIfPresent (v : Bool) : Prop :=
  history.ontic.ExistsAt v false → originGiving.GivesAt v true false 1

def essential (x : Bool) (φ : Bool → Prop) : Prop :=
  x = false ∧ φ = originIfPresent

def ReceiverNatureControl : Prop :=
  InducerFreePersistence.MatchedAssignments ∧ essential false originIfPresent ∧
  (∀ v, originIfPresent v) ∧ ¬ NatureEntailsExistence ancestralFrame essential false

end TruthCore.Explanation.InertialReceiverNature
