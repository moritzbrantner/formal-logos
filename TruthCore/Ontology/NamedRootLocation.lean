module

public import TruthCore.Causality.NecessaryClassicalGodRootControl
public import TruthCore.Ontology.SpacetimeGroundingBridge

/-! Analyst formulation under the same three spatial premises as the
spacetime grounding bridge. The endpoint keeps its whole classical root body
and adds dimensive nonoccupation in one supplied frame. -/

@[expose] public section
namespace TruthCore.Ontology.NamedRootLocation

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryClassicalGodRoot (NecessaryClassicalGodRootAt)
open TruthCore.Causality.SameSourceWitness (ClassicalGodRootWitnessAt UnderivedConcreteAt)
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Ontology.SpacetimeGroundingBridge
open TruthCore.Ontology.Spatiotemporal (Frame Located)

/-- The single witness of the classical root body also fails to occupy a
region of the supplied frame. Its necessary existence and selected-world
roothood are both retained. -/
def NecessaryClassicalGodRootUnlocatedAt {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W) (F : Frame σ.Being)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop) : Prop :=
  ∃ g, ClassicalGodRootWitnessAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
    Composite MatterForm Infinite Eternal HasIntellect HasWill g ∧ ¬ Located F g

namespace Separation
open TruthCore.Causality.NecessaryClassicalGodRootControl
open TruthCore.Causality.RootPositiveIntellectWillControl
  (profile prior component composite matterForm intellect will)

/-- The classical-root control's actual profile is preserved. At the other
accessible world the supporter is absent and the existing recipient grounds
the existing source. These are assignments of the selected grounding relation. -/
def model : Profile Bool TransferRole :=
  let priorModel := TruthCore.Causality.RootPositiveIntellectWillControl.model
  { priorModel with
    ontic := { priorModel.ontic with ExistsAt := fun w x => w = false ∨ x ≠ .supporter }
    grounds := fun w a b => if w then a = .recipient ∧ b = .source
      else priorModel.grounds w a b }

/-- The supporter and the recipient occupy the one region. The actual whole
is the supporter. The frame models occupation alone. -/
def frame : Frame TransferRole where
  Region := Unit
  locatedAt := fun x _ => x = .supporter ∨ x = .recipient
  related := fun _ _ => False
  partOf := fun _ _ => False
  whole := .supporter

/-- Joint satisfaction of the four named-root premises, with a distinct
located actual occupant grounded by the whole and a concrete existing ground
of the same named source at another accessible world. This finite assignment
separates the location consequence from all-world underivedness. -/
def Control : Prop :=
  NecessaryClassicalGodRootAt signature model false profile transferAct potency
    (transferMore true) prior component composite matterForm infinite eternal intellect will ∧
  ActualConcreteWholeAt model false frame ∧ ContingentWholeAt model false frame ∧
  OccupantsDependOnWholeAt model false frame ∧
  TransferRole.recipient ≠ frame.whole ∧ ActualConcrete model false .recipient ∧
  Located frame .recipient ∧ model.grounds false frame.whole .recipient ∧
  ClassicalGodRootWitnessAt signature model false profile transferAct potency
    (transferMore true) prior component composite matterForm infinite eternal intellect will
    .source ∧
  ¬ Located frame .source ∧ model.ontic.frame.access false true ∧
  TransferRole.recipient ≠ TransferRole.source ∧
  ActualConcrete model true .recipient ∧ model.ontic.ExistsAt true .source ∧
  model.grounds true .recipient .source ∧ ¬ UnderivedConcreteAt model false .source

end Separation
end TruthCore.Ontology.NamedRootLocation
