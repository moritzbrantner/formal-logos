module

public import TruthCore.Causality.FirstMoverNecessity
public import TruthCore.Causality.TimeSymmetricGiving
public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-! Limitation of esse, reception in a principle, and dependence on a concrete giver.
The extent of each predicate is supplied independently. All arguments use the selected
respect of esse, and actual grounding is evaluated at one supplied world. -/

@[expose] public section

namespace TruthCore.Causality.FiniteEsseDependence

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)

/-- Actual receipt of a bearer's act of being requires that the bearer is in act
in the selected respect. An aptitude to receive does not meet this premise. -/
def ReceiptImpliesActuality {B P R : Type} (Received : B → P → Prop)
    (InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ x z, Received x z → InAct x esse

/-- A formally limited actual concretum has a distinct cause of its esse, and that
very cause is an actual concrete ground of the bearer at the selected world. -/
def LimitedEsseHasGroundingGiverAt {W B R : Type} (m : Profile W B) (w : W)
    (Limited : B → Prop) (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ x, ActualConcrete m w x → Limited x →
    ∃ g, g ≠ x ∧ CausesIn g x esse ∧ ActualConcreteGround m w g x

end TruthCore.Causality.FiniteEsseDependence
