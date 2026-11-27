module

public import TruthCore.Modal.PrussPowerPremises

/-! A necessary giver supplies a contingent recipient in every world,
while withholding every actual contingent recipient in the alternative.
Analyst formulation with attribution deferred. -/

@[expose] public section

namespace TruthCore.Modal.ActualRecipientReplacement

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Modal.ModalGrounding (NoContingentConcreteIn)
open TruthCore.Modal.PrussPowerPremises
open TruthCore.Modal.PrussPowerPremises.Model

def giving (v : Bool) (y x : Bg) : Prop :=
  givesCHere v y x ∨ givesDThere v y x

def frame : CausalityFrame Bool Bg Unit Bool :=
  gFrame uni replEx giving

/-- One stipulated holder exercises giving in both worlds. The power
assignment admits only outcomes at which it gives something. -/
def Boundary : Prop :=
  NecessaryAt frame.history.ontic false .g ∧ GivenExists frame ∧
  (∀ v, ∃ x, ContingentAt frame.history.ontic v x ∧ GivesTo frame v .g x) ∧
  ActualAbsenceByWithholding frame (positivePower giving) allC false ∧
  (∀ v, ¬ NoContingentConcreteIn frame allC v)

end TruthCore.Modal.ActualRecipientReplacement
