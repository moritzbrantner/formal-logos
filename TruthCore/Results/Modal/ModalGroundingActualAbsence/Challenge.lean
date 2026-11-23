import TruthCore.Modal.ModalGrounding

/-! Pruss's own possibility premise (#1887, after the semantic challenge): the
Aristotelian-modality route with the possibility that every *actual*
contingent concretum is absent ("others in their stead" allowed), not the
global possibility that no contingent concretum exists. No Euclidean premise.
Its projection onto the stage-one node, and its certificate of laws and models.
Analyst reconstruction; attribution deferred. Excluded middle enters only as
the explicit premise `TruthCore.Logic.ExcludedMiddle`. -/

namespace TruthCore.Results.Modal.ModalGroundingActualAbsence
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.ModalGrounding.Model
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Causality.FirstMoverNecessity.Model (noCause noPrior)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)
open TruthCore.Causality.SubtractionArgument (EachConcreteCouldFailAt ConcretePresence)
open TruthCore.Modern.Hume.Conceivability (StrongBridge)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

/-- Argument 1, Pruss's route with his own possibility premise. A concrete `x`
is contingent at `w`, so not every actual contingent concretum is absent at
`w`; P4′ gives an accessible world where all are absent. Grounding (P1′) gives
a being `y` existing at `w` with a power for that absence; initiator presence
(P2′) gives an accessible world `v` where it obtains and `y` exists; `y` is
concrete (P3′). Were `y` absent at some world accessible from `w`, it would be
an actual contingent concretum, hence absent at `v`: contradiction. Excluded
middle gives `y`'s existence at every accessible world. No Euclidean premise. -/
theorem prussActualAbsenceNecessaryPowerHolder {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hGround : ActualAbsenceGrounded F PowerFor concrete w)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hConcrete : ActualAbsencePowerHoldersConcrete F PowerFor concrete w)
    (hPoss : PossiblyNoActualContingentConcrete F concrete w)
    (hSome : SomeContingentConcreteAt F concrete w) :
    NecessaryConcreteActualAbsencePowerAt F PowerFor concrete w := by
  sorry

/-- Argument 2, projection onto the stage-one node: forget the power. An
assembly. -/
theorem prussActualAbsenceNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : NecessaryConcreteActualAbsencePowerAt F PowerFor concrete w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  sorry

/-! ## Laws and models -/

macro "ma_unfold" : tactic => `(tactic|
  simp only [NoActualContingentConcreteIn, ActualAbsenceGrounded, ActualAbsenceInitiatorPresent,
    ActualAbsencePowerHoldersConcrete, PossiblyNoActualContingentConcrete,
    NecessaryConcreteActualAbsencePowerAt, NoContingentConcreteIn, PossiblyNoContingentConcrete,
    SomeContingentConcreteAt, AristotelianGroundingFor, InitiatorPresentFor,
    PowerHoldersConcreteFor, EachConcreteCouldFailAt, ConcretePresence, groundProfile, Dia,
    TruthCore.Modal.Euclidean, NecessaryAt, ContingentAt, theistFrame, creatureFrame,
    emptyFrame, swappedFrame, vanCleveFrame, nonEuclideanSibling, frameOn, allConcrete,
    onlyFalseConcrete, noGrounds, univ, theistEx, creatureOnly, swapped, nothing, gCausesC,
    gPriorC, powerBy, noPowerFor, comboEx, ptAccess, ptAllEx, noCause, noPrior])

theorem actualAbsenceControls : ActualAbsenceControls := by
  sorry

end TruthCore.Results.Modal.ModalGroundingActualAbsence
