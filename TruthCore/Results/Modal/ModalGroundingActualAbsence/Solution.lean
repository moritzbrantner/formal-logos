module

public import TruthCore.Modal.ModalGrounding

/-! Pruss's own possibility premise (#1887, after the semantic challenge): the
Aristotelian-modality route with the possibility that every *actual*
contingent concretum is absent ("others in their stead" allowed), not the
global possibility that no contingent concretum exists. No Euclidean premise.
Its projection onto the stage-one node, and its certificate of laws and models.
Analyst reconstruction; attribution deferred. Excluded middle enters only as
the explicit premise `TruthCore.Logic.ExcludedMiddle`. -/

@[expose] public section

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
  obtain ⟨x, hxc, hx⟩ := hSome
  obtain ⟨y, hyw, hpow⟩ := hGround hPoss (fun h => h x hxc hx hx.1)
  obtain ⟨v, hwv, hpv, hyv⟩ := hInit y hpow
  have hyc := hConcrete y hpow
  refine ⟨y, hyc, hyw, fun u hwu => ?_, hpow⟩
  rcases hEM (F.history.ontic.ExistsAt u y) with h | h
  · exact h
  · exact (hpv y hyc ⟨hyw, u, hwu, h⟩ hyv).elim

/-- Argument 2, projection onto the stage-one node: forget the power. An
assembly. -/
theorem prussActualAbsenceNecessaryConcrete {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W)
    (h : NecessaryConcreteActualAbsencePowerAt F PowerFor concrete w) :
    NecessaryConcreteAt (groundProfile F concrete grounds) w := by
  obtain ⟨y, hc, he, hn, _⟩ := h
  exact ⟨y, hc, he, hn⟩

/-! ## Laws and models -/

theorem actualAbsenceLaws : ActualAbsenceLaws := by
  intro W B T R F concrete w hEuc ⟨v, hwv, hv⟩
  refine ⟨v, hwv, fun x hxc hx hxv => ?_⟩
  obtain ⟨_, u, hwu, hxu⟩ := hx
  exact hv x hxc ⟨hxv, u, hEuc w v u hwv hwu, hxu⟩

theorem Pt.forall_iff' (p : Pt → Prop) : (∀ v, p v) ↔ p .a ∧ p .b ∧ p .c :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨ha, hb, hc⟩ v => by cases v <;> assumption⟩

theorem Pt.exists_iff' (p : Pt → Prop) : (∃ v, p v) ↔ p .a ∨ p .b ∨ p .c :=
  ⟨fun ⟨v, h⟩ => by cases v <;> simp_all, fun h => by
    rcases h with h | h | h <;> exact ⟨_, h⟩⟩

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

theorem siblingNonvacuity : SiblingNonvacuity := by
  unfold SiblingNonvacuity
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  ma_unfold <;> simp [Bool.forall_bool, Pt.forall_iff']

theorem siblingOmissions : SiblingOmissions := by
  unfold SiblingOmissions
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  ma_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Prod.forall, Prod.exists]

theorem replacementVersusJointAbsence : ReplacementVersusJointAbsence := by
  unfold ReplacementVersusJointAbsence
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
  ma_unfold <;> simp [Bool.forall_bool, Bool.exists_bool, Prod.exists]

theorem conceivabilityS4Bundle : ConceivabilityS4Bundle := by
  unfold ConceivabilityS4Bundle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; simp [s4Frame, frameOn, branchingAccess]
  · intro u m v; simp [s4Frame, frameOn, branchingAccess]; intro h1 h2; cases u <;> cases m <;>
      simp_all
  · intro h
    have := h false true false (by simp [s4Frame, frameOn, branchingAccess])
      (by simp [s4Frame, frameOn, branchingAccess])
    simp [s4Frame, frameOn, branchingAccess] at this
  · rintro P (hP | hP)
    · exact ⟨false, Or.inl rfl, (hP false).2 (by simp [s4Frame, frameOn, onlyFHere])⟩
    · exact ⟨true, Or.inl rfl, (hP true).2 (by
        intro u hu
        simp [s4Frame, frameOn, branchingAccess] at hu
        simp [s4Frame, frameOn, onlyFHere, hu])⟩
  · exact Or.inr fun _ => Iff.rfl
  · exact Or.inl fun _ => Iff.rfl

theorem actualAbsenceControls : ActualAbsenceControls :=
  ⟨actualAbsenceLaws, siblingNonvacuity, siblingOmissions, replacementVersusJointAbsence,
    conceivabilityS4Bundle⟩

end TruthCore.Results.Modal.ModalGroundingActualAbsence
