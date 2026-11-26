module

public import TruthCore.Modal.ModalPowerHolder
public import TruthCore.Causality.ActualOnlyEuclidean
public import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCover.Proof
public import TruthCore.Results.Modal.ModalGroundingActualAbsence.Solution

@[expose] public section

namespace TruthCore.Results.Modal.ModalPowerHolder
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.ActualOnlyEuclidean (TransitiveAt)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AccessibleSuccessor finite_omission)
open TruthCore.Modal.ModalGrounding
open TruthCore.Modal.ModalPowerHolder
open TruthCore.Modal.PrussPowerPremises

theorem jointAbsenceOfFiniteRoster {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (w : W)
    (hAccess : AccessibleSuccessor F.history.ontic.frame w)
    (hAmalgam : ActualRosterAmalgamates F concrete w)
    (hFinite : ActualRosterFinite F concrete w) :
    PossiblyNoActualContingentConcrete F concrete w := by
  obtain ⟨xs, hList⟩ := hFinite
  obtain ⟨v, hv, hAbsent⟩ := finite_omission F.history.ontic.frame
    (fun (x : ActualContingentRoster F concrete w) u => F.history.ontic.ExistsAt u x.val)
    w hAccess hAmalgam (fun x => x.property.2.2) xs
  exact ⟨v, hv, fun x hc ht => hAbsent ⟨x, hc, ht⟩ (hList ⟨x, hc, ht⟩)⟩

theorem globalAbsenceOfRosterCoverage {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (w : W)
    (hTrans : TransitiveAt F.history.ontic.frame w)
    (hJoint : PossiblyNoActualContingentConcrete F concrete w)
    (hCover : ActualRosterCoversAtAbsence F concrete w) :
    PossiblyNoContingentConcrete F concrete w := by
  obtain ⟨v, hwv, hAbsent⟩ := hJoint
  refine ⟨v, hwv, fun x hc ht => ?_⟩
  obtain ⟨e, u, hvu, hu⟩ := ht
  exact hAbsent x hc ⟨hCover v hwv hAbsent x hc ⟨e, u, hvu, hu⟩, u, hTrans v u hwv hvu, hu⟩ e

theorem differentGivingOfOneRecipient {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (w : W)
    (hInit : ActualAbsenceInitiatorPresent F PowerFor concrete w)
    (hGive : ActualAbsenceHoldersGiveSome F PowerFor concrete w)
    (hFactive : GivenExists F) :
    ActualAbsenceExerciseDiffers F PowerFor concrete w := by
  intro y hPower
  obtain ⟨x, hc, ht, hxy⟩ := hGive y hPower
  obtain ⟨v, hwv, hAbsent, hy⟩ := hInit y hPower
  exact ⟨v, hwv, hAbsent, hy, fun hSame =>
    hAbsent x hc ht (hFactive v y x ((hSame x).mp hxy))⟩

open TruthCore.Modal.ModalGrounding.Model
open TruthCore.Modal.ModalPowerHolder.Model (populatedProfiles bothPresent AllRosterPresent)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

private def withoutTrue : {v : Bool × Bool // v ≠ (false, false)} :=
  ⟨(false, true), by decide⟩

private def withoutFalse : {v : Bool × Bool // v ≠ (false, false)} :=
  ⟨(true, false), by decide⟩

private theorem bothExist (b : Bool) :
    populatedProfiles.history.ontic.ExistsAt bothPresent b := by
  change comboEx (true, true) b
  cases b <;> simp [comboEx]

private theorem noTrue : ¬ populatedProfiles.history.ontic.ExistsAt withoutTrue true := by
  change ¬ comboEx (false, true) true
  simp [comboEx]

private theorem noFalse : ¬ populatedProfiles.history.ontic.ExistsAt withoutFalse false := by
  change ¬ comboEx (true, false) false
  simp [comboEx]

private theorem eachContingent (b : Bool) :
    ContingentAt populatedProfiles.history.ontic bothPresent b := by
  refine ⟨bothExist b, ?_⟩
  cases b
  · exact ⟨withoutFalse, trivial, noFalse⟩
  · exact ⟨withoutTrue, trivial, noTrue⟩

private theorem somePresent (v : {v : Bool × Bool // v ≠ (false, false)}) :
    populatedProfiles.history.ontic.ExistsAt v true ∨
      populatedProfiles.history.ontic.ExistsAt v false := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  change comboEx (a, b) true ∨ comboEx (a, b) false
  cases a <;> cases b <;> simp_all [comboEx]

theorem controls : TruthCore.Modal.ModalPowerHolder.Model.Controls := by
  let member (b : Bool) : ActualContingentRoster populatedProfiles allConcrete bothPresent :=
    ⟨b, trivial, eachContingent b⟩
  have hFinite : ActualRosterFinite populatedProfiles allConcrete bothPresent :=
    ⟨[member true, member false], fun ⟨b, _⟩ => by cases b <;> simp [member]⟩
  have hNoJoint : ¬ PossiblyNoActualContingentConcrete populatedProfiles allConcrete bothPresent := by
    rintro ⟨v, _, h⟩
    rcases somePresent v with hp | hp
    · exact h true trivial (eachContingent true) hp
    · exact h false trivial (eachContingent false) hp
  have replaced := TruthCore.Results.Modal.ModalGroundingActualAbsence.replacementVersusJointAbsence
  refine ⟨⟨fun _ => trivial, fun _ _ _ _ _ => trivial, hFinite, fun b => bothExist b.val,
    ⟨withoutTrue, trivial, fun h => noTrue (h (member true))⟩, ?_, hNoJoint⟩,
    ⟨fun _ => trivial, fun _ _ _ _ _ => trivial, replaced.1.2.1, ?_, replaced.1.2.2⟩⟩
  · exact fun h => hNoJoint
      (jointAbsenceOfFiniteRoster populatedProfiles allConcrete bothPresent
        ⟨bothPresent, trivial⟩ h hFinite)
  · exact fun h => replaced.1.2.2
      (globalAbsenceOfRosterCoverage swappedFrame allConcrete true
        (fun _ _ _ _ => trivial) replaced.1.2.1 h)

end TruthCore.Results.Modal.ModalPowerHolder
