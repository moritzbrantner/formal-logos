module

public import TruthCore.Causality.FixedContentDoxasticVeracity

@[expose] public section
namespace TruthCore.Results.Causality.FixedContentDoxasticVeracity

open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1 (Veracity)
open TruthCore.Causality.DivineVeracity1410 (GodAssentAccurate)
open TruthCore.Causality.DivineVeracityContent1410 (Attitudes)
open TruthCore.Causality.DoxasticVeracity
open TruthCore.Causality.FixedContentDoxasticVeracity
open TruthCore.Logic.ReflectiveCoherence (Semantics)
open TruthCore.Logic.Doxastic
open TruthCore.Modal

theorem accurateFromFixedContent (σ : Signature) (V : Veracity σ) {W Content : Type}
    (c : Context σ.Being W) (S : Semantics W Content) (report : Content → Prop)
    (A : Attitudes σ Content)
    (calibrated : FixedAssentCalibration σ V c S report A)
    (access : DivineActualAccess σ c) : GodAssentAccurate σ V := by
  intro g god attributes p assent
  obtain ⟨k, contentAssent, names, aligned⟩ := calibrated.1 g god attributes p assent
  have believed := calibrated.2 g god attributes k contentAssent
  exact names ▸ aligned (believed c.actual (access g god attributes))

open TruthCore.Causality.DivineVeracityContent1410.Control (σ a selective)
open TruthCore.Causality.FixedContentDoxasticVeracity.Control
  (semantics pointed veracity always alwaysAssents)

private theorem positiveCalibration :
    FixedAssentCalibration σ (veracity True) (pointed false) semantics (fun _ => True) selective := by
  constructor
  · intro g _ _ p assent
    exact ⟨a, rfl, assent.symm, fun _ => trivial⟩
  · intro g _ _ k hk w hw
    change k = a at hk
    exact hk.symm ▸ hw.symm ▸ (rfl : semantics.trueAt false a)

private theorem omissionCalibration :
    FixedAssentCalibration σ (veracity False) (pointed true) semantics (fun _ => False) selective := by
  constructor
  · intro g _ _ p assent
    exact ⟨a, rfl, assent.symm, Bool.noConfusion⟩
  · intro g _ _ k hk w hw
    change k = a at hk
    exact hk.symm ▸ hw.symm ▸ (rfl : semantics.trueAt false a)

private theorem invariantTruth (w : Bool) : semantics.trueAt w always := by
  cases w <;> rfl

private theorem invariantCalibration :
    FixedAssentCalibration σ (veracity True) (pointed true) semantics (fun _ => True) alwaysAssents := by
  constructor
  · intro g _ _ p assent
    exact ⟨always, rfl, assent.symm, fun _ => trivial⟩
  · intro g _ _ k hk w _
    change k = always at hk
    exact hk.symm ▸ invariantTruth w

theorem controls : Control.Certificate := by
  have access : DivineActualAccess σ (pointed false) := fun _ _ _ => rfl
  have kd45 (g : σ.Being) : FrameSatisfies .KD45 ((pointed true).belief g) :=
    fixedKD45 _ ⟨false, rfl⟩
  have noAccess : ¬ DivineActualAccess σ (pointed true) :=
    fun h => Bool.noConfusion (h true rfl trivial)
  refine ⟨⟨positiveCalibration, access, ?_, rfl, rfl, Bool.noConfusion⟩,
    ⟨omissionCalibration, kd45, noAccess, fun h => h true rfl trivial False rfl⟩,
    ⟨invariantCalibration, kd45, noAccess, ?_, rfl, invariantTruth⟩⟩
  · exact accurateFromFixedContent σ _ _ semantics _ selective positiveCalibration access
  · intro g _ _ p assent
    exact assent.symm ▸ True.intro

end TruthCore.Results.Causality.FixedContentDoxasticVeracity
