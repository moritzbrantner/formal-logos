module

public import TruthCore.Causality.DoxasticVeracity
public import TruthCore.Causality.DivineVeracityContent1410

/-! The content interpretation, report and individuated assent are independently
supplied. The calibration concerns their agreement with the two belief readings
on each actual legacy assent, using a single content witness. -/

@[expose] public section
namespace TruthCore.Causality.FixedContentDoxasticVeracity

open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1 (Veracity)
open TruthCore.Causality.DivineVeracity1410 (GodAssentAccurate)
open TruthCore.Causality.DivineVeracityContent1410 (Attitudes)
open TruthCore.Causality.DoxasticVeracity
open TruthCore.Logic.ReflectiveCoherence (Semantics)
open TruthCore.Logic.SelfApplication (Disquotes)
open TruthCore.Logic.Doxastic
open TruthCore.Modal

/-- OPEN calibration. The report and its world truth conditions are fixed before
matching the assents. The same content is assented to, reports the legacy
proposition, its truth at actuality implies that report, and it is believed across
alternatives. -/
def FixedAssentCalibration (σ : Signature) (V : Veracity σ) {W Content : Type}
    (c : Context σ.Being W) (S : Semantics W Content) (report : Content → Prop)
    (A : Attitudes σ Content) : Prop :=
  (∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Believes g p →
    ∃ k, A.Assents g k ∧ report k = p ∧ Disquotes (S.trueAt c.actual) k (report k)) ∧
  (∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ k, A.Assents g k →
    Believes c g (fun w => S.trueAt w k) c.actual)

namespace Control

open TruthCore.Causality.DivineVeracityContent1410.Control (σ a selective)

/-- The existing tagged truth table with a constructive negation certificate.
This keeps the finite controls within the zero-axiom verifier policy. -/
def semantics : Semantics Bool (Bool × Bool × Bool) where
  trueAt w k := (if w then k.2.1 else k.1) = true
  neg k := (!k.1, !k.2.1, k.2.2)
  neg_true_iff := by
    intro w k
    obtain ⟨atFalse, atTrue, tag⟩ := k
    cases w <;> cases atFalse <;> cases atTrue <;> cases tag <;> decide

def pointed (actual : Bool) : Context σ.Being Bool :=
  ⟨fun _ => fixed (· = false), actual⟩

def veracity (report : Prop) : Veracity σ :=
  TruthCore.Causality.NamingVeracityBatch1.Control.veracity
    True True id (fun _ => False) (· = report) (fun _ => False)

abbrev always : Bool × Bool × Bool := (true, true, false)

def alwaysAssents : Attitudes σ (Bool × Bool × Bool) where
  Asserts _ _ := False
  Assents _ k := k = always

/-- Same independently interpreted contingent content in the first two
profiles. The third keeps the omission frame and selects an invariant content. -/
def Certificate : Prop :=
  (FixedAssentCalibration σ (veracity True) (pointed false) semantics (fun _ => True) selective ∧
    DivineActualAccess σ (pointed false) ∧ GodAssentAccurate σ (veracity True) ∧
    (veracity True).Believes true True ∧ semantics.trueAt false a ∧ ¬ semantics.trueAt true a) ∧
  (FixedAssentCalibration σ (veracity False) (pointed true) semantics (fun _ => False) selective ∧
    (∀ g, FrameSatisfies .KD45 ((pointed true).belief g)) ∧
    ¬ DivineActualAccess σ (pointed true) ∧ ¬ GodAssentAccurate σ (veracity False)) ∧
  (FixedAssentCalibration σ (veracity True) (pointed true) semantics (fun _ => True) alwaysAssents ∧
    (∀ g, FrameSatisfies .KD45 ((pointed true).belief g)) ∧
    ¬ DivineActualAccess σ (pointed true) ∧ GodAssentAccurate σ (veracity True) ∧
    (veracity True).Believes true True ∧ ∀ w, semantics.trueAt w always)

end Control
end TruthCore.Causality.FixedContentDoxasticVeracity
