module

public import TruthCore.Causality.DoxasticVeracity

@[expose] public section
namespace TruthCore.Results.Causality.DoxasticVeracity

open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1 (Veracity)
open TruthCore.Causality.DivineVeracity1410 (GodAssentAccurate)
open TruthCore.Causality.DoxasticVeracity
open TruthCore.Logic.Doxastic

theorem accurateFromActualAccess (σ : Signature) (V : Veracity σ) {W : Type}
    (c : Context σ.Being W) (represented : AssentRepresented σ V c)
    (access : DivineActualAccess σ c) : GodAssentAccurate σ V := by
  intro g god attributes p assent
  obtain ⟨content, actualTruth, believed⟩ := represented g god attributes p assent
  exact actualTruth.mp (believed c.actual (access g god attributes))

theorem actualAccessOmission : ActualAccessOmission := by
  let σ := TruthCore.Causality.NamingVeracityBatch1.Control.sig True True id
  let V := TruthCore.Causality.NamingVeracityBatch1.Control.veracity
    True True id (fun _ => False) (fun _ => True) (fun _ => False)
  refine ⟨σ, V, biased Bool, ?_, biasedKD45, ?_, ?_⟩
  · intro g _ _ p _
    refine ⟨fun w => w = true ∨ p, ⟨?_, Or.inr⟩, fun _ hv => Or.inl hv⟩
    intro h
    exact h.elim Bool.noConfusion id
  · intro h
    exact Bool.noConfusion (h true rfl trivial)
  · intro h
    exact h true rfl trivial False trivial

end TruthCore.Results.Causality.DoxasticVeracity
