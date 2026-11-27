import TruthCore.Causality.DoxasticVeracity

namespace TruthCore.Results.Causality.DoxasticVeracity

open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1 (Veracity)
open TruthCore.Causality.DivineVeracity1410 (GodAssentAccurate)
open TruthCore.Causality.DoxasticVeracity
open TruthCore.Logic.Doxastic

theorem accurateFromActualAccess (σ : Signature) (V : Veracity σ) {W : Type}
    (c : Context σ.Being W) (represented : AssentRepresented σ V c)
    (access : DivineActualAccess σ c) : GodAssentAccurate σ V := by
  sorry

theorem actualAccessOmission : ActualAccessOmission := by
  sorry

end TruthCore.Results.Causality.DoxasticVeracity
