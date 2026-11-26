module

public import TruthCore.Case.Catholicism.FirstSourceIdentification

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.FirstSourceIdentification

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.FirstSourceIdentification
open TruthCore.Causality.TermSenseForks

theorem summaFromCommonMaximum (σ : Signature) {R : Type}
    (God : σ.Being → Prop) (InAct : σ.Being → R → Prop)
    (MoreIn : R → σ.Being → σ.Being → Prop) (esse : R)
    (hNames : SummaGodIsMaximum God InAct MoreIn esse)
    (hClassical : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hUnique : AtMostOneMaximeEns InAct MoreIn esse)
    (hExists : GodExists σ.IsGod) : SummaGodIsClassicalGod σ God := by
  intro x hx
  obtain ⟨g, hg⟩ := hExists
  have hEqual := hUnique x g (hNames x hx) (hClassical g hg)
  exact hEqual.symm ▸ hg

theorem usageFromCommonMaximum (σ : Signature) {R Name : Type}
    (Calls : Name → σ.Being → Prop) (godName : Name) (InAct : σ.Being → R → Prop)
    (MoreIn : R → σ.Being → σ.Being → Prop) (esse : R)
    (hNames : CalledGodIsMaximum Calls godName InAct MoreIn esse)
    (hClassical : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hUnique : AtMostOneMaximeEns InAct MoreIn esse)
    (hExists : GodExists σ.IsGod) : CalledGodIsClassicalGod σ Calls godName := by
  intro x hx
  obtain ⟨g, hg⟩ := hExists
  have hEqual := hUnique x g (hNames x hx) (hClassical g hg)
  exact hEqual.symm ▸ hg

end TruthCore.Results.Case.Catholicism.FirstSourceIdentification
