module

public import TruthCore.Causality.DivineVeracity1410
public import TruthCore.Logic.Doxastic

/-! Analyst representation of the existing divine-assent accuracy step.
The world-indexed representation and actual access are independent inputs. -/

@[expose] public section
namespace TruthCore.Causality.DoxasticVeracity

open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1 (Veracity)
open TruthCore.Causality.DivineVeracity1410 (GodAssentAccurate)
open TruthCore.Logic.Doxastic
open TruthCore.Modal

/-- OPEN: each actual divine assent is represented by a world predicate
whose actual value agrees with the assented proposition. The given profile
remains fixed across contents. Only the scope of the target is assumed. -/
def AssentRepresented (σ : Signature) (V : Veracity σ) {W : Type}
    (c : Context σ.Being W) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Believes g p →
    ∃ content : W → Prop, (content c.actual ↔ p) ∧ Believes c g content c.actual

/-- OPEN: the relevant bearer includes the actual world among the alternatives
at actuality. This one edge is weaker than global reflexivity. -/
def DivineActualAccess (σ : Signature) {W : Type} (c : Context σ.Being W) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → (c.belief g).access c.actual c.actual

/-- Structural omission: the same profile represents every assent and satisfies
KD45 for every agent, yet a classified bearer assents falsely. -/
def ActualAccessOmission : Prop :=
  ∃ (σ : Signature) (V : Veracity σ) (c : Context σ.Being Bool),
    AssentRepresented σ V c ∧ (∀ g, FrameSatisfies .KD45 (c.belief g)) ∧
      ¬ DivineActualAccess σ c ∧ ¬ GodAssentAccurate σ V

end TruthCore.Causality.DoxasticVeracity
