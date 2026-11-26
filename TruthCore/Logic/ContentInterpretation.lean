module

public import TruthCore.Isabelle.AFP.GoedelGod
public import TruthCore.Logic.CorrectionCriterion
public import TruthCore.Logic.InformationInvariance

@[expose] public section

namespace TruthCore.Logic.ContentInterpretation

open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Logic.CorrectionCriterion (AdmitsCriterion FiberInvariant)

/-- Interpret an already individuated content as a world predicate. The
interpretation may identify extensions of distinct contents. -/
abbrev Interpretation (World Content : Type) := Content → MProp World

/-- Agreement at every accessible world licenses substitution under the shared
box and diamond at this origin. It need not give global extension equality. -/
theorem modalSubstitution {W C : Type} (I : Interpretation W C)
    (F : TruthCore.Modal.Frame W) (w : W) (a b : C)
    (h : Box F (fun v => I a v ↔ I b v) w) :
    (Box F (I a) w ↔ Box F (I b) w) ∧ (Dia F (I a) w ↔ Dia F (I b) w) := by
  refine ⟨⟨fun ha v hv => (h v hv).mp (ha v hv),
    fun hb v hv => (h v hv).mpr (hb v hv)⟩, ?_⟩
  exact ⟨fun ⟨v, hv, ha⟩ => ⟨v, hv, (h v hv).mp ha⟩,
    fun ⟨v, hv, hb⟩ => ⟨v, hv, (h v hv).mpr hb⟩⟩

/-- A judgment permits substitution of identical extensions exactly when it
admits a criterion on extensions. Fix the other arguments to apply this to
one slot of an essence or grounding judgment. -/
theorem extensionCriterion {W C : Type} (I : Interpretation W C) (J : C → Prop) :
    AdmitsCriterion I J ↔ FiberInvariant I J :=
  TruthCore.Logic.InformationInvariance.factor_iff I J

end TruthCore.Logic.ContentInterpretation
