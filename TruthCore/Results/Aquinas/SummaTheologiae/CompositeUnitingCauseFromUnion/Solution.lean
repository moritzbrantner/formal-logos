module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

@[expose] public section

universe u v

namespace TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseFromUnion
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-- Preserve the *same* witness through composition, union, efficient action
and causation of esse. The legacy result below deliberately forgets that the
returned cause was also a uniter. No world-local presence, nonparthood or
ongoing activity follows from the stronger conditional either. -/
theorem compositeHasSameUnitingEsseCause {Being : Sort u} {Respect : Sort v}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop)
    (Unites : Being → Being → Being → Being → Prop)
    (EfficientlyCausesIn CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnite : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites)
    (hEfficient : UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn)
    (hBeing : UnitingCauseCausesBeingReading Unites CausesIn esse)
    (hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) :
    ∀ x, Composite x →
      ∃ a b c, ComponentOf a x ∧ ComponentOf b x ∧ a ≠ b ∧
        Unites c a b x ∧ c ≠ x ∧ CausesIn c x esse := by
  intro x hx
  obtain ⟨a, b, ha, hb, hab⟩ := hTwo x hx
  obtain ⟨c, hc⟩ := hUnite x a b ha hb hab
  have hne : c ≠ x := by
    intro hcx
    obtain ⟨r, hr⟩ := hEfficient c a b x hc
    rw [hcx] at hr
    exact hNoSelf x r hr
  exact ⟨a, b, c, ha, hb, hab, hc, hne, hBeing c a b x hc⟩

/-- Every composite has a cause, other than itself, of its being, derived from
five premises. A composite has two distinct components (q.11 a.1); distinct
components of one thing are united only by a uniting cause (q.3 a.7, third
proof); a uniting cause efficiently causes what it unites in some respect (q.3
a.7, third proof); a uniting cause causes the being of what it unites (q.11 a.1
with q.3 a.7); and nothing is an efficient cause of itself (q.2 a.3, second
way). The uniter causes the composite's being, and it is not the composite,
since otherwise the composite would efficiently cause itself. -/
theorem compositeHasAUnitingCause {Being : Sort u} {Respect : Sort v}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop)
    (Unites : Being → Being → Being → Being → Prop)
    (EfficientlyCausesIn CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnite : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites)
    (hEfficient : UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn)
    (hBeing : UnitingCauseCausesBeingReading Unites CausesIn esse)
    (hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) :
    CompositeHasAUnitingCauseReading Composite CausesIn esse := by
  intro x hComposite
  obtain ⟨a, b, c, ha, hb, hab, hc, hne, hEsse⟩ :=
    compositeHasSameUnitingEsseCause Composite ComponentOf Unites
      EfficientlyCausesIn CausesIn esse hTwo hUnite hEfficient hBeing hNoSelf x hComposite
  exact ⟨c, hne, hEsse⟩

end TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseFromUnion
