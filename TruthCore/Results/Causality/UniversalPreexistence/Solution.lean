module

public import TruthCore.Causality.UniversalPreexistence
public import TruthCore.Logic.ExcludedMiddle

/-!
# Preexistence at the universal source: results

Analyst formulations, attribution deferred; no premise is established.
-/

@[expose] public section

namespace TruthCore.Results.Causality.UniversalPreexistence

open TruthCore.Causality.UniversalPreexistence
open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (CausesAllInGenus PerfectionsOfEffectPreexistInCauseReading
    MaximumInGenusCausesAllInGenusReading ActualityOnlyInsofarAsBeingReading)
open TruthCore.Case.Catholicism
  (UniversalCauseTransfersPerfections GodIsMaximalInBeing GodIsPerfect)
open TruthCore.Causality.CausalMapsBatch1 (CauseOfBeingHasWhatItGives)

/-- Universal-source preexistence from universal-scope transfer and
universal-source possession: a universal cause of `x`'s being causes each of
`x`'s perfections (`b26c10a0`), and a universal source has every perfection it
causes in a thing whose being it causes. No nonuniversal transfer is used. -/
theorem universalPreexistenceOfTransferAndPossession {W B T R : Type}
    (F : GradesFrame W B T R)
    (hTransfer : UniversalCauseTransfersPerfections F.InAct F.CausesIn F.esse)
    (hHas : UniversalSourceHasWhatItGives F) :
    UniversalSourcePreexistence F := by
  intro c hc x r hne hBeing hx
  exact hHas c hc x r hne hBeing (hTransfer c hc x r hne hBeing hx)

/-- Strength order: q.4 a.2 preexistence entails its restriction to universal
sources. -/
theorem universalPreexistenceOfPreexistence {W B T R : Type} (F : GradesFrame W B T R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) :
    UniversalSourcePreexistence F :=
  fun c _ x r _ hBeing hx => hPre c x r hBeing hx

/-- Strength order: cause-of-being possession entails its restriction to
universal sources. -/
theorem universalPossessionOfCauseOfBeingPossession {W B T R : Type}
    (F : GradesFrame W B T R)
    (hHas : CauseOfBeingHasWhatItGives F.CausesIn F.InAct F.esse) :
    UniversalSourceHasWhatItGives F :=
  fun c _ x r _ hBeing hr => hHas c x r hBeing hr

/-- Sibling of `godIsPerfect` with universal-source preexistence in place of
q.4 a.2 preexistence, which that proof applies only at a maximum in being, a
universal cause of being by the genus principle. -/
theorem godIsPerfectOfUniversalPreexistence {W B T R : Type} (F : GradesFrame W B T R)
    (IsGod : B → Prop)
    (hMaximal : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading F.InAct F.MoreIn F.CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hUniversal : UniversalSourcePreexistence F)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GodIsPerfect IsGod F.InAct := by
  intro g hg x r hx
  cases hEM (x = g) with
  | inl hSame => exact hSame ▸ hx
  | inr hOther =>
    have hAll : CausesAllInGenus F.InAct F.CausesIn F.esse g :=
      hGenus F.esse g (hMaximal g hg)
    exact hUniversal g hAll x r hOther (hAll x hOther (hBeing x r hx)) hx

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The impersonal-source interpretation, checked by decision. The larger
instance budget only lets instance search assemble the `Decidable` instances of
the nested quantifiers. -/
theorem controls : Control.Controls := by
  dsimp [Control.Controls, UniversalSourceHasWhatItGives, UniversalSourcePreexistence,
    CausesAllInGenus, UniversalCauseTransfersPerfections,
    PerfectionsOfEffectPreexistInCauseReading,
    TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection,
    ActualityOnlyInsofarAsBeingReading, GodIsPerfect, TruthCore.Case.Catholicism.IsPerfect,
    Control.grades, Control.act, TruthCore.Causality.CartesianAdequacy.gradesOf,
    Control.causes, Control.formal, Control.virtual, Control.inclusive, Control.more]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end TruthCore.Results.Causality.UniversalPreexistence
