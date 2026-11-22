import TruthCore.Causality.CartesianAdequacy

/-! Cartesian causal adequacy compared with the case's cause-of-perfection
premises (analyst formulations, attribution deferred).

* `preexistenceOfContainment`: respect-wise containment in every cause, with the
  existing cause-of-being transfer premise, gives q.4 a.2 preexistence (PEPC).
* `containmentOfStrictComparative`: the Aristotelian strict comparative, "more
  such has the perfection" and excluded middle give respect-wise containment in
  every cause. With the previous theorem this factors the existing four-premise
  derivation `PERFECTION-PREEXISTENCE-FROM-CAUSAL-TRANSFER` through one hinge.
* `totalContainmentOfContainment`: strength order, containment in every cause
  entails containment in total causes.
* `wholeEffectContainmentOfPreexistence`, `causeOfABeingHasBeingOfContainment`:
  strength orders to the whole-effect sibling and to the esse instance.
* `containmentAndPreexistenceIndependent`: respect-wise total-cause containment
  and PEPC are independent (two finite interpretations).
* `degreeAdequacyOfStrictComparative`: with the MORE_1-to-degree calibration
  the strict comparative yields the weaker non-strict "at least as much"
  represented degree; the proof never uses `Total`, so it holds for every cause.
* `strictComparativeWithoutNonStrictAdequacy`: on bare MORE_1 it does not. -/

namespace TruthCore.Results.Causality.CartesianAdequacy

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.CartesianAdequacy
open TruthCore.Causality.Round3FourthWay (MoreInExceedsDegree)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (PerfectionsOfEffectPreexistInCauseReading MoreSuchHasThePerfectionReading)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (CauseOfBeingCausesEveryPerfection)
open TruthCore.Logic (ExcludedMiddle)

/-- Containment in every cause and the cause-of-being transfer give PEPC: a
cause of `x`'s being causes `x`'s being `r` for each `r` `x` is in act in, and
whatever causes that is in act in `r`. -/
theorem preexistenceOfContainment {W B T R : Type} (F : GradesFrame W B T R)
    (hTransfer : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse)
    (hContain : ContainmentInEveryCause F) :
    PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse := by
  sorry

/-- The strict comparative, "more such has the perfection" and excluded middle
give containment in every cause: a distinct cause of `x`'s being `r` is more `r`
than `x` and so has `r`; a cause identical with `x` has `r` because `x` does. -/
theorem containmentOfStrictComparative {W B T R : Type} (F : GradesFrame W B T R)
    (hEM : ExcludedMiddle)
    (hStrict : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hHas : MoreSuchHasThePerfectionReading F.InAct F.MoreIn) :
    ContainmentInEveryCause F := by
  sorry

/-- Strength order: containment in every cause entails containment in total
causes, for every `Total`. -/
theorem totalContainmentOfContainment {W B T R : Type} (F : GradesFrame W B T R)
    (Total : B → B → R → Prop) (hContain : ContainmentInEveryCause F) :
    ContainmentInTotalCause F Total := by
  sorry

/-- Strength order: PEPC entails whole-effect containment in total causes of
being, for every `Total`. -/
theorem wholeEffectContainmentOfPreexistence {W B T R : Type} (F : GradesFrame W B T R)
    (Total : B → B → R → Prop)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) :
    WholeEffectContainmentInTotalCause F Total := by
  sorry

/-- Strength order: containment in every cause gives its instance at being,
nothing gives being that it does not have. -/
theorem causeOfABeingHasBeingOfContainment {W B T R : Type} (F : GradesFrame W B T R)
    (hContain : ContainmentInEveryCause F) :
    TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfABeingHasBeing
      F.InAct F.CausesIn F.esse := by
  sorry

/-- Respect-wise total-cause containment and PEPC are independent on finite
grades frames. -/
theorem containmentAndPreexistenceIndependent : ContainmentAndPreexistenceIndependent := by
  sorry

/-- With the calibration from MORE_1 to a represented degree, the strict
comparative yields the weaker non-strict comparative: at least as much
represented degree in every total cause (strictly more for a distinct cause,
the same for the effect itself). `Total` is never used, so the same proof
covers every cause. -/
theorem degreeAdequacyOfStrictComparative {W B T R D : Type} [Preorder D]
    (F : GradesFrame W B T R) (Total : B → B → R → Prop) (deg : R → B → D)
    (hEM : ExcludedMiddle)
    (hStrict : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hCalibration : MoreInExceedsDegree F.MoreIn deg) :
    AtLeastAsMuchDegreeInTotalCause F Total deg := by
  sorry

/-- On bare MORE_1 the strict comparative does not give the non-strict reading. -/
theorem strictComparativeWithoutNonStrictAdequacy :
    StrictComparativeWithoutNonStrictAdequacy := by
  sorry

end TruthCore.Results.Causality.CartesianAdequacy
