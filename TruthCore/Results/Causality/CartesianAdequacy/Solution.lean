module

public import TruthCore.Causality.CartesianAdequacy
public import TruthCore.Case.Catholicism.StageOneBridges

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

@[expose] public section

namespace TruthCore.Results.Causality.CartesianAdequacy

open TruthCore.Causality.Grades (GradesFrame)
open TruthCore.Causality.TermSenseForks (ActFrame)
open TruthCore.Causality.CartesianAdequacy
open TruthCore.Causality.Round3FourthWay (MoreInExceedsDegree)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (PerfectionsOfEffectPreexistInCauseReading MoreSuchHasThePerfectionReading
  MaximumInGenusCausesAllInGenusReading ActualityOnlyInsofarAsBeingReading)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic (ExcludedMiddle)

/-- Containment in every cause and the cause-of-being transfer give PEPC: a
cause of `x`'s being causes `x`'s being `r` for each `r` `x` is in act in, and
whatever causes that is in act in `r`. -/
theorem preexistenceOfContainment {W B T R : Type} (F : GradesFrame W B T R)
    (hTransfer : CauseOfBeingCausesEveryPerfection F.InAct F.CausesIn F.esse)
    (hContain : ContainmentInEveryCause F) :
    PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse := by
  intro c x r hc hx
  exact hContain c x r (hTransfer c x r hc hx) hx

/-- The strict comparative, "more such has the perfection" and excluded middle
give containment in every cause: a distinct cause of `x`'s being `r` is more `r`
than `x` and so has `r`; a cause identical with `x` has `r` because `x` does. -/
theorem containmentOfStrictComparative {W B T R : Type} (F : GradesFrame W B T R)
    (hEM : ExcludedMiddle)
    (hStrict : CauseOfQualityInAnotherIsMoreSuchReading F.CausesIn F.MoreIn)
    (hHas : MoreSuchHasThePerfectionReading F.InAct F.MoreIn) :
    ContainmentInEveryCause F := by
  intro c x r hc hx
  rcases hEM (c = x) with hEq | hNe
  · subst hEq
    exact hx
  · exact hHas r c x (hStrict c x r hNe hc)

/-- Strength order: containment in every cause entails containment in total
causes, for every `Total`. -/
theorem totalContainmentOfContainment {W B T R : Type} (F : GradesFrame W B T R)
    (Total : B → B → R → Prop) (hContain : ContainmentInEveryCause F) :
    ContainmentInTotalCause F Total := by
  intro c x r hc hx
  exact hContain c x r hc.1 hx

/-- Strength order: PEPC entails whole-effect containment in total causes of
being, for every `Total`. -/
theorem wholeEffectContainmentOfPreexistence {W B T R : Type} (F : GradesFrame W B T R)
    (Total : B → B → R → Prop)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse) :
    WholeEffectContainmentInTotalCause F Total := by
  intro c x r hc hx
  exact hPre c x r hc.1 hx

/-- Strength order: containment in every cause gives its instance at being,
nothing gives being that it does not have. -/
theorem causeOfABeingHasBeingOfContainment {W B T R : Type} (F : GradesFrame W B T R)
    (hContain : ContainmentInEveryCause F) :
    TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfABeingHasBeing
      F.InAct F.CausesIn F.esse := by
  intro c x hc hx
  exact hContain c x F.esse hc hx

/-- Respect-wise total-cause containment and PEPC are independent on finite
grades frames. -/
theorem containmentAndPreexistenceIndependent : ContainmentAndPreexistenceIndependent := by
  refine ⟨⟨gradesOf (fun x _ => x = false) (fun _ _ _ => False)
      (fun c x r => c = true ∧ x = false ∧ r = true) false,
    fun _ _ _ => True, ?_, ?_⟩,
    ⟨gradesOf (fun x r => x = false ∨ r = false) (fun _ _ _ => False)
      (fun c x _ => c = true ∧ x = false) false,
    fun _ _ r => r = false, ?_, ?_⟩⟩
  · rintro c x r ⟨_, _, h⟩ _
    exact Bool.noConfusion (show false = true from h)
  · intro h
    have := h true false true ⟨⟨rfl, rfl, rfl⟩, trivial⟩ rfl
    exact Bool.noConfusion (show true = false from this)
  · rintro c x r ⟨⟨_, _⟩, hr⟩ _
    exact Or.inr hr
  · intro h
    have := h true false true ⟨rfl, rfl⟩ (Or.inl rfl)
    rcases (show true = false ∨ true = false from this) with h1 | h1 <;>
      exact Bool.noConfusion h1

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
  intro c x r hc
  rcases hEM (c = x) with hEq | hNe
  · subst hEq
    exact le_refl _
  · exact le_of_lt (hCalibration r c x (hStrict c x r hNe hc.1))

/-- On bare MORE_1 the strict comparative does not give the non-strict reading. -/
theorem strictComparativeWithoutNonStrictAdequacy :
    StrictComparativeWithoutNonStrictAdequacy := by
  refine ⟨gradesOf (fun _ _ => True) (fun _ _ _ => True) (fun c x _ => c ≠ x) (),
    fun _ _ _ => True, ?_, ?_, ?_⟩
  · intro _ _ _ _ _
    trivial
  · intro _ _ _ _
    trivial
  · intro h
    exact h true false () ⟨(by decide : true ≠ false), trivial⟩ trivial


/-! ## Asymmetric q.4 → source-level intellect containment -/

/-- The exact two sense bridges needed to read the legacy uniform q.4
preexistence as formal effect / formally-or-eminently possessed cause.
Neither bridge follows merely from the word "in act". -/
theorem asymmetricFromUniform {W B T R : Type} (F : GradesFrame W B T R)
    (A : ActFrame B R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading F.InAct F.CausesIn F.esse)
    (hFormal : FormalActEntersGrades F A)
    (hInclusive : GradesActIsInclusive F A) :
    FormalEffectPreexistsInclusively F A := by
  intro c x r hCause hEff
  exact hInclusive c r (hPre c x r hCause (hFormal x r hEff))

/-- At EVERY supplied GOD_4 maximal being g, one formally intellectual EXEMPLAR is enough, even without proving it is
distinct from g: if g = x, it already has that perfection formally; otherwise
g causes the exemplar's esse and hence contains its cognitive respect formally
or eminently. This uses explicit excluded middle and holds at the SAME g.
No intrinsic intellect or actual exercise is concluded. -/
theorem godContainsFromIntellectualExemplar {W B T R : Type}
    (F : GradesFrame W B T R) (A : ActFrame B R)
    (IsGod HasIntellect : B → Prop) (intellectual : R)
    (hMaximal : GodIsMaximalInBeing IsGod F.InAct F.MoreIn F.esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading
      F.InAct F.MoreIn F.CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading F.InAct F.esse)
    (hSome : ∃ x, HasIntellect x)
    (hEM : ExcludedMiddle)
    (hFormal : ∀ x, HasIntellect x → A.InActFormally x intellectual)
    (hFormalCalibration : FormalActEntersGrades F A)
    (hAsymmetric : FormalEffectPreexistsInclusively F A) :
    GodContainsIntellectualPerfection A IsGod intellectual := by
  obtain ⟨x, hx⟩ := hSome
  have hFormalX := hFormal x hx
  intro g hg
  rcases hEM (x = g) with hSame | hOther
  · subst x
    exact Or.inl hFormalX
  · have hActualX := hFormalCalibration x intellectual hFormalX
    have hEsseX := hBeing x intellectual hActualX
    have hCause := hGenus F.esse g (hMaximal g hg) x hOther hEsseX
    exact hAsymmetric g x intellectual hCause hFormalX

/-- Direct q.4 first-mover consumer: reuses its verified "every perfection
found in things" result at the SAME first mover, and merely specializes the
intellectual respect. A cognitive exemplar is needed; a mere name for the
respect cannot produce one. The q.4 theorem carries its own causal/identity
premises; this does not supply those premises independently. -/
theorem firstMoverContainsIntellect {W B T R : Type}
    (F : GradesFrame W B T R) (A : ActFrame B R)
    (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (HasIntellect : B → Prop) (intellectual : R)
    (hQ4 : FirstUnmovedMoverHasEveryPerfectionOfThings MovedIn MovesIn F.InAct)
    (hSome : ∃ x, HasIntellect x)
    (hForm : ∀ x, HasIntellect x → A.InActFormally x intellectual)
    (hFormalCalibration : FormalActEntersGrades F A)
    (hInclusive : GradesActIsInclusive F A) :
    ∀ f, IsFirstUnmovedMover MovedIn MovesIn f →
      A.InActFormallyOrVirtually f intellectual := by
  obtain ⟨x, hx⟩ := hSome
  intro f hf
  exact hInclusive f intellectual (hQ4 f hf x intellectual
    (hFormalCalibration x intellectual (hForm x hx)))

/-- Explicit remaining API bridge to HAS_INTELLECT_1: the formal and virtual
branches require DIFFERENT recognition obligations. In particular an
effective power to cause intellectual beings is not by definition an intrinsic
capacity for intentional understanding. This is an adapter, not a discharge
of either recognition premise or a new will route. -/
theorem intrinsicIntellectOfContainment {B R : Type}
    (A : ActFrame B R) (IsGod HasIntellect : B → Prop) (intellectual : R)
    (hContains : GodContainsIntellectualPerfection A IsGod intellectual)
    (hFormalRecognition : ∀ b, A.InActFormally b intellectual → HasIntellect b)
    (hEminentRecognition : ∀ b, A.InActVirtually b intellectual → HasIntellect b) :
    GodHasIntellect IsGod HasIntellect := by
  intro g hg
  rcases hContains g hg with hFormal | hVirtual
  · exact hFormalRecognition g hFormal
  · exact hEminentRecognition g hVirtual

/-- Populated finite separation of formally cognitive effect, inclusive causal
containment, intrinsic source intellect and actual exercise; with a second
model witnessing cognitive production without containment. -/
theorem formalEminentControls : FormalEminentControl.Controls := by
  decide

end TruthCore.Results.Causality.CartesianAdequacy
