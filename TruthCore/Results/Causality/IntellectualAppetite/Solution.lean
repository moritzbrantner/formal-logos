module

public import TruthCore.Causality.IntellectualAppetite
public import TruthCore.Causality.DeiFiliusLivingSelfOperation
public import TruthCore.Causality.Round5Worklist
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
public import TruthCore.Results.Causality.PracticalSpecification.Solution

@[expose] public section

namespace TruthCore.Results.Causality.IntellectualAppetite

open TruthCore.Case.Catholicism (GodHasIntellect GodHasWill)
open TruthCore.Causality.IntellectualAppetite
open TruthCore.Causality.IntellectualInclination
open TruthCore.Causality.AppetitePowerExercise
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

theorem godHasWillFromAppraisedForm {B F : Type}
    {IsGod HasIntellect HasWill : B → Prop}
    {HasForm Appraises InclinedTo : B → F → Prop} {Intelligible : F → Prop}
    (hIntellect : GodHasIntellect IsGod HasIntellect)
    (hAppraisal : GodIntellectApprehendsGood IsGod HasIntellect HasForm Appraises Intelligible)
    (hInclination : AppraisedFormInclines IsGod HasForm Appraises InclinedTo Intelligible)
    (hRecognition : AppraisedInclinationIsWill IsGod Appraises InclinedTo Intelligible HasWill) :
    GodHasWill IsGod HasWill := by
  intro g hg
  obtain ⟨f, hForm, hKind, hGood⟩ := hAppraisal g hg (hIntellect g hg)
  exact hRecognition g f hg hKind hGood (hInclination g f hg hForm hKind hGood)

/-- Restrict the old inclination law on the very same assignment of forms
and inclinations. This comparison is between Lean predicates. -/
theorem restrictFormInclination {B F : Type} {IsGod : B → Prop}
    {HasForm Appraises InclinedTo : B → F → Prop} {Intelligible : F → Prop}
    (h : EveryFormHasInclination HasForm InclinedTo) :
    AppraisedFormInclines IsGod HasForm Appraises InclinedTo Intelligible :=
  fun g f _ hForm _ _ => h g f hForm

theorem restrictRecognition {B F : Type} {IsGod : B → Prop} {Appraises InclinedTo : B → F → Prop}
    {Intelligible : F → Prop} {HasWill : B → Prop}
    (h : IntelligibleInclinationIsWill Intelligible InclinedTo HasWill) :
    AppraisedInclinationIsWill IsGod Appraises InclinedTo Intelligible HasWill :=
  fun g f _ hKind _ hInclination => h g f hKind hInclination

/-- Pure act rules out one represented alternative in the local calibration. -/
theorem exerciseAtPossessedGood {m : Interpretation} {R : Type}
    {HasWill : m.Subject → Prop} {InPotency : m.Subject → R → Prop}
    {g : m.Subject} {o : m.Object} {t : m.Occasion} {r : R}
    (hPure : PureAct InPotency g) (hWill : HasWill g)
    (hAppraisal : m.apprehendsGood g o t) (hPossessed : m.possessed g o t)
    (hCalibration : ExerciseOrPotency HasWill InPotency g o t r) :
    Nonempty (Exercise m g o t) :=
  (hCalibration hWill hAppraisal hPossessed).resolve_right (hPure r)

open TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency (InPotency)

/-- Worked calibration with POTENCY_1. The selected act predicate must
track exercise at this good and occasion when applied at this respect. -/
theorem exerciseAtMatchedRespect {m : Interpretation} {R : Type}
    {InAct CanBe : m.Subject → R → Prop}
    {g : m.Subject} {o : m.Object} {t : m.Occasion} {r : R}
    (hPure : PureAct (InPotency InAct CanBe) g) (hCan : CanBe g r)
    (hReflects : InAct g r → Nonempty (Exercise m g o t)) :
    Nonempty (Exercise m g o t) := by
  classical
  by_contra hIdle
  exact hPure r ⟨hCan, fun hAct => hIdle (hReflects hAct)⟩

open TruthCore.Causality.DeiFiliusAttributeField (Primitives)
open TruthCore.Causality.DeiFiliusLivingSelfOperation (PureActLifeAtSomeTimeIsLiving)

/-- Worked life application. The self-operation is separately supplied
at an actual time of the duration frame. -/
example {B R T : Type} {InPotency : B → R → Prop} {Operates Lives : B → T → Prop}
    {D : Primitives B} {g : B} {t : T}
    (hPure : PureAct InPotency g)
    (hLife : TruthCore.Causality.Round5Worklist.OperatingFromItselfIsLiving Operates Lives)
    (hBridge : PureActLifeAtSomeTimeIsLiving InPotency Lives D)
    (hOperates : Operates g t) : D.Lives g :=
  hBridge g hPure ⟨t, hLife g t hOperates⟩

open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.WillVersusChance (AgencyFrame)
open TruthCore.Causality.ThroughWill (RationallyGivesAt)
open TruthCore.Causality.PracticalSpecification

/-- Worked application at the same giver and distinct recipient.
Rational exercise in giving is a separate input to the direction proof. -/
example {W B T R S P E K : Type} {F : CausalityFrame W B T R} {A : AgencyFrame W B S P}
    {M : Plan W B R E K} {InAct : B → R → Prop} {Directs : B → B → E → Prop}
    {w : W} {g x : B}
    (hCoverage : RationalGivingHasPlan F A M InAct w)
    (hOmission : PlanRejectsEndOmission F M InAct w)
    (hRecognition : RequiredEndIsDirected M Directs w)
    (hDistinct : x ≠ g) (hActual : InAct x F.esse) (hGiving : RationallyGivesAt F A w g x) :
    ∃ e, Directs g x e :=
  TruthCore.Results.Causality.PracticalSpecification.effectDirectionOfPracticalSpecification
    hCoverage hOmission hRecognition g x hDistinct hActual hGiving

namespace Control

def yes (_ : Unit) : Prop := True
def no (_ : Unit) : Prop := False
def present (_ : Unit) (_ : Bool) : Prop := True
def absent (_ : Unit) (_ : Bool) : Prop := False
def selected (_ : Unit) (f : Bool) : Prop := f = true
def intelligible (f : Bool) : Prop := f = true
theorem godIntellect : GodHasIntellect yes yes := fun _ _ => trivial
theorem seesGood : GodIntellectApprehendsGood yes yes present selected intelligible :=
  fun _ _ _ => ⟨true, trivial, rfl, rfl⟩
theorem inclines : AppraisedFormInclines yes present selected selected intelligible :=
  fun _ _ _ _ _ h => h

/-- A populated intelligible good with no inclination. Scope and recognition
hold, while the local inclination principle and the will conclusion fail. -/
theorem contemplator :
    GodHasIntellect yes yes ∧ GodIntellectApprehendsGood yes yes present selected intelligible ∧
    AppraisedInclinationIsWill yes selected absent intelligible no ∧
    ¬ AppraisedFormInclines yes present selected absent intelligible ∧ ¬ GodHasWill yes no := by
  exact ⟨godIntellect, seesGood,
    fun _ _ _ _ _ h => h, fun h => h () true trivial trivial rfl rfl, fun h => h () trivial⟩

/-- The other omissions: empty intellect, missing good-appraisal or
unrecognized inclination. The positive application has a bearer. -/
theorem otherOmissions :
    (¬ GodHasIntellect yes no ∧ GodIntellectApprehendsGood yes no present absent intelligible ∧
      AppraisedFormInclines yes present absent absent intelligible ∧
      AppraisedInclinationIsWill yes absent absent intelligible no ∧ ¬ GodHasWill yes no) ∧
    (GodHasIntellect yes yes ∧ ¬ GodIntellectApprehendsGood yes yes present absent intelligible ∧
      AppraisedFormInclines yes present absent absent intelligible ∧
      AppraisedInclinationIsWill yes absent absent intelligible no ∧ ¬ GodHasWill yes no) ∧
    (GodHasIntellect yes yes ∧ GodIntellectApprehendsGood yes yes present selected intelligible ∧
      AppraisedFormInclines yes present selected selected intelligible ∧
      ¬ AppraisedInclinationIsWill yes selected selected intelligible no ∧ ¬ GodHasWill yes no) ∧
    (GodHasWill yes yes ∧ ∃ g, yes g) := by
  have noWill : ¬ GodHasWill yes no := fun h => h () trivial
  refine ⟨⟨fun h => h () trivial, fun _ _ h => h.elim, fun _ _ _ _ _ h => h,
      fun _ _ _ _ h _ => h, noWill⟩,
    ⟨godIntellect, ?_, fun _ _ _ _ _ h => h, fun _ _ _ _ h _ => h, noWill⟩,
    ⟨godIntellect, seesGood, inclines, fun h => h () true trivial rfl rfl rfl, noWill⟩, ?_⟩
  · intro h
    obtain ⟨_, _, _, hGood⟩ := h () trivial trivial
    exact hGood
  · have h := godHasWillFromAppraisedForm godIntellect seesGood inclines (fun _ _ _ _ _ _ => trivial)
    exact ⟨h, (), trivial⟩

/-- Checking maximal scope requires checking a form outside the appraised
intelligible class, even when a positive instance of the local law exists. -/
theorem scopeIsStrict :
    AppraisedFormInclines yes present selected selected intelligible ∧
    ¬ EveryFormHasInclination present selected ∧ selected () true := by
  exact ⟨fun _ _ _ _ _ h => h, fun h => Bool.noConfusion (h () false trivial), rfl⟩

theorem noExerciseWithIdleActs (IsSoul : Unit → Prop) :
    ¬ Nonempty (Exercise { idle with isSoul := IsSoul } () () ()) := by
  rintro ⟨episode⟩
  cases episode with
  | seeking _ _ act => exact act
  | loving _ _ act => exact act
  | delighting _ _ act => exact act
  | communicating _ _ _ _ act => exact act

/-- Paired cases at the same good and occasion. First a soul's possible
response without an act, then actual love in the matched assignment. -/
theorem capacityAndExercise :
    idleCapacity.Possessed ∧ ¬ Nonempty (Exercise idle () () ()) ∧
    Nonempty (Exercise possessedLove () () ()) := by
  exact ⟨⟨trivial, (), (), .love, rfl⟩, noExerciseWithIdleActs idle.isSoul,
    ⟨.loving trivial trivial trivial⟩⟩

/-- A bare pure-act assignment with possessed apprehended good and HasWill
omits the exercise calibration. The subject here is never assigned soulhood. -/
theorem pureActWithoutCalibration :
    let m : Interpretation := { idle with isSoul := fun _ => False }
    let potency : Unit → Unit → Prop := fun _ _ => False
    PureAct potency () ∧ yes () ∧ m.apprehendsGood () () () ∧ m.possessed () () () ∧
      ¬ Nonempty (Exercise m () () ()) ∧
      ¬ ExerciseOrPotency (m := m) yes potency () () () () := by
  have hNoExercise := noExerciseWithIdleActs (fun _ => False)
  refine ⟨fun _ h => h, trivial, trivial, trivial, hNoExercise, ?_⟩
  intro h
  exact (h trivial trivial trivial).elim hNoExercise id

end Control
end TruthCore.Results.Causality.IntellectualAppetite
