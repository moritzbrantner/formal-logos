module

public import TruthCore.Causality.SelectionScope
public import TruthCore.Causality.PracticalSpecification

/-!
# Content-fixed favouring and dependence on goodness (#2145, Lane 2b)

Analyst formulations, attribution deferred (logic first). Program #2145,
Investigations 2 and 3. See `docs/notes/optimal-creation-choice.md` §§65–69.

**Part A (a favouring standard that a re-description fails).** On the cell
carrier of `SelectionScope` (the local STIT frame, its histories through one
moment and an outcome map), an explanatory level supplies at each history a
*content* `e h`, and each content carries a favouring relation `fav c x y`
("content c counts in favour of x over y"). The level explains "the actual
outcome rather than y" when its actual content favours the actual outcome over
y (`FavouringExplains`). The content is *outcome-independent* when it is the
same at every compared history (`OutcomeIndependent`): it is fixed before, and
independently of, which outcome occurs. This is the cell-carrier analogue of
pro tanto favouring (SELECTING_AN_OUTCOME_1, `NetSelects` of #742), not one of
its senses and not bridged to it. Unlike the determination standard of
`SelectionScope` (law 8), it is not met trivially: an outcome-independent
asymmetric content cannot favour the realized outcome over its rivals at every
history of a scope with a contingent outcome. The re-description of the outcome
does that only by being outcome-dependent. This is the cell-carrier form of the
#742 incompatible core (base-fixed favouring, selection at both histories).

**Part B (what "because of its goodness" can mean).** Favouring is compared
across *variation scenarios* `s : S`: a profile `φ s x y` gives the source's
favouring in each scenario, and features of candidates (a physical type, the
realization of the recipient good D, a betterness standard) are scenario-indexed
relations. `DependsUnder g ctrl φ s x y`: the profile favours x over y at s, and in
some scenario that agrees with s on the controlled feature `ctrl`, `g` does not
rank x over y and neither does the profile (controlled difference-making). A
profile that factors through the control (`Function.FactorsThrough φ ctrl`)
depends on nothing else under that control; a fixed profile depends on nothing;
and if the goodness standard itself factors through the control, no profile
aligned with it depends on it. The three readings of "produced because of its
goodness" are kept apart (disambiguation BECAUSE_OF_GOODNESS):
`BecauseOfContent` (dependence on D-realization with nothing held fixed),
`BecauseOfGoodness` (dependence on betterness with D-realization held fixed)
and `PracticalSpecification.Governing` (an apprehended plan actually governs
the giving).

**Plan standard.** A `PracticalSpecification.Plan` induces a standard on
outcomes from its requirements (`planStandard`). It reads only `Requirement`,
so it is the same whatever the plan's `ApprehendsAsGood` and `SpecifiesGiving`
fields are: dependence on a plan's standard does not supply apprehension or
the primitive governing relation.

Every model below is a finite structural surrogate. It witnesses only the stated
formal interpretation, never a metaphysical possibility. Which philosophical
account a profile represents (rational exercise, good-sensitive propensity,
intrinsic generative finality, chance) is an interpretive assignment, not typed;
no intellect, apprehension, chance measure or simplicity is typed. Scenarios
that vary the goodness standard while D-realization is fixed are counterpossible
if goodness facts are necessary; law 4 of `GoodDependenceLaws` states what
follows without them.
-/

@[expose] public section

namespace TruthCore.Causality.GoodFavouring

open TruthCore.Modal.STIT
open TruthCore.Causality.SelectionScope
open TruthCore.Causality.PracticalSpecification (Plan Meets Clause)

/-! ## Part A: content-fixed favouring on choice cells -/

section Favouring

variable {M H A X C : Type} {F : BranchingFrame M H A} {m : M}

/-- OUTCOME-INDEPENDENT CONTENT: the explanans content `e` is the same at every
compared history: it is fixed independently of which outcome occurs. -/
def OutcomeIndependent (e : F.Through m → C) : Prop :=
  ∀ h k, e h = e k

/-- FAVOURING EXPLAINS A CONTRAST: at history `h`, the content `e h` favours the
actual outcome over `y`. Pro tanto: it need not exclude `y` from the cell. -/
def FavouringExplains (fav : C → X → X → Prop) (e : F.Through m → C) (h : F.Through m)
    (out : F.Through m → X) (y : X) : Prop :=
  fav (e h) (out h) y

/-- FAVOURING SELECTS: at `h`, the content favours the actual outcome over every
other realized outcome of the scope. -/
def FavouringSelects (fav : C → X → X → Prop) (e : F.Through m → C) (h : F.Through m)
    (out : F.Through m → X) : Prop :=
  ∀ y ∈ RealizedRange out, y ≠ out h → fav (e h) (out h) y

/-- The content selects whatever outcome occurs: at every history it favours that
history's outcome over every other realized outcome. -/
def SelectsAtEveryHistory (fav : C → X → X → Prop) (e : F.Through m → C)
    (out : F.Through m → X) : Prop :=
  ∀ k, FavouringSelects fav e k out

/-- Re-description content: the content is an outcome, and it favours that outcome
over every other one. Paired with `e := out` it re-describes what occurred. -/
def outcomeFavour : X → X → X → Prop :=
  fun c x y => x = c ∧ y ≠ c

/-- GOOD-BOUNDED: the content favours only what the standard `G` ranks higher. -/
def GoodBounded (fav : C → X → X → Prop) (e : F.Through m → C) (G : X → X → Prop) : Prop :=
  ∀ k x y, fav (e k) x y → G x y

end Favouring

/-- Laws of the content-fixed favouring standard (Part A).

1. **Non-triviality.** An outcome-independent content whose favouring relations
   are asymmetric does not select the realized outcome at every history of a
   scope with a contingent outcome. (The #742 core on the cell carrier.)
2. **The re-description.** The outcome itself, as content with `outcomeFavour`,
   selects whatever occurs at every history; its favouring relations are
   asymmetric; and with a contingent outcome it is not outcome-independent. So
   outcome independence is exactly what separates it from law 1.
3. **Invariant levels supply outcome-independent content.** A content constant on
   the cells of an invariant level (`InvariantExplanans`) is outcome-independent.
4. **Ties.** A good-bounded content does not select the actual outcome when some
   other realized outcome is not ranked below it by the standard.
5. **No best.** With an asymmetric standard under which every realized outcome is
   strictly bettered by a realized outcome, no good-bounded content selects. -/
def FavouringStandardLaws : Prop :=
  (∀ (M H A X C : Type) (F : BranchingFrame M H A) (m : M) (fav : C → X → X → Prop)
      (e : F.Through m → C) (out : F.Through m → X) (h : F.Through m),
    OutcomeIndependent e → (∀ c, Std.Asymm (fav c)) → ContingentOutcome h out →
      ¬ SelectsAtEveryHistory fav e out) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (out : F.Through m → X)
      (h : F.Through m),
    SelectsAtEveryHistory outcomeFavour out out ∧ (∀ c : X, Std.Asymm (outcomeFavour c)) ∧
      (ContingentOutcome h out → ¬ OutcomeIndependent out)) ∧
  (∀ (M H A C : Type) (F : BranchingFrame M H A) (m : M) (a : A) (e : F.Through m → C),
    InvariantExplanans F m a → (∀ h k, (F.choice m a).r h k → e h = e k) →
      OutcomeIndependent e) ∧
  (∀ (M H A X C : Type) (F : BranchingFrame M H A) (m : M) (fav : C → X → X → Prop)
      (e : F.Through m → C) (out : F.Through m → X) (h : F.Through m) (G : X → X → Prop)
      (y : X),
    GoodBounded fav e G → y ∈ RealizedRange out → y ≠ out h → ¬ G (out h) y →
      ¬ FavouringSelects fav e h out) ∧
  (∀ (M H A X C : Type) (F : BranchingFrame M H A) (m : M) (fav : C → X → X → Prop)
      (e : F.Through m → C) (out : F.Through m → X) (h : F.Through m) (G : X → X → Prop),
    GoodBounded fav e G → Std.Asymm G →
      (∀ x ∈ RealizedRange out, ∃ y ∈ RealizedRange out, G y x) →
      ¬ FavouringSelects fav e h out)

/-! ## Part B: dependence of favouring on a feature, across scenarios -/

section Dependence

variable {S X Z : Type}

/-- A favouring profile: the source's favouring of `x` over `y` in scenario `s`. -/
abbrev Profile (S X : Type) := S → X → X → Prop

/-- The profile coincides with the feature `f` in every scenario. -/
def Tracks (φ : Profile S X) (f : S → X → X → Prop) : Prop :=
  ∀ s x y, φ s x y ↔ f s x y

/-- The profile is the same in every scenario (determined to one content). -/
def Fixed (φ : Profile S X) : Prop :=
  ∀ s t x y, φ s x y ↔ φ t x y

/-- The profile coincides with the feature `f` in scenario `s`. -/
def AlignedAt (φ : Profile S X) (f : S → X → X → Prop) (s : S) : Prop :=
  ∀ x y, φ s x y ↔ f s x y

/-- CONTROLLED DEPENDENCE: at `s` the profile favours `x` over `y`, and in some
scenario agreeing with `s` on the controlled feature `ctrl`, the feature `g` does
not rank `x` over `y` and the profile does not favour it. -/
def DependsUnder (g : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (s : S) (x y : X) :
    Prop :=
  φ s x y ∧ ∃ t, ctrl t = ctrl s ∧ ¬ g t x y ∧ ¬ φ t x y

/-- BECAUSE_OF_GOODNESS_1 (end content): the favouring depends on the realization
of the end D (`fit`), with nothing held fixed beyond the scenario space. -/
def BecauseOfContent (fit : S → X → X → Prop) (φ : Profile S X) (s : S) (x y : X) : Prop :=
  DependsUnder fit (fun _ => ()) φ s x y

/-- BECAUSE_OF_GOODNESS_2 (goodness): the favouring depends on the betterness
standard `good` with the realization of D (`fitOf`) held fixed. -/
def BecauseOfGoodness {D : Type} (good : S → X → X → Prop) (fitOf : S → D) (φ : Profile S X)
    (s : S) (x y : X) : Prop :=
  DependsUnder good fitOf φ s x y

end Dependence

/-- PLAN STANDARD: plan `k` ranks `x` over `y` when the description of `x` meets
its requirements and that of `y` does not. Reads only `Requirement`. -/
def planStandard {W B R E K X : Type} (P : Plan W B R E K) (desc : X → Clause B R E → Prop) :
    K → X → X → Prop :=
  fun k x y => Meets P k (desc x) ∧ ¬ Meets P k (desc y)

/-- Laws of controlled dependence (Part B).

1. **Factoring.** A profile that factors through the controlled feature depends on
   nothing under that control.
2. **Fixity.** A fixed profile depends on nothing, under any control.
3. **Tracking.** A profile tracking `f` depends on `g` under `ctrl` exactly when
   `f` ranks `x` over `y` at `s` and some scenario agreeing on `ctrl` has neither
   `g` nor `f` ranking `x` over `y`.
4. **No variation, no dependence.** If the standard `g` factors through the
   control, a profile depends on `g` only by favouring what `g` does not rank
   higher; so no profile aligned with `g` at `s` depends on it. This holds of
   every profile, personal or impersonal by interpretation.
5. **Fixed and tracking.** A fixed profile tracks only a fixed feature.
6. **Label independence.** Two profiles tracking the same feature have the same
   dependence verdicts. Definitional.
7. **Plan standard is blind to apprehension.** Replacing a plan's
   `ApprehendsAsGood` and `SpecifiesGiving` fields leaves its standard unchanged,
   so a profile depends on the plan standards of the one plan exactly when it
   depends on those of the other. -/
def GoodDependenceLaws : Prop :=
  (∀ (S X Z : Type) (g : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (s : S) (x y : X),
    Function.FactorsThrough φ ctrl → ¬ DependsUnder g ctrl φ s x y) ∧
  (∀ (S X Z : Type) (g : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (s : S) (x y : X),
    Fixed φ → ¬ DependsUnder g ctrl φ s x y) ∧
  (∀ (S X Z : Type) (f g : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (s : S)
      (x y : X),
    Tracks φ f →
      (DependsUnder g ctrl φ s x y ↔ f s x y ∧ ∃ t, ctrl t = ctrl s ∧ ¬ g t x y ∧ ¬ f t x y)) ∧
  (∀ (S X Z : Type) (g : S → X → X → Prop) (ctrl : S → Z) (φ : Profile S X) (s : S) (x y : X),
    Function.FactorsThrough g ctrl →
      (DependsUnder g ctrl φ s x y → ¬ g s x y) ∧
        (AlignedAt φ g s → ¬ DependsUnder g ctrl φ s x y)) ∧
  (∀ (S X : Type) (f : S → X → X → Prop) (φ : Profile S X),
    Fixed φ → Tracks φ f → ∀ s t x y, f s x y ↔ f t x y) ∧
  (∀ (S X Z : Type) (f g : S → X → X → Prop) (ctrl : S → Z) (φ ψ : Profile S X) (s : S)
      (x y : X),
    Tracks φ f → Tracks ψ f → (DependsUnder g ctrl φ s x y ↔ DependsUnder g ctrl ψ s x y)) ∧
  (∀ (W B R E K X Z : Type) (P : Plan W B R E K) (desc : X → Clause B R E → Prop)
      (app : W → B → K → Prop) (spec : W → B → B → K → Prop) (ctrl : K → Z)
      (φ : Profile K X) (k : K) (x y : X),
    planStandard { P with ApprehendsAsGood := app, SpecifiesGiving := spec } desc =
        planStandard P desc ∧
      (DependsUnder (planStandard { P with ApprehendsAsGood := app, SpecifiesGiving := spec } desc)
          ctrl φ k x y ↔ DependsUnder (planStandard P desc) ctrl φ k x y))

/-! ## Part C: one matched model -/

namespace Model

/-- Variation scenarios. `actual`: c and d realize D and are tied, z and total
omission do not. `reversal`: the same physical provisions, but D is realized by c
and z, not d (recipient-relative reversal). `valueless`: D-realization as actual,
but no outcome is better than another (counterpossible if goodness facts are
necessary). `cBetter`: D-realization as actual, and c is better than d. -/
inductive Scenario
  | actual
  | reversal
  | valueless
  | cBetter
  deriving DecidableEq

/-- Physical provision type: c and d share one type; z and omission do not. It is
the same in every scenario. -/
def physical : Outcome → Bool
  | .c => true
  | .d => true
  | _ => false

/-- Realization of the recipient good D in each scenario. -/
def fits : Scenario → Outcome → Bool
  | .reversal, .c => true
  | .reversal, .z => true
  | .reversal, _ => false
  | _, .c => true
  | _, .d => true
  | _, _ => false

/-- Physical-type ordering (the same in every scenario). -/
def physOrder (_ : Scenario) (x y : Outcome) : Prop :=
  physical x = true ∧ physical y = false

/-- D-realization ordering. -/
def fitOrder (s : Scenario) (x y : Outcome) : Prop :=
  fits s x = true ∧ fits s y = false

/-- Betterness. It follows D-realization except where it is stipulated to vary. -/
def better : Scenario → Outcome → Outcome → Prop
  | .valueless, _, _ => False
  | .cBetter, x, y => fitOrder .cBetter x y ∨ (x = .c ∧ y = .d)
  | s, x, y => fitOrder s x y

/-- Chance: no favouring. -/
def chance : Profile Scenario Outcome := fun _ _ _ => False

/-- A propensity to the physical provision type, aligned with D in `actual`. -/
def proxy : Profile Scenario Outcome := physOrder

/-- Intrinsic generative finality directed to D (determined to that end). -/
def dNature : Profile Scenario Outcome := fitOrder

/-- A will with a fixed preference for D (the same profile, personal by interpretation). -/
def determinedWill : Profile Scenario Outcome := fitOrder

/-- A good-general nature: favours what is better (impersonal by interpretation). -/
def goodGeneral : Profile Scenario Outcome := better

/-- Rational exercise under a correctly apprehended good (personal by interpretation). -/
def rational : Profile Scenario Outcome := better

/-- The exercise frame of `SelectionScope` (scope c, d) and its two histories. -/
abbrev frame := exerciseSource

def hc : frame.Through () := ⟨.c, trivial⟩
def hd : frame.Through () := ⟨.d, trivial⟩

/-- The content fixed at scenario `s` at every history. -/
def at_ (s : Scenario) : frame.Through () → Scenario := fun _ => s

end Model

open Model in
/-- The matched table, at the actual outcome c of the exercise frame.

1. Fit links to `SelectionScope.Fit` in `actual`.
2. Standard A in `actual`: proxy, D-nature, determined will, good-general nature
   and rational exercise each explain "c rather than z" and "c rather than
   omission", none explains "c rather than d", and none selects c; chance
   explains none of them.
3. Standard A in `cBetter`: good-general and rational select c; D-nature and
   proxy do not explain "c rather than d".
4. The re-description selects at every history and is not outcome-independent;
   no outcome-independent content with asymmetric favouring does.
5. Dependence on D-realization (`BecauseOfContent`) for "d rather than z": the
   D-nature and both good-tracking profiles have it, the proxy and chance lack it.
6. Dependence on goodness with D-realization fixed (`BecauseOfGoodness`) for
   "c rather than z": good-general and rational have it; D-nature, determined will,
   proxy and chance lack it. The D-nature still favours the beneficial c over z.
7. The two good-tracking profiles are the same function, and so are the D-nature
   and the determined will. -/
def GoodFavouringTable : Prop :=
  (∀ o, fits .actual o = true ↔ Fit o) ∧
  ((∀ φ ∈ [proxy, dNature, determinedWill, goodGeneral, rational],
      FavouringExplains φ (at_ .actual) hc outcome .z ∧
      FavouringExplains φ (at_ .actual) hc outcome .none ∧
      ¬ FavouringExplains φ (at_ .actual) hc outcome .d ∧
      ¬ FavouringSelects φ (at_ .actual) hc outcome) ∧
    (∀ y, ¬ FavouringExplains chance (at_ .actual) hc outcome y)) ∧
  (FavouringSelects goodGeneral (at_ .cBetter) hc outcome ∧
    FavouringSelects rational (at_ .cBetter) hc outcome ∧
    ¬ FavouringExplains dNature (at_ .cBetter) hc outcome .d ∧
    ¬ FavouringExplains proxy (at_ .cBetter) hc outcome .d) ∧
  (SelectsAtEveryHistory outcomeFavour (outcome : frame.Through () → Outcome) outcome ∧
    ¬ OutcomeIndependent (outcome : frame.Through () → Outcome) ∧
    ∀ (C : Type) (fav : C → Outcome → Outcome → Prop) (e : frame.Through () → C),
      OutcomeIndependent e → (∀ c, Std.Asymm (fav c)) → ¬ SelectsAtEveryHistory fav e outcome) ∧
  (BecauseOfContent fitOrder dNature .actual .d .z ∧
    BecauseOfContent fitOrder goodGeneral .actual .d .z ∧
    BecauseOfContent fitOrder rational .actual .d .z ∧
    proxy .actual .d .z ∧ ¬ BecauseOfContent fitOrder proxy .actual .d .z ∧
    ¬ BecauseOfContent fitOrder chance .actual .d .z) ∧
  (BecauseOfGoodness better fits goodGeneral .actual .c .z ∧
    BecauseOfGoodness better fits rational .actual .c .z ∧
    (dNature .actual .c .z ∧ better .actual .c .z) ∧
    ¬ BecauseOfGoodness better fits dNature .actual .c .z ∧
    ¬ BecauseOfGoodness better fits determinedWill .actual .c .z ∧
    ¬ BecauseOfGoodness better fits proxy .actual .c .z ∧
    ¬ BecauseOfGoodness better fits chance .actual .c .z) ∧
  (goodGeneral = rational ∧ dNature = determinedWill)

end TruthCore.Causality.GoodFavouring
