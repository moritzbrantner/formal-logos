module

public import Mathlib.Order.Minimal
public import Mathlib.Order.Preorder.Finite
public import TruthCore.Models.STITControls
public import TruthCore.Causality.WillVersusChance
public import TruthCore.Modal.Kripke

/-!
# Permitted range versus actual selection, and three omission scopes (#2145, Lane 2)

Analyst formulations, attribution deferred (logic first). Program #2145 asks
whether a simple necessary foundation can be impersonal. Investigation 3 asks
how an invariant, unlimited source can produce particular finite effects without
necessitating them, and whether an account explains the *actual selection* or
only a *range of permitted outcomes*. See `docs/notes/optimal-creation-choice.md`
§§59–63.

**Part A (one standard, one carrier).** The carrier is the local STIT frame
(`TruthCore.Modal.STIT`): the histories through one moment are the compared
outcome scope, an outcome map assigns each history its outcome, and an agent's
choice cells partition the histories. An agent here is an *explanatory level of
one source*: its cells are the classes of histories that agree on that level's
explanans. A source's invariant nature has one cell; an exercise (adoption,
actualization, generative act) that varies with the outcome has finer cells.
The contrastive standard is `Cstit`: the actual explanans explains "this rather
than y" exactly when no history agreeing with it on that explanans has outcome
y. It is the determination test (SELECTING_AN_OUTCOME_2, a reason false at each
rival-history), not a theory of explanation; nothing here says that determination
is the only kind of explanation.

**Part B (three omission scopes).** On the shared `CausalityFrame`, a source's
giving can be withheld recipient by recipient (`WithholdsEachAt`), for the whole
actual roster with replacement allowed (`WithholdsActualRosterAt`), or wholly
(`WithholdsAllAt`). The complete-decision fork of #1953 is stated with Mathlib's
`Maximal` on a partial order of complete decisions.

**Part C (scope of `0050b6ed`).** `GodsHoldActualAbsencePower` asks for a power
for the joint absence of the concrete beings contingent at `w` (replacement
allowed). Its cited warrant (total refraining) is the stronger
`GodsHoldTotalAbsencePower`; the passage needs Euclidean access and the
monotonicity of `PowerFor` under accessible entailment.

Every model below is a finite structural surrogate. It witnesses only the stated
formal interpretation, never a metaphysical possibility, and supplies no
intellect, apprehension, goodness or simplicity beyond the named predicates.
-/

@[expose] public section

namespace TruthCore.Causality.SelectionScope

open TruthCore.Modal.STIT
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Modal.PrussPowerPremises (GivesTo FixedGiver ActualAbsenceByWithholding)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn NoContingentConcreteIn)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Causality.WillVersusChance (GodsHoldActualAbsencePower)

/-! ## Part A: range and selection on choice cells -/

section RangeSelection

variable {M H A X : Type} {F : BranchingFrame M H A} {m : M}

/-- REALIZED RANGE: the outcomes realized by some history of the compared scope
(the histories through `m`). The *permitted range* of an account is what it
allows; in this scope it is the realized range. -/
def RealizedRange (out : F.Through m → X) : Set X := Set.range out

/-- CELL RANGE: the outcomes realized by histories that agree with the actual
history `h` on the explanans of level `a` (its actual choice cell). The outcomes
an account leaves open after its actual explanans is given. -/
def CellRange (a : A) (h : F.Through m) (out : F.Through m → X) : Set X :=
  {y | ∃ k, (F.choice m a).r h k ∧ out k = y}

/-- CONTRAST EXPLAINED (determination standard): the actual explanans of level
`a` at `h` rules out outcome `y`: no history agreeing with it has outcome `y`.
`Cstit a h (out ≠ y)`. A test of contrastive determination, not of
explanatory adequacy. -/
def ExplainsContrast (a : A) (h : F.Through m) (out : F.Through m → X) (y : X) : Prop :=
  Cstit a h (fun k => out k ≠ y)

/-- ACTUAL SELECTION EXPLAINED: the actual explanans of level `a` fixes the
actual outcome: every history agreeing with it has the actual outcome. -/
def SelectsActual (a : A) (h : F.Through m) (out : F.Through m → X) : Prop :=
  Cstit a h (fun k => out k = out h)

/-- INVARIANT EXPLANANS: level `a` has a single cell: every history in the scope
agrees on its explanans. Example: a source's necessary nature, propensity or
standing will, the same in every compared history. -/
def InvariantExplanans (F : BranchingFrame M H A) (m : M) (a : A) : Prop :=
  ∀ h k : F.Through m, (F.choice m a).r h k

/-- The proposition that a history agrees with `h` on the explanans of level `a`
(lies in `a`'s actual cell): "the actual adoption/actualization/exercise
obtains". -/
def InCell (a : A) (h : F.Through m) : F.Through m → Prop :=
  fun k => (F.choice m a).r h k

/-- The outcome is contingent in the scope: some compared history has another
outcome. -/
def ContingentOutcome (h : F.Through m) (out : F.Through m → X) : Prop :=
  ∃ k, out k ≠ out h

end RangeSelection

/-- General laws of the determination standard (Part A).

1. **Cell characterization.** Level `a` explains "the actual outcome rather
   than `y`" exactly when `y` is not in its cell range.
2. **The #1953 decomposition.** For any candidate set `T0` containing the
   realized range, the unexplained-away candidates `T0 \ CellRange` split
   disjointly into those outside the range (`T0 \ RealizedRange`, answered by
   the range) and those inside it but outside the cell (`RealizedRange \
   CellRange`, answered only by the explanans that fixes the cell).
3. **Projection boundary.** An invariant explanans explains a contrast exactly
   when the rival outcome is outside the realized range: it explains the range
   and nothing within it.
4. **Necessary manifestation.** An invariant explanans selects the actual
   outcome exactly when the outcome is not contingent in the scope.
5. **Selection is every contrast.** Selection holds exactly when every rival
   outcome is excluded.
6. **Relocation.** If level `a` selects a contingent actual outcome, then `a`
   deliberatively sees to its own actual cell (`Dstit`: its explanans is itself
   contingent in the scope), and no invariant explanans of any level sees to that
   cell: the contrast between the actual explanans and its alternatives is not
   determined by anything invariant.
7. **Label independence.** Two levels with the same actual cell explain exactly
   the same contrasts; the standard consults the cell partition only. -/
def SelectionRangeLaws : Prop :=
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h : F.Through m)
      (out : F.Through m → X) (y : X),
    ExplainsContrast a h out y ↔ y ∉ CellRange a h out) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h : F.Through m)
      (out : F.Through m → X) (T0 : Set X),
    RealizedRange out ⊆ T0 →
    T0 \ CellRange a h out =
        (T0 \ RealizedRange out) ∪ (RealizedRange out \ CellRange a h out) ∧
      Disjoint (T0 \ RealizedRange out) (RealizedRange out \ CellRange a h out)) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h : F.Through m)
      (out : F.Through m → X) (y : X),
    InvariantExplanans F m a → (ExplainsContrast a h out y ↔ y ∉ RealizedRange out)) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h : F.Through m)
      (out : F.Through m → X),
    InvariantExplanans F m a → (SelectsActual a h out ↔ ¬ ContingentOutcome h out)) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h : F.Through m)
      (out : F.Through m → X),
    SelectsActual a h out ↔ ∀ y, y ≠ out h → ExplainsContrast a h out y) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a : A) (h : F.Through m)
      (out : F.Through m → X),
    SelectsActual a h out → ContingentOutcome h out →
      Dstit a h (InCell a h) ∧ ∀ b, InvariantExplanans F m b → ¬ Cstit b h (InCell a h)) ∧
  (∀ (M H A X : Type) (F : BranchingFrame M H A) (m : M) (a b : A) (h : F.Through m)
      (out : F.Through m → X) (y : X),
    (∀ k, (F.choice m a).r h k ↔ (F.choice m b).r h k) →
      (ExplainsContrast a h out y ↔ ExplainsContrast b h out y))

/-! ### The matched four-account model

One carrier for every account: four candidate outcomes, matched in reach,
efficacy and recipient good. `c` and `d` are creations that realize the
recipient good D (`Fit`); `z` is a creation that does not; `none` is total
omission. Every history is a complete outcome (`Outcome`), its outcome map is
the history itself. Two explanatory levels of the one source are agents:
`nature` (its invariant nature, propensity or standing will: one cell) and
`exercise` (its actual adoption, actualization or generative exercise, whose
cells follow the outcome map `f`). -/

/-- Candidate complete outcomes. -/
inductive Outcome
  | none
  | c
  | d
  | z
  deriving DecidableEq

/-- The recipient good D is realized by `c` and `d`, not by `z` or `none`. -/
def Fit : Outcome → Prop
  | .c => True
  | .d => True
  | _ => False

/-- The level of the source's invariant nature. -/
abbrev nature : Bool := false

/-- The level of the source's actual exercise. -/
abbrev exercise : Bool := true

/-- An account with modal scope `scope` (the outcomes it can realize) and an
exercise level whose explanans at each outcome is `f`. The nature level has one
cell. -/
def accountFrame {E : Type} (scope : Outcome → Prop) (f : Outcome → E) :
    BranchingFrame Unit Outcome Bool where
  traverses _ o := scope o
  choice _ a := Setoid.ker fun k => if a = true then some (f k.val) else none

/-- Outcome map: a history is its outcome. -/
def outcome {E : Type} {scope : Outcome → Prop} {f : Outcome → E} :
    (accountFrame scope f).Through () → Outcome :=
  Subtype.val

/-- Only `c`: the scope of a necessary manifestation. -/
def onlyC (o : Outcome) : Prop := o = .c

/-- Categorical good-directed scope: exactly the D-realizing creations. -/
def fitScope (o : Outcome) : Prop := Fit o

/-- Permissive scope: total omission or a D-realizing creation. -/
def permissiveScope (o : Outcome) : Prop := o = .none ∨ Fit o

/-- An exercise level that adds nothing: it does not vary. -/
def noExercise (_ : Outcome) : Unit := ()

/-- An exercise level that varies with the outcome: adoption of, actualization
toward, or generative exercise into, that outcome. -/
def outcomeExercise (o : Outcome) : Outcome := o

/-- Necessary manifestation: the source necessarily produces `c`. -/
abbrev manifestation := accountFrame onlyC noExercise

/-- Invariant D-range source (impersonal propensity matched to the D-range, or
intrinsic generative finality, or a standing will, with no further exercise
datum): scope `Fit`, no varying exercise. -/
abbrev rangeSource := accountFrame fitScope noExercise

/-- The same with total omission in scope. -/
abbrev permissiveRange := accountFrame permissiveScope noExercise

/-- Exercise account: scope `Fit` and a varying exercise level. The rational
free exercise (adoption), the propensity's actualization and the generative
nature's exercise all have this encoding when matched. -/
abbrev exerciseSource := accountFrame fitScope outcomeExercise

/-- The same with total omission in scope. -/
abbrev permissiveExercise := accountFrame permissiveScope outcomeExercise

/-- The actual history `c` in each scope containing it. -/
def actualIn {E : Type} (scope : Outcome → Prop) (f : Outcome → E) (hc : scope .c) :
    (accountFrame scope f).Through () :=
  ⟨.c, hc⟩

/-- The comparison table, all at the actual outcome `c`.

* Necessary manifestation: its invariant nature excludes every rival and
  selects `c`, and `c` is not contingent in its scope.
* Invariant D-range source (categorical): its nature explains "rather than
  nothing" and "rather than the unfit `z`", not "rather than `d`"; no
  selection; `c` contingent.
* Invariant permissive source: its nature explains "rather than `z`" but not
  "rather than nothing".
* Exercise account (categorical and permissive): its exercise level selects
  `c`, including "rather than nothing" in the permissive scope; the exercise is
  contingent (`Dstit` of its own cell) and the nature level does not see to it.
  The nature level of the same frame keeps the range profile. -/
def FourAccountTable : Prop :=
  (ExplainsContrast (F := manifestation) nature (actualIn onlyC noExercise rfl) outcome .none ∧
    ExplainsContrast (F := manifestation) nature (actualIn onlyC noExercise rfl) outcome .z ∧
    ExplainsContrast (F := manifestation) nature (actualIn onlyC noExercise rfl) outcome .d ∧
    SelectsActual (F := manifestation) nature (actualIn onlyC noExercise rfl) outcome ∧
    ¬ ContingentOutcome (F := manifestation) (actualIn onlyC noExercise rfl) outcome) ∧
  (ExplainsContrast (F := rangeSource) nature (actualIn fitScope noExercise trivial) outcome .none ∧
    ExplainsContrast (F := rangeSource) nature (actualIn fitScope noExercise trivial) outcome .z ∧
    ¬ ExplainsContrast (F := rangeSource) nature (actualIn fitScope noExercise trivial) outcome .d ∧
    ¬ SelectsActual (F := rangeSource) nature (actualIn fitScope noExercise trivial) outcome ∧
    ContingentOutcome (F := rangeSource) (actualIn fitScope noExercise trivial) outcome) ∧
  (¬ ExplainsContrast (F := permissiveRange) nature
      (actualIn permissiveScope noExercise (Or.inr trivial)) outcome .none ∧
    ExplainsContrast (F := permissiveRange) nature
      (actualIn permissiveScope noExercise (Or.inr trivial)) outcome .z) ∧
  (SelectsActual (F := exerciseSource) exercise (actualIn fitScope outcomeExercise trivial)
      outcome ∧
    ContingentOutcome (F := exerciseSource) (actualIn fitScope outcomeExercise trivial) outcome ∧
    Dstit (F := exerciseSource) exercise (actualIn fitScope outcomeExercise trivial)
      (InCell exercise (actualIn fitScope outcomeExercise trivial)) ∧
    ¬ Cstit (F := exerciseSource) nature (actualIn fitScope outcomeExercise trivial)
      (InCell exercise (actualIn fitScope outcomeExercise trivial)) ∧
    ¬ ExplainsContrast (F := exerciseSource) nature (actualIn fitScope outcomeExercise trivial)
      outcome .d) ∧
  (ExplainsContrast (F := permissiveExercise) exercise
      (actualIn permissiveScope outcomeExercise (Or.inr trivial)) outcome .none ∧
    ¬ ExplainsContrast (F := permissiveExercise) nature
      (actualIn permissiveScope outcomeExercise (Or.inr trivial)) outcome .none ∧
    Dstit (F := permissiveExercise) exercise
      (actualIn permissiveScope outcomeExercise (Or.inr trivial))
      (InCell exercise (actualIn permissiveScope outcomeExercise (Or.inr trivial))))

/-! ## Part B: three omission scopes of a source's giving -/

section Omission

variable {W B T R : Type}

/-- INDIVIDUAL OMISSION: each being `g` gives being to at `w` is withheld at some
accessible world where `g` exists. Different recipients may use different
worlds. -/
def WithholdsEachAt (F : CausalityFrame W B T R) (w : W) (g : B) : Prop :=
  ∀ x, GivesTo F w g x →
    ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v g ∧ ¬ GivesTo F v g x

/-- WHOLE ACTUAL ROSTER WITHHELD, replacement allowed: at one accessible world
where `g` exists, `g` gives none of the beings it gives at `w`; it may give
others. The giving-level counterpart of `NoActualContingentConcreteIn`. -/
def WithholdsActualRosterAt (F : CausalityFrame W B T R) (w : W) (g : B) : Prop :=
  ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v g ∧
    ∀ x, GivesTo F w g x → ¬ GivesTo F v g x

/-- TOTAL REFRAINING: at one accessible world where `g` exists, `g` gives
nothing. Not the same as there being no contingent concretum there: brute or
otherwise-caused beings are not excluded. -/
def WithholdsAllAt (F : CausalityFrame W B T R) (w : W) (g : B) : Prop :=
  ∃ v, F.history.ontic.frame.access w v ∧ F.history.ontic.ExistsAt v g ∧ ∀ x, ¬ GivesTo F v g x

/-- NECESSARILY PRODUCTIVE: at every accessible world where `g` exists it gives
something. The giving-level form of a necessarily operative productive purpose,
of a categorically directed generative nature, or of a maximizer for whom some
creation beats omission. -/
def NecessarilyGivesSomeAt (F : CausalityFrame W B T R) (w : W) (g : B) : Prop :=
  ∀ v, F.history.ontic.frame.access w v → F.history.ontic.ExistsAt v g → ∃ x, GivesTo F v g x

end Omission

namespace Model

open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 gFrame uni replEx givesCHere givesDThere
  vanCleveG theistG allC gPower)

/-- §56's replacement table: universal access, `g` everywhere, `c` only at
`false`, `d` only at `true`; `g` gives `c` at `false` and `d` at `true`. -/
def replGivingG : CausalityFrame Bool Bg Unit Bool :=
  gFrame uni replEx fun v y x => givesCHere v y x ∨ givesDThere v y x

end Model

open Model in
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 vanCleveG theistG allC gPower) in
/-- The omission-scope table.

1. Total refraining gives whole-roster withholding, which gives individual
   omission of each recipient.
2. A necessarily productive source never totally refrains.
3. A fixed giver (necessary manifestation) existing at `w` that gives something
   there withholds no recipient individually.
4. Van Cleve's frame with a giver: each actual recipient is individually
   withheld, the whole roster is not, and the source is necessarily productive.
5. §56's replacement table: the whole actual roster is withheld (by
   replacement), there is no total refraining, the source is necessarily
   productive, and #1897's `ActualAbsenceByWithholding` holds.
6. The theist surrogate: total refraining.
7. The registered STIT controls on the decision frame: each single recipient
   can be ensured absent while no cell omits all creation (`pointwiseNotJoint`),
   and two tied optimal outputs each omit an optional recipient while every
   cell creates the common one (`tiedNoEmptyChoice`). -/
def OmissionScopeTable : Prop :=
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (g : B),
    (WithholdsAllAt F w g → WithholdsActualRosterAt F w g) ∧
    (WithholdsActualRosterAt F w g → WithholdsEachAt F w g)) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (g : B),
    NecessarilyGivesSomeAt F w g → ¬ WithholdsAllAt F w g) ∧
  (∀ (W B T R : Type) (F : CausalityFrame W B T R) (w : W) (g x : B),
    FixedGiver F g → F.history.ontic.ExistsAt w g → GivesTo F w g x → ¬ WithholdsEachAt F w g) ∧
  (WithholdsEachAt vanCleveG .a .g ∧ ¬ WithholdsActualRosterAt vanCleveG .a .g ∧
    NecessarilyGivesSomeAt vanCleveG .a .g) ∧
  (WithholdsActualRosterAt replGivingG false .g ∧ ¬ WithholdsAllAt replGivingG false .g ∧
    NecessarilyGivesSomeAt replGivingG false .g ∧
    ActualAbsenceByWithholding replGivingG gPower allC false) ∧
  WithholdsAllAt theistG false .g ∧
  ((∀ x : Bool, CanEnsure (historical _ _) false TruthCore.Models.STITControls.actual
      (fun k => TruthCore.Models.STITControls.choiceWorld k ≠ x)) ∧
    ¬ CanEnsure (historical _ _) false TruthCore.Models.STITControls.actual
      (fun k => ∀ x, TruthCore.Models.STITControls.choiceWorld k ≠ x)) ∧
  ((∀ k, TruthCore.Modal.WillChoiceCensus.optimal TruthCore.Modal.WillChoiceCensus.quality
      (TruthCore.Models.STITControls.tiedOutput k) = true) ∧
    CanEnsure (historical _ _) false TruthCore.Models.STITControls.actual
      (fun k => TruthCore.Modal.WillChoiceCensus.includes
        (TruthCore.Models.STITControls.tiedOutput k) 1 = false) ∧
    ¬ CanEnsure (historical _ _) false TruthCore.Models.STITControls.actual
      (fun k => ∀ x, TruthCore.Modal.WillChoiceCensus.includes
        (TruthCore.Models.STITControls.tiedOutput k) x = false))

/-! ### The complete-decision fork (#1953 §1) -/

/-- The fork for complete decisions under a strict partial order of
all-things-considered superiority (`<` of a Mathlib `PartialOrder`); the
feasible decisions are omission `o` together with the creation decisions `C`;
`Maximal (· ∈ insert o C)` is "not strictly surpassed". Not the `IsGreatest`
optimum of `OptimalCreationChoice.Optimal`, which is stronger in partial orders.

1. Omission is undominated exactly when no creation strictly surpasses it.
2. A creation is undominated among all decisions exactly when it is undominated
   among creations and omission does not strictly surpass it.
3. In a finite creation set with a unique undominated creation `m`, `m`
   strictly surpasses every other creation.
4. If every creation is strictly improvable by a creation and some creation
   surpasses omission, no decision is undominated.
5. A policy choosing an undominated decision at every world of a scope, when
   some creation surpasses omission, never chooses omission there.
6. Control: two incomparable creations both surpass omission; a policy choosing
   one of them at each world chooses only undominated decisions, never omits,
   and omits each particular creation at some world. -/
def CompleteDecisionFork : Prop :=
  (∀ (D : Type) [PartialOrder D] (C : Set D) (o : D),
    Maximal (· ∈ insert o C) o ↔ ¬ ∃ c ∈ C, o < c) ∧
  (∀ (D : Type) [PartialOrder D] (C : Set D) (o c : D), c ∈ C →
    (Maximal (· ∈ insert o C) c ↔ Maximal (· ∈ C) c ∧ ¬ c < o)) ∧
  (∀ (D : Type) [PartialOrder D] (C : Set D) (m : D), C.Finite → Maximal (· ∈ C) m →
    (∀ c, Maximal (· ∈ C) c → c = m) → ∀ c ∈ C, c ≠ m → c < m) ∧
  (∀ (D : Type) [PartialOrder D] (C : Set D) (o : D),
    (∀ c ∈ C, ∃ c' ∈ C, c < c') → (∃ c ∈ C, o < c) → ¬ ∃ d, Maximal (· ∈ insert o C) d) ∧
  (∀ (W D : Type) [PartialOrder D] (C : Set D) (o : D) (scope : W → Prop) (chosen : W → D),
    (∀ v, scope v → Maximal (· ∈ insert o C) (chosen v)) → (∃ c ∈ C, o < c) →
      ∀ v, scope v → chosen v ≠ o) ∧
  (let C : Set (Set Bool) := {{true}, {false}}
   let chosen : Bool → Set Bool := fun b => {b}
   (∀ b, Maximal (· ∈ insert ∅ C) (chosen b)) ∧ (∃ c ∈ C, ∅ < c) ∧
     (∀ b, chosen b ≠ ∅) ∧ ∀ c ∈ C, ∃ b, chosen b ≠ c)

/-! ## Part C: the scope of `0050b6ed` -/

section PowerScope

variable {W B T R : Type}

/-- OPEN (strong sibling of `0050b6ed`, total refraining): every GOD_4 exists at
`w` and has at `w` a power for there being no contingent concrete being. The
reading of "could have refrained from creating" at the level of contingent
concreta (ST I q.19 a.3; navigation only). -/
def GodsHoldTotalAbsencePower (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod : B → Prop) (w : W) :
    Prop :=
  ∀ g, IsGod g → F.history.ontic.ExistsAt w g ∧ PowerFor w g (NoContingentConcreteIn F concrete)

/-- OPEN bridge (monotone powers): at `w`, a power for `p` is a power for any `q`
that holds at every accessible world where `p` holds. Reading: an exercise
issuing in `p` obtaining issues in `q` obtaining. Its cost: any power is then a
power for whatever holds at every accessible world. -/
def PowerForMonotoneAt (F : CausalityFrame W B T R) (PowerFor : W → B → (W → Prop) → Prop)
    (w : W) : Prop :=
  ∀ y (p q : W → Prop), (∀ v, F.history.ontic.frame.access w v → p v → q v) →
    PowerFor w y p → PowerFor w y q

/-- The possibility reading of a power, used only in controls: `y` has at `w` a
power for `p` when `p` holds at an accessible world where `y` exists. Monotone;
no causal content. -/
def possibilityPower (F : CausalityFrame W B T R) (w : W) (y : B) (p : W → Prop) : Prop :=
  ∃ v, F.history.ontic.frame.access w v ∧ p v ∧ F.history.ontic.ExistsAt v y

end PowerScope

namespace Model

open TruthCore.Modal.PrussPowerPremises.Model (Bg gFrame allC)

/-- Three worlds: `none` (no creature), `some false` (`c`), `some true` (`d`);
`g` everywhere and gives each creature where it exists; universal access. -/
def threeEx (v : Option Bool) (x : Bg) : Prop :=
  x = .g ∨ (x = .c ∧ v = some false) ∨ (x = .d ∧ v = some true)

/-- The three-world frame with giving. -/
def threeG : CausalityFrame (Option Bool) Bg Unit Bool :=
  gFrame (fun _ _ => True) threeEx fun v y x => y = .g ∧ x ≠ .g ∧ threeEx v x

/-- A maximally specific power: `g` has a power for `p` only when `p` holds at
no world but `none`. Not monotone; an encoding artifact used only to show that
the monotonicity bridge is needed. -/
def onlyNonePower (_ : Option Bool) (y : Bg) (p : Option Bool → Prop) : Prop :=
  y = .g ∧ ∀ v, p v → v = none

/-- Non-Euclidean access `a → b`, `a → c`, `b → b` (ModalGrounding's `ptAccess`). -/
def ptFrame : CausalityFrame TruthCore.Modal.ModalGrounding.Model.Pt Bg Unit Bool :=
  gFrame TruthCore.Modal.ModalGrounding.Model.ptAccess
    (fun v x => x ≠ .d ∧ v ≠ .c) fun _ _ _ => False

end Model

open Model in
open TruthCore.Modal.PrussPowerPremises.Model (Bg allC gPower) in
/-- Controls for the scope of `0050b6ed`.

1. Nonvacuity: on the three-world frame with the possibility reading every
   premise of `actualAbsencePowerOfTotal` and its conclusion hold.
2. Strictness and productive compatibility: on §56's replacement frame with the
   possibility reading, `0050b6ed` holds with Euclidean access and monotone
   powers, its total-refraining sibling fails, the giver is necessarily
   productive and #1897's withholding holds.
3. Euclidean access needed: on the non-Euclidean frame the total sibling and
   monotonicity hold and `0050b6ed` fails.
4. Monotonicity needed: on the three-world frame with the maximally specific
   power the total sibling and Euclidean access hold and `0050b6ed` fails. -/
def ActualAbsencePowerScopeControls : Prop :=
  (GodsHoldTotalAbsencePower threeG (possibilityPower threeG) allC (· = .g) (some false) ∧
    TruthCore.Modal.Euclidean threeG.history.ontic.frame ∧
    PowerForMonotoneAt threeG (possibilityPower threeG) (some false) ∧
    GodsHoldActualAbsencePower threeG (possibilityPower threeG) allC (· = .g) (some false)) ∧
  (GodsHoldActualAbsencePower replGivingG (possibilityPower replGivingG) allC (· = .g) false ∧
    TruthCore.Modal.Euclidean replGivingG.history.ontic.frame ∧
    PowerForMonotoneAt replGivingG (possibilityPower replGivingG) false ∧
    ¬ GodsHoldTotalAbsencePower replGivingG (possibilityPower replGivingG) allC (· = .g) false ∧
    NecessarilyGivesSomeAt replGivingG false .g ∧
    ActualAbsenceByWithholding replGivingG (possibilityPower replGivingG) allC false) ∧
  (GodsHoldTotalAbsencePower ptFrame (possibilityPower ptFrame) allC (· = .g) .a ∧
    PowerForMonotoneAt ptFrame (possibilityPower ptFrame) .a ∧
    ¬ TruthCore.Modal.Euclidean ptFrame.history.ontic.frame ∧
    ¬ GodsHoldActualAbsencePower ptFrame (possibilityPower ptFrame) allC (· = .g) .a) ∧
  (GodsHoldTotalAbsencePower threeG onlyNonePower allC (· = .g) (some false) ∧
    TruthCore.Modal.Euclidean threeG.history.ontic.frame ∧
    ¬ PowerForMonotoneAt threeG onlyNonePower (some false) ∧
    ¬ GodsHoldActualAbsencePower threeG onlyNonePower allC (· = .g) (some false))

end TruthCore.Causality.SelectionScope
