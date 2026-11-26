module

public import TruthCore.Modal.OptimalCreationChoice

/-!
The comparison in #1955 fixes the producer and the feasible complete decisions.
Its rankings concern external effects, complete decisions and intrinsic perfection.
The obligation to maximize over decisions that meet due care is an additional premise.
-/

@[expose] public section

namespace TruthCore.Modal.CreationDecisionComparison

open TruthCore.Modal.OptimalCreationChoice (Optimal)

variable {S E A P : Type} [LT E] [LT A] [LT P] [Std.Irrefl (α := P) (· < ·)]

/-- Some feasible comparison has a strictly better outcome on this measure. -/
abbrev StrictVariation {V : Type} [LT V] (grade : S → V) :=
  ∃ i j, grade i < grade j

/-- Each strict improvement on the first measure is strict on the second
for that very pair of decisions, in the same direction. -/
abbrev PreservesImprovement {V W : Type} [LT V] [LT W] (fromGrade : S → V) (toGrade : S → W) :=
  ∀ i j, fromGrade i < fromGrade j → toGrade i < toGrade j

abbrev Invariant {V : Type} (grade : S → V) := ∀ i j, grade i = grade j

/-- A fixed intrinsic grade rules out a strict act improvement if act improvements
must carry over to the producer. This applies at any selected effect pair. -/
theorem noActImprovement {act : S → A} {intrinsic : S → P}
    (actToIntrinsic : PreservesImprovement act intrinsic) (fixed : Invariant intrinsic) (i j : S) :
    ¬ act i < act j := by
  intro h
  exact (irrefl (r := (· < ·)) _) ((fixed i j) ▸ actToIntrinsic i j h : intrinsic j < intrinsic j)

/-- Reflection through both comparisons gives a strict intrinsic improvement at
the original pair, contradicting invariance of that producer's intrinsic grade. -/
theorem reflectionObstruction {effect : S → E} {act : S → A} {intrinsic : S → P}
    (varies : StrictVariation effect) (effectToAct : PreservesImprovement effect act)
    (actToIntrinsic : PreservesImprovement act intrinsic) (fixed : Invariant intrinsic) : False := by
  obtain ⟨i, j, h⟩ := varies
  exact noActImprovement actToIntrinsic fixed i j (effectToAct i j h)

/-- The four rows of the omission table use these particular maps, including
the displayed choice of the third situation for the strict increase. -/
def threeGrades (a b c : Nat) : Fin 3 → Nat
  | 0 => a
  | 1 => b
  | 2 => c

theorem omissionControls :
    let flat := threeGrades 0 0 0
    let rises := threeGrades 0 0 1
    (¬ StrictVariation flat ∧ PreservesImprovement flat flat ∧
      PreservesImprovement flat flat ∧ Invariant flat) ∧
    (StrictVariation rises ∧ ¬ PreservesImprovement rises flat ∧
      PreservesImprovement flat flat ∧ Invariant flat) ∧
    (StrictVariation rises ∧ PreservesImprovement rises rises ∧
      ¬ PreservesImprovement rises flat ∧ Invariant flat) ∧
    (StrictVariation rises ∧ PreservesImprovement rises rises ∧
      PreservesImprovement rises rises ∧ ¬ Invariant rises) := by decide

/-- Execution and complete-decision grades can be exchanged while fixing the
effect grades. Each strict reflection can hold while the other fails. -/
theorem executionAndDecision :
    let effect := threeGrades 0 0 1
    (∃ execution decision : Fin 3 → Nat,
      PreservesImprovement effect execution ∧ ¬ PreservesImprovement effect decision) ∧
    (∃ execution decision : Fin 3 → Nat,
      ¬ PreservesImprovement effect execution ∧ PreservesImprovement effect decision) := by
  exact ⟨⟨threeGrades 0 0 1, threeGrades 0 0 0, by decide, by decide⟩,
    ⟨threeGrades 0 0 0, threeGrades 0 0 1, by decide, by decide⟩⟩

/-! The exhaustive three-situation, three-grade comparison. Each map is
generated once from its ordered triple. The counts concern these assignments. -/
private def gradeMaps : List (Fin 3 → Nat) := do
  let a ← List.range 3
  let b ← List.range 3
  let c ← List.range 3
  return threeGrades a b c

private structure Counts where
  total : Nat := 0
  allFour : Nat := 0
  withoutVariation : Nat := 0
  withoutEffectToAct : Nat := 0
  withoutActToIntrinsic : Nat := 0
  withoutInvariance : Nat := 0
  variableEffectFixedIntrinsic : Nat := 0
  variableEffectFixedIntrinsicWithEffectToAct : Nat := 0
  deriving BEq

private def counts : Counts := Id.run do
  let mut count : Counts := {}
  for effect in gradeMaps do
    let v := decide (StrictVariation effect)
    for act in gradeMaps do
      let ea := decide (PreservesImprovement effect act)
      for intrinsic in gradeMaps do
        let ap := decide (PreservesImprovement act intrinsic)
        let p := decide (Invariant intrinsic)
        count := {
          total := count.total + 1
          allFour := count.allFour + (v && ea && ap && p).toNat
          withoutVariation := count.withoutVariation + (!v && ea && ap && p).toNat
          withoutEffectToAct := count.withoutEffectToAct + (v && !ea && ap && p).toNat
          withoutActToIntrinsic := count.withoutActToIntrinsic + (v && ea && !ap && p).toNat
          withoutInvariance := count.withoutInvariance + (v && ea && ap && !p).toNat
          variableEffectFixedIntrinsic := count.variableEffectFixedIntrinsic + (v && p).toNat
          variableEffectFixedIntrinsicWithEffectToAct :=
            count.variableEffectFixedIntrinsicWithEffectToAct + (v && p && ea).toNat }
  return count

#guard counts == ⟨19683, 0, 27, 216, 288, 312, 1944, 288⟩

/-! Beneficiaries of the complete decision, and care actually given. -/
inductive Decision
  | refrain | createOne | careForBoth | neglectSecond
  deriving DecidableEq

inductive Recipient
  | first | second
  deriving DecidableEq

open Decision Recipient

def beneficiaries : Decision → List Recipient
  | refrain => []
  | createOne => [first]
  | careForBoth | neglectSecond => [first, second]

def caredFor : Decision → List Recipient
  | refrain => []
  | createOne | neglectSecond => [first]
  | careForBoth => [first, second]

def DueCare (d : Decision) : Prop := ∀ r ∈ beneficiaries d, r ∈ caredFor d

/-- O vacuously supplies each actual beneficiary's care. C has a particular
beneficiary whose due care is withheld. -/
theorem eligibility (d : Decision) : DueCare d ↔ d ≠ neglectSecond := by
  cases d <;> simp [DueCare, beneficiaries, caredFor]

/-- All four decisions are feasible. Among those satisfying due care, B
uniquely maximizes the supplied value. C's value is left entirely free. -/
theorem optimalEligible {V : Type} [PartialOrder V] (value : Decision → V)
    (omitBelowOne : value refrain < value createOne)
    (oneBelowBoth : value createOne < value careForBoth) (d : Decision) :
    Optimal {x | DueCare x} value d ↔ d = careForBoth := by
  have bothEligible := (eligibility careForBoth).2 (by decide)
  constructor
  · intro h
    have best : value careForBoth ≤ value d := h.2.2 ⟨careForBoth, bothEligible, rfl⟩
    cases d with
    | refrain => exact False.elim (not_le_of_gt (lt_trans omitBelowOne oneBelowBoth) best)
    | createOne => exact False.elim (not_le_of_gt oneBelowBoth best)
    | careForBoth => rfl
    | neglectSecond => exact False.elim ((eligibility _).1 h.1 rfl)
  · rintro rfl
    refine ⟨bothEligible, ⟨careForBoth, bothEligible, rfl⟩, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    cases x with
    | refrain => exact (lt_trans omitBelowOne oneBelowBoth).le
    | createOne => exact oneBelowBoth.le
    | careForBoth => exact le_rfl
    | neglectSecond => exact False.elim ((eligibility _).1 hx rfl)

end TruthCore.Modal.CreationDecisionComparison
