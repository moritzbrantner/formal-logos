module

public import TruthCore.Case.Catholicism.CausalPerfectionTransfer

/-! Analyst test of comparative predication. Integer readings have a common
unit and orientation. A named source's two increments are independently
assigned to the selected operation. Removing them keeps both bearers present
and all other inputs fixed. This controlled omission need not be an available
withdrawal of a universal cause. -/

@[expose] public section
namespace TruthCore.Causality.ComparativeFoundation

/-- For offset zero this compares the two readings themselves. The signed
offset also permits testing a family of comparison thresholds. -/
structure Pair where
  left : Int
  right : Int

def Pair.below (p : Pair) (offset : Int) : Prop := p.left + offset < p.right

/-- The residual pair keeps everything except the selected source input.
It may differ from the earlier observed pair. -/
structure Run where
  residual : Pair
  leftInput : Int
  rightInput : Int

def Run.actual (w : Run) : Pair :=
  ⟨w.residual.left + w.leftInput, w.residual.right + w.rightInput⟩

/-- Includes both acquisition and loss under the comparison with the residual.
All thresholds are blind to the input exactly when it translates both readings
equally. This is a fact about the selected contrasts. -/
def ThresholdCharacterization : Prop :=
  ∀ w : Run,
    (∀ k,
      ((¬ w.residual.below k ∧ w.actual.below k) ↔
        w.residual.right - w.residual.left ≤ k ∧ k < w.actual.right - w.actual.left) ∧
      ((w.residual.below k ∧ ¬ w.actual.below k) ↔
        w.actual.right - w.actual.left ≤ k ∧ k < w.residual.right - w.residual.left)) ∧
    ((∀ k, w.residual.below k ↔ w.actual.below k) ↔ w.leftInput = w.rightInput)

namespace Rods
open TruthCore.Case.Catholicism (TransferRole UniversalCauseTransfersPerfections)
open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus)

/-- The receiver is the fixed rod and the supporter the extending rod. The
two control settings assign the same two-unit extension to different drivers.
Neither the driver nor its operation is inferred from the final lengths. -/
def before : Pair := ⟨2, 1⟩

def after (driver : TransferRole) (excluded : Option TransferRole) : Pair :=
  ⟨before.left, before.right + (if excluded = some driver then 0 else 2)⟩

inductive Respect | esse | shorterThanExtending | longerThanFixed

def inAct (driver : TransferRole) (x : TransferRole) : Respect → Prop
  | .esse => True
  | .shorterThanExtending => x = .recipient ∧ (after driver none).below 0
  | .longerThanFixed => x = .supporter ∧ (after driver none).right > (after driver none).left

/-- A deliberately restricted interpretation at the two comparative respects:
changing the reading from false to true when the actual input is reinstated.
This does not define efficient causal responsibility for all purposes. -/
def diagnostic (driver a x : TransferRole) : Respect → Prop
  | .esse => a = .source ∧ x ≠ .source
  | .shorterThanExtending => inAct driver x .shorterThanExtending ∧
      ¬ (after driver (some a)).below 0
  | .longerThanFixed => inAct driver x .longerThanFixed ∧
      ¬ (after driver (some a)).right > (after driver (some a)).left

def transfer (driver : TransferRole) : Prop :=
  UniversalCauseTransfersPerfections (inAct driver) (diagnostic driver) .esse

/-- A source can add the same nonzero amount to both already comparable
readings. Such an addition reaches each foundation and is invisible to every
offset comparison. Whether this source is productively responsible for the
foundations in reality is an interpretation premise. -/
def common : Run := ⟨⟨2, 3⟩, 1, 1⟩

def Controls : Prop :=
  (∀ driver : TransferRole,
    CausesAllInGenus (inAct driver) (diagnostic driver) .esse .source ∧
    (after driver none).left = before.left ∧ (after driver none).right = 3 ∧
    ¬ before.below 0 ∧ (after driver none).below 0 ∧
    diagnostic driver driver .recipient .shorterThanExtending ∧
    diagnostic driver driver .supporter .longerThanFixed) ∧
  (transfer .source ∧ ¬ transfer .producer ∧
    ¬ diagnostic .producer .source .recipient .shorterThanExtending) ∧
  (common.actual.left ≠ common.residual.left ∧ common.actual.right ≠ common.residual.right ∧
    ∀ k, common.residual.below k ↔ common.actual.below k)

end Rods
end TruthCore.Causality.ComparativeFoundation
