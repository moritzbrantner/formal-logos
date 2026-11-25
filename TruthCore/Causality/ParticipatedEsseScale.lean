module

public import Mathlib.Order.Bounds.Basic
public import TruthCore.Causality.SoleEsseGiver

/-! An analyst test of represented adequacy at participated esse. A common
scale values independently identified pure determinations. Source possession
and calibration to the bearer's own esse are separate open hypotheses. -/

@[expose] public section
namespace TruthCore.Causality.ParticipatedEsseScale

open TruthCore.Causality.EsseCauseEfficiency (EfficiencyProfile)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4 (Profile)

variable {B P R A D : Type}

/-- Levels witnessed by a bearer's real determinations in the selected inventory. -/
def realizedLevels (Pure : A → Prop) (Has : B → A → Prop) (level : A → D) (b : B) : Set D :=
  {v | ∃ a, Pure a ∧ Has b a ∧ level a = v}

/-- Total efficient giving to a participant communicates only pure determinations
in the selected inventory already realized in the giver. The inventory can be
much narrower than the roster of all the recipient's properties. -/
def GivingPreservesDeterminations (q : EfficiencyProfile B P R)
    (Participated : B → Prop) (Total : B → B → R → Prop)
    (Pure : A → Prop) (Has : B → A → Prop) : Prop :=
  ∀ c x, q.InAct x q.esse → Participated x → q.EfficientlyCausesEsse c x →
    Total c x q.esse → ∀ a, Pure a → Has x a → Has c a

/-- The bearer's own represented degree is the least upper bound of the levels
of the admitted determinations it realizes. The level assignment is common to
all bearers; it takes neither the causal edge nor the bearer's degree as input. -/
def OwnDegreeFromRealizedLevels [Preorder D] (f : Profile B P R)
    (Pure : A → Prop) (Has : B → A → Prop) (level : A → D) (degree : R → B → D) : Prop :=
  ∀ b, f.InAct b f.esse → IsLUB (realizedLevels Pure Has level b) (degree f.esse b)

/-- Two input channels can pass through separately or be routed into one port. -/
def route (combine : Bool) (input : Nat × Nat) : Nat × Nat :=
  if combine then (input.1 + input.2, 0) else input

/-- A local detector fires if one port receives at least k units. -/
def detected (ports : Nat × Nat) (k : Nat) : Prop := k ≤ ports.1 ∨ k ≤ ports.2

/-- Both output configurations use the entire supplied quantity. The pass-through
ties the input on every local test. Concentration raises the calibrated peak,
and the failed test has the independently specified witness 2n. -/
def ChannelControl : Prop :=
  ∀ n : Nat, 0 < n →
    let input := (n, n)
    let straight := route false input
    let combined := route true input
    straight.1 + straight.2 = input.1 + input.2 ∧
    combined.1 + combined.2 = input.1 + input.2 ∧
    (∀ k, detected straight k ↔ detected input k) ∧
    IsLUB {k | detected input k} n ∧ IsLUB {k | detected straight k} n ∧
    IsLUB {k | detected combined k} (n + n) ∧
    n < n + n ∧ detected combined (n + n) ∧ ¬ detected input (n + n)

end TruthCore.Causality.ParticipatedEsseScale
