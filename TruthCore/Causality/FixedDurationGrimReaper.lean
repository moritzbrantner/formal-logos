module

public import TruthCore.Causality.MetricGrimReaper

/-!
# Fixed-duration station coverage

Analyst application alignment for #1489. One positive duration is supplied for
all descents and worlds; it does not assert arbitrary-speed devices. All four
register interfaces, history, accessibility and clock are inherited unchanged.
No concrete station, host geometry or metaphysical realization is encoded.
-/

@[expose] public section

namespace TruthCore.Causality.FixedDurationGrimReaper

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.GrimReaperPatchwork
open TruthCore.Causality.MetricGrimReaper

/-- Every slot lasts at least the one supplied positive duration. -/
def DurationSlots {T : Type} [Preorder T] (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (c : Nat → T) : Prop :=
  ∀ n, d.1 ≤ k.reading (c n) - k.reading (c (n + 1))

/-- One total local recipe, parameterized by the station's supplied address.
The rejecting branch is normal error handling, not forwarding of an alien code. -/
def guardedStep (n : Nat) : Option Nat → Bool × Option Nat
  | none => (true, some n)
  | some j => if n ≤ j then (false, some j) else (false, none)

/-- Local coverage of all descents with enough temporal duration for a fixed
station patch. Spatial room and actual station realization remain OPEN. -/
def DurationPiecesPossible {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c →
    DurationSlots k d c → PopulatedAt h Concrete v (c 0) →
    AdjacentPiecesCoPossible R h v c

/-- Patchwork coverage only for descents with slots at least the supplied d. -/
def DurationPatchwork {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c →
    DurationSlots k d c → PopulatedAt h Concrete v (c 0) →
    AdjacentPiecesCoPossible R h v c → ArrangementPossible R h v c

/-- Weaker local coverage: each metrically infinite populated past need supply
only one fixed-duration descent with co-possible adjacent pieces. It need not
supply pieces along every sufficiently spaced descent. -/
def DurationDescentPossible {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ t, PopulatedAt h Concrete v t →
    ¬ MetricallyFinitePast k t →
    ∃ c : Nat → T, c 0 = t ∧ Descent c ∧ DurationSlots k d c ∧
      AdjacentPiecesCoPossible R h v c

end TruthCore.Causality.FixedDurationGrimReaper
