import TruthCore.Causality.FixedDurationGrimReaper
import TruthCore.Results.Causality.MetricGrimReaper.Solution

namespace TruthCore.Results.Causality.FixedDurationGrimReaper

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.GrimReaperPatchwork
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.FixedDurationGrimReaper
open TruthCore.Results.Causality.MetricGrimReaper

/-- Every output from the guarded recipe has an address at least n. This
range property alone does not claim that the named station actually issued. -/
theorem guardedOutputAdmissible (n : Nat) (input : Option Nat) :
    ∀ j, (guardedStep n input).2 = some j → n ≤ j := by
  sorry

/-- A faithful connected guarded input/output at one station gives the actual
four-interface PieceAt, provided the upstream port supplies its address bound.
No countable coexistence or concrete realization is asserted. -/
theorem pieceOfGuardedPort {W T : Type} (R : ReaperFrame W T) (u : W)
    (c : Nat → T) (n : Nat) (input : Option Nat)
    (hInput : ∀ j, input = some j → n + 1 ≤ j)
    (hUpstream : R.out u (c (n + 1)) = input.map c)
    (hOutput : R.out u (c n) = ((guardedStep n input).2).map c)
    (hIssue : R.issues u (c n) ↔ (guardedStep n input).1 = true) :
    PieceAt R u c n := by
  sorry

/-- Thin an existing unbounded descent by selecting moments below the preceding
reading minus d. The supplied clock and the first moment remain unchanged. -/
theorem durationDescentOfUnbounded {T : Type} [LinearOrder T] (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (t : T) (hInf : ¬ MetricallyFinitePast k t) :
    ∃ c : Nat → T, c 0 = t ∧ Descent c ∧ DurationSlots k d c := by
  sorry

theorem durationPiecesOfSpaced {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W)
    (hPieces : SpacedReaperPiecesPossible R h Concrete k w) :
    DurationPiecesPossible R h Concrete k d w := by
  sorry

theorem durationPatchworkOfSpaced {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W)
    (hPatch : SpacedReaperPatchwork R h Concrete k w) :
    DurationPatchwork R h Concrete k d w := by
  sorry

theorem durationDescentOfPieces {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hPieces : DurationPiecesPossible R h Concrete k d w) :
    DurationDescentPossible R h Concrete k d w := by
  sorry

theorem metricallyFiniteOfDurationDescent {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hLocal : DurationDescentPossible R h Concrete k d w)
    (hPatch : DurationPatchwork R h Concrete k d w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  sorry

theorem metricallyFiniteOfDurationPieces {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hPieces : DurationPiecesPossible R h Concrete k d w)
    (hPatch : DurationPatchwork R h Concrete k d w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  sorry

theorem durationDescentOfStationPrefixes {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hLocal : SelectedFiniteStationCompatibility R h Concrete k d w) :
    DurationDescentPossible R h Concrete k d w := by
  sorry

theorem metricallyFiniteOfCountableStationRecombination {W B T : Type}
    [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hLocal : SelectedFiniteStationCompatibility R h Concrete k d w)
    (hGlue : CountableStationRecombination R h Concrete k d w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  sorry

theorem finiteStationPrefixesGiveAdjacent {W B T : Type}
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (stations : Nat → B) (v : W) (c : Nat → T)
    (hFinite : FiniteStationPrefixCompatibility R h Concrete stations v c) :
    AdjacentPiecesCoPossible R h v c := by
  sorry


theorem pivotFinitePrefixPiece (N n : Nat) (hn : n ≤ N) :
    PieceAt pivotFrame (stationMoments (N + 1)) stationMoments n := by
  sorry


theorem causalFinitePrefixCompatibility :
    FiniteStationPrefixCompatibility pivotFrame causalPivot all stationMoments
      1 stationMoments := by
  sorry


theorem causalFinitePrefixControls : CausalFinitePrefixCertificate := by
  sorry


end TruthCore.Results.Causality.FixedDurationGrimReaper
