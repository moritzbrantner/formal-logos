module

public import TruthCore.Causality.MetricGrimReaper

/-!
# Fixed-duration station coverage

Analyst application alignment for #1489. One positive duration is supplied for
all descents and worlds; it does not assert arbitrary-speed devices. All four
register interfaces, history, accessibility and clock are inherited unchanged.
Station bearers and Ontic.Causes edges are conjoined to the register protocol
without binding them to it; host geometry and metaphysical realization are
not encoded.
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


/-- An actual causal station in a possible history, rather than a register-only
piece. Both neighboring bearers exist and are temporally present; the earlier
bearer causes the later one in that history; and the existing four signal
interfaces hold. Ontic.Causes is an individual-efficient-cause reading here,
NOT existential grounding or causation of the contingent totality. Nothing
in the type guarantees physically realizable devices or intrinsic powers.
The bearer conjuncts and PieceAt are conjoined with no bearer-register
binding: R.out and R.issues are indexed by moment, and nothing relates
stations n to them, so the Causes edge is not modelled signal transmission. -/
def StationOperationAt {W B T : Type} (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop)
    (stations : Nat → B) (u : W) (c : Nat → T) (n : Nat) :
    Prop :=
  Concrete (stations n) ∧
  Concrete (stations (n + 1)) ∧
  h.ontic.ExistsAt u (stations n) ∧
  h.ontic.ExistsAt u (stations (n + 1)) ∧
  h.IsAt u (stations n) (c n) ∧
  h.IsAt u (stations (n + 1)) (c (n + 1)) ∧
  h.ontic.Causes u (stations (n + 1)) (stations n) ∧
  PieceAt R u c n

/-- Each finite initial segment of actual operations has a possible witness.
The witnesses may differ with N. Crucially this does NOT assert one world with
all operations, nor that register contents agree between finite witnesses. -/
def FiniteStationPrefixCompatibility {W B T : Type} (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop)
    (stations : Nat → B) (v : W) (c : Nat → T) : Prop :=
  ∀ N, ∃ u, h.ontic.frame.access v u ∧
    ∀ n, n ≤ N → StationOperationAt R h Concrete stations u c n

/-- Only one d-separated schedule and concrete station family is required per
metrically infinite populated past. They may depend on the history and moment,
but are fixed across the finite-prefix witnesses of the chosen schedule. -/
def SelectedFiniteStationCompatibility {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ t, PopulatedAt h Concrete v t →
    ¬ MetricallyFinitePast k t →
    ∃ (c : Nat → T) (stations : Nat → B),
      c 0 = t ∧ Descent c ∧ DurationSlots k d c ∧
      FiniteStationPrefixCompatibility R h Concrete stations v c

/-- Explicit OPEN countable recombination principle. A single history
accessible from v must realize all ACTUAL operations, with the same station
identities, causal edges, port dictionary and signal rules as its locally
possible finite prefixes. This is strictly more content than preservation of
intrinsic abilities under duplication, and is not a theorem of finite
compatibility. Fixed duration is only a room condition; the physical source
of such host space, protection and calibration remains an open bridge.
Because arrangementImpossible excludes its consequent, it holds exactly when
no qualifying descent has finite-prefix-compatible station operations
(countableStationRecombinationIff in the results module). -/
def CountableStationRecombination {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ (c : Nat → T) (stations : Nat → B),
    Descent c → DurationSlots k d c → PopulatedAt h Concrete v (c 0) →
    FiniteStationPrefixCompatibility R h Concrete stations v c →
    ∃ u, h.ontic.frame.access v u ∧
      ∀ n, StationOperationAt R h Concrete stations u c n


/-! ## Concrete finite-prefix control

Unlike bare adjacent PieceAt compatibility, this assigns one bearer to each
station, stipulates a world-independent integer-succession relation as
Ontic.Causes between successive bearers, and requires world-relative station
existence and temporal presence. It is a STRUCTURAL SURROGATE: it witnesses
formal satisfiability under a stipulated relation, not causal coherence. No claim that arbitrary actual physics or
metaphysics realizes the entire network, or that bearer-to-bearer causation is
signal transmission, follows from this certificate. -/

namespace Control
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot pivotFrame)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.MetricGrimReaper.Control (intClock)

/-- Same integer history as pivot, with directed actual causes between
successive integer-addressed stations. No new time shape or existence
profile; the cause relation is intentionally distinct from esse grounding. -/
def causalPivot : History Int Int Int where
  ontic := { frame := pivot.ontic.frame,
             ExistsAt := pivot.ontic.ExistsAt,
             Causes := fun _ y x => y + 1 = x }
  IsAt := pivot.IsAt
  now := pivot.now

def stationMoments (n : Nat) : Int := -(n : Int)
def oneDuration : {d : ℝ // 0 < d} := ⟨1, one_pos⟩

/-- The concrete integer-world finite-prefix model will have stations
operating in every finite initial segment, yet no accessible history
realizing all operations. The latter follows from the previous global
Reaper impossibility theorem; it is not a new contradiction proof. -/
def CausalFinitePrefixCertificate : Prop :=
  PopulatedAt causalPivot all 1 0 ∧
  ¬ MetricallyFinitePast intClock 0 ∧
  DurationSlots intClock oneDuration stationMoments ∧
  FiniteStationPrefixCompatibility pivotFrame causalPivot all stationMoments
    1 stationMoments ∧
  ¬ (∃ u, causalPivot.ontic.frame.access 1 u ∧
        ∀ n, StationOperationAt pivotFrame causalPivot all stationMoments
          u stationMoments n)

end Control

end TruthCore.Causality.FixedDurationGrimReaper
