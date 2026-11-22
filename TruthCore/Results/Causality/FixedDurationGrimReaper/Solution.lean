module

public import TruthCore.Causality.FixedDurationGrimReaper
public import TruthCore.Results.Causality.MetricGrimReaper.Solution

@[expose] public section

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
  cases input with
  | none => simp [guardedStep]
  | some j =>
    by_cases hj : n ≤ j <;> simp [guardedStep, hj]

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
  cases input with
  | none =>
    simp [guardedStep] at hUpstream hOutput hIssue
    refine ⟨fun _ => hIssue, fun _ => hOutput, ?_, ?_⟩
    · intro r hr
      rw [hUpstream] at hr
      cases hr
    · intro r hr
      rw [hOutput] at hr
      cases hr
      exact ⟨n, le_refl _, rfl⟩
  | some j =>
    have hj : n + 1 ≤ j := hInput j rfl
    have hnj : n ≤ j := Nat.le_trans (Nat.le_succ n) hj
    simp [guardedStep, hnj] at hUpstream hOutput hIssue
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hr
      rw [hUpstream] at hr
      cases hr
    · intro hi
      exact False.elim (hIssue hi)
    · intro r hr
      rw [hUpstream] at hr
      cases hr
      exact hOutput
    · intro r hr
      rw [hOutput] at hr
      cases hr
      exact ⟨j, hnj, rfl⟩

/-- Thin an existing unbounded descent by selecting moments below the preceding
reading minus d. The supplied clock and the first moment remain unchanged. -/
theorem durationDescentOfUnbounded {T : Type} [LinearOrder T] (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (t : T) (hInf : ¬ MetricallyFinitePast k t) :
    ∃ c : Nat → T, c 0 = t ∧ Descent c ∧ DurationSlots k d c := by
  obtain ⟨seed, _, _, hSlots⟩ := spacedDescentOfUnbounded k t hInf
  have hBelow : ∀ x : T, ∃ n, k.reading (seed n) < k.reading x - d.1 :=
    fun x => readingsUnbounded k seed hSlots (k.reading x - d.1)
  choose pick hLt using hBelow
  let c : Nat → T := fun n => Nat.rec t (fun _ x => seed (pick x)) n
  have hRead : ∀ n, k.reading (c (n + 1)) < k.reading (c n) - d.1 :=
    fun n => hLt (c n)
  refine ⟨c, rfl, ?_, ?_⟩
  · intro n
    apply k.strictMono.lt_iff_lt.mp
    linarith [hRead n, d.property]
  · intro n
    linarith [hRead n]

theorem durationPiecesOfSpaced {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W)
    (hPieces : SpacedReaperPiecesPossible R h Concrete k w) :
    DurationPiecesPossible R h Concrete k d w := by
  intro v hv c hDesc hSlots hPop
  exact hPieces v hv c hDesc ⟨d.1, d.property, hSlots⟩ hPop

theorem durationPatchworkOfSpaced {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (d : {d : ℝ // 0 < d}) (w : W)
    (hPatch : SpacedReaperPatchwork R h Concrete k w) :
    DurationPatchwork R h Concrete k d w := by
  intro v hv c hDesc hSlots hPop hLocal
  exact hPatch v hv c hDesc ⟨d.1, d.property, hSlots⟩ hPop hLocal

theorem durationDescentOfPieces {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hPieces : DurationPiecesPossible R h Concrete k d w) :
    DurationDescentPossible R h Concrete k d w := by
  intro v hv t hPop hInf
  obtain ⟨c, hc0, hDesc, hSlots⟩ := durationDescentOfUnbounded k d t hInf
  refine ⟨c, hc0, hDesc, hSlots, ?_⟩
  exact hPieces v hv c hDesc hSlots (hc0.symm ▸ hPop)

theorem metricallyFiniteOfDurationDescent {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hLocal : DurationDescentPossible R h Concrete k d w)
    (hPatch : DurationPatchwork R h Concrete k d w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  intro v hv x t hx hCont hAt
  by_contra hInf
  have hPop : PopulatedAt h Concrete v t := ⟨x, hx, hCont, hAt⟩
  obtain ⟨c, hc0, hDesc, hSlots, hPieces⟩ := hLocal v hv t hPop hInf
  obtain ⟨u, _, hAll⟩ := hPatch v hv c hDesc hSlots (hc0.symm ▸ hPop) hPieces
  exact TruthCore.Results.Causality.GrimReaperPatchwork.arrangementImpossible
    R u c hDesc hAll

theorem metricallyFiniteOfDurationPieces {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hPieces : DurationPiecesPossible R h Concrete k d w)
    (hPatch : DurationPatchwork R h Concrete k d w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  exact metricallyFiniteOfDurationDescent R h Concrete k d w
    (durationDescentOfPieces R h Concrete k d w hPieces) hPatch


/-- Actual finite-prefix station witnesses imply the existing locally
co-possible Reaper interfaces. No causal relation is discarded when defining
the stronger StationOperationAt; this projection only uses its register field. -/
theorem finiteStationPrefixesGiveAdjacent {W B T : Type}
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (stations : Nat → B) (v : W) (c : Nat → T)
    (hFinite : FiniteStationPrefixCompatibility R h Concrete stations v c) :
    AdjacentPiecesCoPossible R h v c := by
  intro n
  obtain ⟨u, huv, hOps⟩ := hFinite (n + 1)
  obtain ⟨_, _, _, _, _, _, _, hn⟩ := hOps n (Nat.le_succ n)
  obtain ⟨_, _, _, _, _, _, _, hn1⟩ := hOps (n + 1) (Nat.le_refl _)
  exact ⟨u, huv, hn, hn1⟩

/-- Concrete finite-prefix compatibility yields the existing weaker
selected-descent local premise, reusing its own history and clock. -/
theorem durationDescentOfStationPrefixes {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hLocal : SelectedFiniteStationCompatibility R h Concrete k d w) :
    DurationDescentPossible R h Concrete k d w := by
  intro v hv t hPop hInf
  obtain ⟨c, stations, hc, hDesc, hSlots, hFinite⟩ :=
    hLocal v hv t hPop hInf
  exact ⟨c, hc, hDesc, hSlots,
    finiteStationPrefixesGiveAdjacent R h Concrete stations v c hFinite⟩

/-- Stronger, genuinely causal interpretation of fixed-duration patchwork:
if every infinite populated past admits one finite-prefix compatible family of
actual station operations, and countable recombination preserves their
existence, temporal presence, causal edges and signal behavior in one world,
then that past has finite metric duration. The original Reaper contradiction
is imported, not reproduced. The two modal commitments remain OPEN. -/
theorem metricallyFiniteOfCountableStationRecombination {W B T : Type}
    [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop)
    (k : TimeClock T) (d : {d : ℝ // 0 < d}) (w : W)
    (hLocal : SelectedFiniteStationCompatibility R h Concrete k d w)
    (hGlue : CountableStationRecombination R h Concrete k d w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  intro v hv x t hx hCont hAt
  by_contra hInfinite
  have hPop : PopulatedAt h Concrete v t := ⟨x, hx, hCont, hAt⟩
  obtain ⟨c, stations, hc, hDesc, hSlots, hFinite⟩ :=
    hLocal v hv t hPop hInfinite
  have hPopC : PopulatedAt h Concrete v (c 0) := hc.symm ▸ hPop
  obtain ⟨u, _, hOps⟩ :=
    hGlue v hv c stations hDesc hSlots hPopC hFinite
  have hPieces : ∀ n, PieceAt R u c n := by
    intro n
    obtain ⟨_, _, _, _, _, _, _, hPiece⟩ := hOps n
    exact hPiece
  exact TruthCore.Results.Causality.GrimReaperPatchwork.arrangementImpossible
    R u c hDesc hPieces

/-- A structural separation: every finite prefix of an unbounded sequence can
be contained in some finite bound, but there is no bound containing all n.
This witnesses the distinct LOGICAL content of finite vs countable assembly,
not a metaphysically possible Reaper network or an objection to recombination. -/
theorem finitePrefixNotCountable :
    (∀ N : Nat, ∃ bound : Nat, ∀ n, n ≤ N → n < bound) ∧
    ¬ (∃ bound : Nat, ∀ n, n < bound) := by
  constructor
  · intro N
    exact ⟨N + 1, fun _ hn => Nat.lt_succ_of_le hn⟩
  · rintro ⟨bound, hb⟩
    exact Nat.lt_irrefl bound (hb bound)

end TruthCore.Results.Causality.FixedDurationGrimReaper
