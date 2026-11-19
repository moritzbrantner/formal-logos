module

public import TruthCore.Explanation.NoFoundationLawChaos

@[expose] public section

namespace TruthCore.Results.Explanation.NoFoundationLawChaos
open TruthCore.Explanation.NoFoundationLawChaos
open TruthCore.Modern.Hume.Induction
open TruthCore.Modern.Hume.Regularity
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Explanation.LawActuality
open TruthCore.Modal.TemporalHistory
open TruthCore.Modal.HistoryContrastive

private theorem cell_iff_prefix (n : Nat) (f : Trace) :
    Cell (openFuture n) on n f ↔ ∀ i, i < n+1 → f i = true := by
  constructor
  · intro hf i hi
    exact hf.2 i hi
  · intro hp
    refine ⟨⟨hp 0 (by omega), ?_⟩, ?_⟩
    · intro t ht
      exact (hp (t+1) ht).trans (hp t (by omega)).symm
    · intro i hi
      exact hp i hi

private theorem splice_before (n : Nat) (tail : Trace) (i : Nat)
    (hi : i < n+1) : splice n tail i = true := by
  simp [splice, hi]

private theorem splice_after (n : Nat) (tail : Trace) (i : Nat)
    (hi : n+1 ≤ i) : splice n tail i = tail i := by
  simp [splice, show ¬ i < n+1 by omega]

private theorem all_splices (n : Nat) (tail : Trace) :
    Cell (openFuture n) on n (splice n tail) := by
  apply (cell_iff_prefix n _).2
  intro i hi
  exact splice_before n tail i hi

private theorem populated_pair (n k : Nat) (hk : n+1 ≤ k) :
    ∃ f g : Trace,
      Cell (openFuture n) on n f ∧ Cell (openFuture n) on n g ∧
      (∀ i, i < n+1 → f i = g i) ∧ f k ≠ g k ∧
      ¬ SameHistory realized f g := by
  let f : Trace := splice n (fun _ => true)
  let g : Trace := splice n (fun _ => false)
  have hf : Cell (openFuture n) on n f := all_splices n _
  have hg : Cell (openFuture n) on n g := all_splices n _
  have heq : ∀ i, i < n+1 → f i = g i := by
    intro i hi
    rw [show f i = true from splice_before n _ i hi,
      show g i = true from splice_before n _ i hi]
  have hfk : f k = true := splice_after n _ k hk
  have hgk : g k = false := splice_after n _ k hk
  have hneq : f k ≠ g k := by
    rw [hfk, hgk]
    decide
  have hhist : ¬ SameHistory realized f g := by
    intro hs
    have hh := (hs true k).mp (show realized.IsAt f true k from hfk.symm)
    change true = g k at hh
    rw [hgk] at hh
    exact Bool.noConfusion hh
  exact ⟨f, g, hf, hg, heq, hneq, hhist⟩

private theorem no_uniform_forecast (n k : Nat) (p : Profile)
    (predict : Trace → Bool) (hk : n+1 ≤ k)
    (hcomplete : SuffixComplete p n) (hrecord : UsesRecord n predict) :
    ¬ UniformForecast p n k predict := by
  intro huniform
  let f : Trace := splice n (fun _ => true)
  let g : Trace := splice n (fun _ => false)
  have hf : Cell p on n f := hcomplete _
  have hg : Cell p on n g := hcomplete _
  have heq : ∀ i, i < n+1 → f i = g i := by
    intro i hi
    rw [show f i = true from splice_before n _ i hi,
      show g i = true from splice_before n _ i hi]
  have hfk : f k = true := splice_after n _ k hk
  have hgk : g k = false := splice_after n _ k hk
  have hfirst : predict f = true := (huniform f hf).trans hfk
  have hsecond : predict g = false := (huniform g hg).trans hgk
  have hsame := hrecord f g heq
  exact Bool.noConfusion (hfirst.symm.trans (hsame.trans hsecond))

private theorem arbitrary_pair (n t : Nat) (a b : Bool) (ht : n+1 ≤ t) :
    ∃ tail : Trace, splice n tail t = a ∧ splice n tail (t+1) = b := by
  let tail : Trace := fun i => if i = t then a else if i = t+1 then b else true
  refine ⟨tail, ?_, ?_⟩
  · rw [splice_after n tail t ht]
    simp [tail]
  · rw [splice_after n tail (t+1) (by omega)]
    have hne : t+1 ≠ t := by omega
    simp [tail, hne]

private theorem future_total (n : Nat) (p q : Profile)
    (hcomplete : SuffixComplete p n) (huniversal : UniversalProjection p q n) :
    ∀ t a b, n+1 ≤ t → q.step t a b := by
  intro t a b ht
  obtain ⟨tail, ha, hb⟩ := arbitrary_pair n t a b ht
  have hstep := (huniversal (splice n tail) (hcomplete tail)).2 t
  simpa only [ha, hb] using hstep

private theorem no_future_exclusion (n : Nat) (p q : Profile)
    (hcomplete : SuffixComplete p n) (hbad : FutureExclusion q n) :
    ¬ UniversalProjection p q n := by
  intro huniversal
  obtain ⟨t, a, b, ht, hnot⟩ := hbad
  exact hnot (future_total n p q hcomplete huniversal t a b ht)

private theorem no_deterministic_projection (n : Nat) (p q : Profile)
    (hcomplete : SuffixComplete p n) (hdet : Deterministic q) :
    ¬ UniversalProjection p q n := by
  intro huniversal
  have hall := future_total n p q hcomplete huniversal
  have htrue := hall (n+1) true true (Nat.le_refl _)
  have hfalse := hall (n+1) true false (Nat.le_refl _)
  exact Bool.noConfusion (hdet (n+1) true true false htrue hfalse)

private theorem projection_characterization (n : Nat) (q : Profile) :
    UniversalProjection (openFuture n) q n ↔
      q.initial = true ∧
      (∀ t, t < n → q.step t true true) ∧
      (∀ b, q.step n true b) ∧
      (∀ t a b, n+1 ≤ t → q.step t a b) := by
  constructor
  · intro huniversal
    have hon : Cell (openFuture n) on n on :=
      (cell_iff_prefix n on).2 (fun _ _ => rfl)
    have hpath : Follows q on := huniversal on hon
    refine ⟨hpath.1.symm, ?_, ?_, ?_⟩
    · intro t _
      exact hpath.2 t
    · intro b
      have hstep := (huniversal (splice n (fun _ => b)) (all_splices n _)).2 n
      have ha : splice n (fun _ => b) n = true :=
        splice_before n _ n (by omega)
      have hb : splice n (fun _ => b) (n+1) = b :=
        splice_after n _ (n+1) (Nat.le_refl _)
      simpa only [ha, hb] using hstep
    · exact future_total n (openFuture n) q (all_splices n) huniversal
  · rintro ⟨hinitial, hpast, hboundary, hfuture⟩ f hf
    refine ⟨?_, ?_⟩
    · exact (hf.2 0 (by omega)).trans hinitial.symm
    · intro t
      by_cases ht : t < n
      · have ha : f t = true := hf.2 t (by omega)
        have hb : f (t+1) = true := hf.2 (t+1) (by omega)
        rw [ha, hb]
        exact hpast t ht
      · by_cases he : t = n
        · subst t
          have ha : f n = true := hf.2 n (by omega)
          rw [ha]
          exact hboundary (f (n+1))
        · exact hfuture t (f t) (f (t+1)) (by omega)

/-- Any whole-path invariant above an unrestricted suffix loses all
substantive future transition exclusions. These are conditional mathematical
consequences, not an empirical claim that the future really is unrestricted. -/
theorem certificate : Certificate := by
  refine ⟨cell_iff_prefix, ?_, ?_, populated_pair,
    no_uniform_forecast, future_total, no_future_exclusion,
    no_deterministic_projection, projection_characterization⟩
  · intro n tail
    exact all_splices n tail
  · exact ⟨fun _ _ => Iff.rfl,
      fun f t => ⟨f t, rfl, fun _ hy => hy⟩⟩

private theorem generated_follows (switches : Nat → Bool) :
    Follows (scheduled switches) (generated switches) := by
  exact ⟨rfl, fun _ => rfl⟩

private theorem generated_unique (switches : Nat → Bool) (f : Trace)
    (hf : Follows (scheduled switches) f) : f = generated switches := by
  funext t
  induction t with
  | zero => exact hf.1
  | succ t ih =>
      calc
        f (t+1) = (if switches t then !(f t) else f t) := hf.2 t
        _ = (if switches t then !(generated switches t)
             else generated switches t) := by rw [ih]
        _ = generated switches (t+1) := rfl

private theorem extracted_follows (f : Trace) (h0 : f 0 = true) :
    Follows (scheduled (scheduleOf f)) f := by
  refine ⟨h0, ?_⟩
  intro t
  cases ha : f t <;> cases hb : f (t+1) <;>
    simp [scheduled, scheduleOf, ha, hb]

private theorem copy_all (t : Nat) : generated copySchedule t = true := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (if copySchedule t then !(generated copySchedule t)
        else generated copySchedule t) = true
      simpa [copySchedule] using ih

private theorem toggle_prefix (k : Nat) :
    ∀ i, i ≤ k → generated (toggleFrom k) i = true := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hle
      have hfalse : toggleFrom k i = false := by
        simp [toggleFrom, show ¬ k ≤ i by omega]
      change (if toggleFrom k i then !(generated (toggleFrom k) i)
        else generated (toggleFrom k) i) = true
      rw [hfalse]
      exact ih (by omega)

private theorem toggle_first (k : Nat) :
    generated (toggleFrom k) (k+1) = false := by
  change (if toggleFrom k k then !(generated (toggleFrom k) k)
    else generated (toggleFrom k) k) = false
  rw [show toggleFrom k k = true by simp [toggleFrom],
    toggle_prefix k k (Nat.le_refl _)]
  rfl

private theorem toggle_cell (n k : Nat) (hk : n ≤ k) :
    Cell (openFuture n) on n (generated (toggleFrom k)) := by
  apply (cell_iff_prefix n _).2
  intro i hi
  exact toggle_prefix k i (by omega)

private theorem copy_cell (n : Nat) :
    Cell (openFuture n) on n (generated copySchedule) := by
  apply (cell_iff_prefix n _).2
  intro i _
  exact copy_all i

/-- The transition schedule can switch from copying to toggling at any date
later than the observed window, even when both individually deterministic
laws admit uniquely determined whole traces. Ex-post extraction is not a
source-independent governing law. -/
theorem lawSwitch : LawSwitch := by
  refine ⟨?_, extracted_follows, ?_⟩
  · intro switches
    refine ⟨?_, generated_follows switches, generated_unique switches⟩
    intro t a b c hb hc
    exact hb.trans hc.symm
  · intro n k hk
    refine ⟨toggle_cell n k hk, copy_cell n, ?_, ?_, ?_, toggle_first k,
      copy_all (k+1)⟩
    · intro t ht a b
      have hcopy : toggleFrom k t = false := by
        simp [toggleFrom, show ¬ k ≤ t by omega]
      simp [scheduled, copySchedule, hcopy]
    · change true = if copySchedule k then !(true : Bool) else true
      simp [copySchedule]
    · change ¬ true = if toggleFrom k k then !(true : Bool) else true
      simp [toggleFrom]

private theorem fixed_complete (n : Nat) : SuffixComplete unconstrained n := by
  intro tail
  refine ⟨⟨splice_before n tail 0 (by omega), fun _ => trivial⟩, ?_⟩
  intro i hi
  exact splice_before n tail i hi

/-- Unlike the cutoff-indexed `openFuture n` construction, this quantifies
over one and the same rival class for ALL finite observation windows. Every
admitted history can be written as a deterministic but potentially changing
copy/toggle schedule, which is extracted only after knowing its full path. -/
theorem oneRival : OneRival := by
  have scheduled_iff : ∀ f : Trace,
      f 0 = true ↔ ∃ switches, Follows (scheduled switches) f := by
    intro f
    constructor
    · intro h0
      exact ⟨scheduleOf f, extracted_follows f h0⟩
    · rintro ⟨switches, hf⟩
      exact hf.1
  refine ⟨scheduled_iff, fixed_complete, ?_, ?_⟩
  · intro n f
    constructor
    · intro hf
      exact ⟨(scheduled_iff f).mp hf.1.1, hf.2⟩
    · rintro ⟨hschedule, hpast⟩
      exact ⟨⟨(scheduled_iff f).mpr hschedule, fun _ => trivial⟩, hpast⟩
  · intro n q hdet
    exact no_deterministic_projection n unconstrained q (fixed_complete n) hdet

private theorem stable_cell (n : Nat) : Cell stable on n on :=
  ⟨⟨rfl, fun _ => rfl⟩, fun _ _ => rfl⟩

private theorem stable_det : Deterministic stable := by
  intro _ _ _ _ hb hc
  exact hb.trans hc.symm

private theorem stable_not_complete (n : Nat) : ¬ SuffixComplete stable n := by
  intro hcomplete
  exact no_deterministic_projection n stable stable hcomplete stable_det
    (fun _ hf => hf.1)

private theorem on_in_open (n : Nat) : Cell (openFuture n) on n on :=
  (cell_iff_prefix n on).2 (fun _ _ => rfl)

private theorem unrestricted_on_open (n : Nat) :
    UniversalProjection (openFuture n) unconstrained n := by
  intro f hf
  exact ⟨hf.1.1, fun _ => trivial⟩

private theorem nondeterministic_unconstrained : ¬ Deterministic unconstrained := by
  intro hdet
  exact Bool.noConfusion (hdet 0 true true false trivial trivial)

private theorem impossible_empty (n : Nat) : ¬ ∃ f, Cell impossible on n f := by
  rintro ⟨f, hf⟩
  have htrue : f 0 = true := hf.2 0 (by omega)
  have hfalse : f 0 = false := hf.1.1
  exact Bool.noConfusion (htrue.symm.trans hfalse)

/-- Groundlessness does not, by itself, force anarchy: the brute-grounding
scope and the stable trace coexist. Conversely an independently supplied
grounding scope can be paired with open suffixes. Neither is a causal model. -/
theorem omissions : Omissions := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨stable_cell n, fun _ hf => hf.1, stable_not_complete n⟩
  · intro n
    exact ⟨on_in_open n, ⟨rfl, fun _ => rfl⟩,
      unrestricted_on_open n, nondeterministic_unconstrained⟩
  · intro n
    exact ⟨impossible_empty n, fun q f hf =>
      (impossible_empty n ⟨f, hf⟩).elim⟩
  · intro n
    refine ⟨?_, ?_, stable_not_complete n, all_splices n⟩
    · rintro ⟨_, hg⟩
      exact (by decide : Target.spacetime ≠ Target.process) hg
    · exact ⟨.process, trivial⟩

end TruthCore.Results.Explanation.NoFoundationLawChaos
