module

public import TruthCore.Causality.ParallelPowerTransmission

@[expose] public section

namespace TruthCore.Results.Causality.ParallelPowerTransmission

open TruthCore.Causality
open TruthCore.Causality.ParallelPowerTransmission

theorem transmissionEquation {Node : Type} (supplier : Node → Node)
    (intact active : Node → Prop) :
    PowerTransmissionRule (fun y x => y = supplier x ∧ intact x) active ↔
      ∀ x, active x ↔ intact x ∧ active (supplier x) := by
  constructor
  · intro law x
    constructor
    · intro hx
      obtain ⟨_, ⟨rfl, link⟩, upstream⟩ := (law x).mp hx
      exact ⟨link, upstream⟩
    · intro h
      exact (law x).mpr ⟨supplier x, ⟨rfl, h.1⟩, h.2⟩
  · intro equation x
    constructor
    · intro hx
      obtain ⟨link, upstream⟩ := (equation x).mp hx
      exact ⟨supplier x, ⟨rfl, link⟩, upstream⟩
    · rintro ⟨_, ⟨rfl, link⟩, upstream⟩
      exact (equation x).mpr ⟨link, upstream⟩

theorem intactTailStep (intact : Nat → Prop) (n : Nat) :
    intactTail intact n ↔ intact n ∧ intactTail intact (n + 1) := by
  constructor
  · intro h
    exact ⟨h n (Nat.le_refl _), fun m hm => h m (Nat.le_trans (Nat.le_succ _) hm)⟩
  · rintro ⟨link, tail⟩ m hm
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact link
    · exact tail m hlt

/-- When a ray has an active position, every position with an intact
upstream tail is active. Activity also requires an intact upstream tail. -/
theorem populatedRay {intact active : Nat → Prop}
    (equation : ∀ n, active n ↔ intact n ∧ active (n + 1))
    (populated : ∃ n, active n) (n : Nat) : active n ↔ intactTail intact n := by
  have propagate {i j : Nat} (h : i ≤ j) (hi : active i) : active j := by
    induction h with
    | refl => exact hi
    | step _ ih => exact ((equation _).mp ih).2
  constructor
  · intro hn m hm
    exact ((equation m).mp (propagate hm hn)).1
  · intro tail
    obtain ⟨i, hi⟩ := populated
    have agree {m : Nat} (hm : n ≤ m) : active n ↔ active m := by
      induction hm with
      | refl => exact Iff.rfl
      | step h ih =>
        exact ih.trans ⟨fun hx => ((equation _).mp hx).2,
          fun hx => (equation _).mpr ⟨tail _ h, hx⟩⟩
    exact (agree (Nat.le_max_left n i)).mpr (propagate (Nat.le_max_right n i) hi)

private theorem parallelEquation {K : Type} (intact : K → Nat → Prop)
    (active : K × Nat → Prop) :
    PowerTransmissionRule (transmissionLink intact) active ↔
      ∀ x : K × Nat, active x ↔ intact x.1 x.2 ∧ active (x.1, x.2 + 1) :=
  transmissionEquation (fun x => (x.1, x.2 + 1)) (fun x => intact x.1 x.2) active

private theorem selectedTailStep {K : Type} (intact : K → Nat → Prop)
    (selected : K → Prop) (k : K) (n : Nat) :
    (selected k ∧ intactTail (intact k) n) ↔
      intact k n ∧ (selected k ∧ intactTail (intact k) (n + 1)) := by
  constructor
  · rintro ⟨chosen, tail⟩
    obtain ⟨link, upstream⟩ := (intactTailStep (intact k) n).mp tail
    exact ⟨link, chosen, upstream⟩
  · rintro ⟨link, chosen, upstream⟩
    exact ⟨chosen, (intactTailStep (intact k) n).mpr ⟨link, upstream⟩⟩

private theorem raySolutions : RaySolutions := by
  intro K intact
  constructor
  · intro active
    constructor
    · intro law k n
      have equation (m : Nat) := (parallelEquation intact active).mp law (k, m)
      exact ⟨fun hn => ⟨⟨n, hn⟩, (populatedRay equation ⟨n, hn⟩ n).mp hn⟩,
        fun h => (populatedRay equation h.1 n).mpr h.2⟩
    · intro classified
      apply (parallelEquation intact active).mpr
      rintro ⟨k, n⟩
      constructor
      · intro hn
        obtain ⟨link, chosen, upstream⟩ :=
          (selectedTailStep intact (fun j => ∃ m, active (j, m)) k n).mp
            ((classified k n).mp hn)
        exact ⟨link, (classified k (n + 1)).mpr ⟨chosen, upstream⟩⟩
      · rintro ⟨link, upstream⟩
        exact (classified k n).mpr
          ((selectedTailStep intact (fun j => ∃ m, active (j, m)) k n).mpr
            ⟨link, (classified k (n + 1)).mp upstream⟩)
  · intro selected
    constructor
    · apply (parallelEquation intact _).mpr
      rintro ⟨k, n⟩
      exact selectedTailStep intact selected k n
    · intro k
      exact ⟨fun ⟨n, chosen, tail⟩ => ⟨chosen, n, tail⟩,
        fun ⟨chosen, n, tail⟩ => ⟨n, chosen, tail⟩⟩

private theorem cutEffects : CutEffects := by
  intro K intact
  obtain ⟨classify, realize⟩ := raySolutions K intact
  have offOfCut (active : K × Nat → Prop)
      (law : PowerTransmissionRule (transmissionLink intact) active)
      (k : K) (n m : Nat) (le : n ≤ m) (cut : ¬ intact k m) : ¬ active (k, n) := by
    intro hn
    have tail := ((classify active).mp law k n).mp hn
    exact cut (tail.2 m le)
  refine ⟨offOfCut, ?_, ?_⟩
  · constructor
    · intro allOff k n tail
      exact allOff _ (realize (fun _ => True)).1 (k, n) ⟨True.intro, tail⟩
    · intro none active law x hx
      exact none x.1 x.2 (((classify active).mp law x.1 x.2).mp hx).2
  · intro cofinal active law
    rintro ⟨k, n⟩
    obtain ⟨m, le, cut⟩ := cofinal k n
    exact offOfCut active law k n m le cut

theorem activityClassification : ActivityClassification :=
  ⟨raySolutions, cutEffects⟩

theorem countableCatalogueMisses (classified : ActivityClassification) :
    CountableCatalogueMisses := by
  intro catalogue
  let selected (i : Nat) := ¬ catalogue i (i, 0)
  obtain ⟨_, realize⟩ := classified.1 Nat (fun _ _ => True)
  refine ⟨fun x => selected x.1 ∧ intactTail (fun _ => True) x.2,
    (realize selected).1, ?_⟩
  intro i agrees
  have notEntry : selected i := fun entry => ((agrees.mpr entry).1) entry
  exact notEntry (agrees.mp ⟨notEntry, fun _ _ => True.intro⟩)

end TruthCore.Results.Causality.ParallelPowerTransmission
