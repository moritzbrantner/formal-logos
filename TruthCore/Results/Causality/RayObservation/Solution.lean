module

public import TruthCore.Causality.RayObservation

@[expose] public section

namespace TruthCore.Results.Causality.RayObservation

open TruthCore.Causality
open TruthCore.Causality.ParallelPowerTransmission
open TruthCore.Causality.RayObservation

theorem rayReportCharacterization (classified : ActivityClassification) :
    RayReportCharacterization := by
  intro K O intact position report
  obtain ⟨classify, realize⟩ := classified.1 K intact
  constructor
  · rintro ⟨active, law, observed⟩
    have observedOn (i : O) : report i = true ↔
        (∃ n, active ((position i).1, n)) ∧ Live intact position i :=
      (observed i).symm.trans (classify active |>.mp law (position i).1 (position i).2)
    have off : ∀ i, ¬ Live intact position i → report i = false := by
      intro i cut
      cases value : report i
      · rfl
      · exact False.elim (cut ((observedOn i).mp value).2)
    refine ⟨off, ?_⟩
    intro i j liveI liveJ sameRay
    apply Bool.eq_iff_iff.mpr
    rw [observedOn, observedOn, sameRay, and_iff_left liveI, and_iff_left liveJ]
  · rintro ⟨off, agree⟩
    let selected (k : K) :=
      ∃ i, (position i).1 = k ∧ Live intact position i ∧ report i = true
    refine ⟨fun x => selected x.1 ∧ intactTail (intact x.1) x.2, (realize selected).1, ?_⟩
    intro i
    change selected (position i).1 ∧ Live intact position i ↔ report i = true
    constructor
    · rintro ⟨⟨j, sameRay, liveJ, on⟩, liveI⟩
      exact (agree j i liveJ liveI sameRay).symm.trans on
    · intro on
      have live : Live intact position i := by
        by_contra cut
        simp [off i cut] at on
      exact ⟨⟨i, rfl, live, on⟩, live⟩

private theorem reportEquiv (characterized : RayReportCharacterization)
    {K O : Type} (intact : K → Nat → Prop) (position : O → K × Nat) :
    Nonempty ((ObservedRays intact position → Bool) ≃
      {report : O → Bool // Feasible intact position report}) := by
  classical
  let extend (assignment : ObservedRays intact position → Bool) (i : O) : Bool :=
    if live : Live intact position i then assignment (observedRay i live) else false
  have extendLive (assignment : ObservedRays intact position → Bool) (i : O)
      (live : Live intact position i) :
      extend assignment i = assignment (observedRay i live) := dite_eq_left live
  let observe (assignment : ObservedRays intact position → Bool) :
      {report : O → Bool // Feasible intact position report} :=
    ⟨extend assignment, (characterized K O intact position (extend assignment)).mpr
      ⟨fun _ cut => dite_eq_right cut, fun i j liveI liveJ sameRay => by
        rw [extendLive assignment i liveI, extendLive assignment j liveJ]
        exact congrArg assignment (Subtype.ext sameRay)⟩⟩
  refine ⟨Equiv.ofBijective observe ⟨?_, ?_⟩⟩
  · intro a b sameReport
    funext k
    rcases k with ⟨k, ⟨⟨i, live⟩, rfl⟩⟩
    have sameReading := congrArg (fun report => report.val i) sameReport
    change extend a i = extend b i at sameReading
    change a (observedRay i live) = b (observedRay i live)
    simpa only [extendLive _ i live] using sameReading
  · rintro ⟨report, feasible⟩
    obtain ⟨off, agree⟩ := (characterized K O intact position report).mp feasible
    let assignment (k : ObservedRays intact position) := report k.property.choose.val
    refine ⟨assignment, Subtype.ext (funext fun i => ?_)⟩
    change extend assignment i = report i
    by_cases live : Live intact position i
    · rw [extendLive assignment i live]
      let k := observedRay i live
      exact agree _ i k.property.choose.property live k.property.choose_spec
    · exact (dite_eq_right live).trans (off i live).symm

theorem finiteRayReportCount (characterized : RayReportCharacterization) :
    FiniteRayReportCount := by
  intro K O _ intact position
  let : Finite (ObservedRays intact position) :=
    Finite.of_surjective _ Set.rangeFactorization_surjective
  obtain ⟨equiv⟩ := reportEquiv characterized intact position
  rw [← Nat.card_congr equiv, Nat.card_fun]
  simp

theorem sharedSwitchCharacterization (classified : ActivityClassification) :
    SharedSwitchCharacterization := by
  classical
  intro K O intact position report
  constructor
  · constructor
    · rintro ⟨enabled, readings⟩
      constructor
      · intro i cut
        cases value : report i
        · rfl
        · exact False.elim (cut ((readings i).mp value).2)
      · intro i j liveI liveJ
        apply Bool.eq_iff_iff.mpr
        rw [readings i, readings j, and_iff_left liveI, and_iff_left liveJ]
    · rintro ⟨off, agree⟩
      by_cases someLive : ∃ i, Live intact position i
      · obtain ⟨i, liveI⟩ := someLive
        refine ⟨report i, fun j => ?_⟩
        by_cases liveJ : Live intact position j
        · rw [and_iff_left liveJ, agree j i liveJ liveI]
        · simp [liveJ, off j liveJ]
      · exact ⟨false, fun i => by simp [off i (fun live => someLive ⟨i, live⟩)]⟩
  · constructor
    · rintro ⟨enabled, readings⟩
      let active (x : K × Nat) := enabled = true ∧ intactTail (intact x.1) x.2
      exact ⟨enabled, active, ((classified.1 K intact).2 (fun _ => enabled = true)).1,
        fun _ _ => Iff.rfl, fun i => (readings i).symm⟩
    · rintro ⟨enabled, active, _, profile, readings⟩
      exact ⟨enabled, fun i =>
        (readings i).symm.trans (profile (position i).1 (position i).2)⟩

theorem mixedLiveRayReport (characterized : RayReportCharacterization)
    (shared : SharedSwitchCharacterization) : MixedLiveRayReport := by
  classical
  intro K O intact position i j liveI liveJ
  constructor
  · constructor
    · rintro ⟨report, feasible, on, off⟩ sameRay
      obtain ⟨_, agree⟩ := (characterized K O intact position report).mp feasible
      exact Bool.noConfusion (on.symm.trans ((agree i j liveI liveJ sameRay).trans off))
    · intro distinct
      let report (k : O) :=
        if Live intact position k ∧ (position k).1 = (position i).1 then true else false
      refine ⟨report, (characterized K O intact position report).mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · intro k cut
        simp [report, cut]
      · intro k l liveK liveL sameRay
        simp [report, liveK, liveL, sameRay]
      · simp [report, liveI]
      · simp [report, distinct.symm]
  · intro report on off admitted
    obtain ⟨_, agree⟩ := ((shared K O intact position report).1).mp admitted
    exact Bool.noConfusion (on.symm.trans ((agree i j liveI liveJ).trans off))

theorem distinctLiveSuppliers {K O : Type} (intact : K → Nat → Prop)
    (position : O → K × Nat) (i j : O)
    (liveI : Live intact position i) (liveJ : Live intact position j)
    (distinct : (position i).1 ≠ (position j).1) :
    (∃ supplier, transmissionLink intact supplier (position i)) ∧
    (∃ supplier, transmissionLink intact supplier (position j)) ∧
    ¬ ∃ supplier, transmissionLink intact supplier (position i) ∧
      transmissionLink intact supplier (position j) := by
  refine ⟨⟨_, rfl, liveI _ (Nat.le_refl _)⟩, ⟨_, rfl, liveJ _ (Nat.le_refl _)⟩, ?_⟩
  rintro ⟨_, ⟨supplierI, _⟩, ⟨supplierJ, _⟩⟩
  have sameRay := congrArg Prod.fst (supplierI.symm.trans supplierJ)
  exact distinct sameRay

end TruthCore.Results.Causality.RayObservation
