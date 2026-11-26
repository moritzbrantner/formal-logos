module

public import TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver
public import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution
public import TruthCore.Results.Causality.SupplierAuditCertificates.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.UnobservedGiver

open TruthCore.Causality.SupplierAuditCertificates (RootAncestor)
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.UnobservedGiver
open TruthCore.Latin.Aquinas.SummaTheologiae

private theorem actualCauseIff {g c x : Option Nat} :
    ActualEsseCause (rankedProfile g) c x ↔ rank g c < rank g x := by
  constructor
  · exact fun h => h.2.2.2
  · intro h
    refine ⟨?_, trivial, trivial, h⟩
    rintro rfl
    exact (Nat.lt_irrefl _ h)

private theorem rankBound (g x : Option Nat) : rank g x ≤ 2 := by
  unfold rank
  split
  · exact Nat.zero_le 2
  · split
    · exact Nat.le.step Nat.le.refl
    · exact Nat.le.refl

private theorem rootGives {g x : Option Nat} (different : x ≠ g) :
    ActualEsseCause (rankedProfile g) g x := by
  apply actualCauseIff.mpr
  unfold rank
  rw [ite_eq_left rfl, ite_eq_right different]
  split
  · exact Nat.zero_lt_succ 0
  · exact Nat.zero_lt_succ 1

private theorem rootUncaused (g c : Option Nat) :
    ¬ ActualEsseCause (rankedProfile g) c g := by
  intro h
  have lower := actualCauseIff.mp h
  have zero : rank g g = 0 := ite_eq_left rfl
  rw [zero] at lower
  exact Nat.not_lt_zero _ lower

private theorem rankedGiverProfile (g : Option Nat) : RankedGiverProfile g := by
  have wf : NoInfiniteActualEsseCauseRegress (rankedProfile g) :=
    Subrelation.wf (fun h => actualCauseIff.mp h) (measure (rank g)).wf
  have maximum (x : Option Nat) :
      IsMaximumIn (rankedProfile g).InAct (moreIn g) (rankedProfile g).esse x ↔ x = g := by
    constructor
    · intro h
      by_contra different
      exact h.2 g (actualCauseIff.mp (rootGives different))
    · intro equal
      subst x
      exact ⟨trivial, fun c lower => rootUncaused g c (actualCauseIff.mpr lower)⟩
  refine ⟨fun _ => trivial, rankBound g, wf,
    TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.closedOfWF _ wf,
    fun _ _ _ _ h => h, fun _ _ _ h => h,
    ⟨g, (maximum g).mpr rfl, fun _ different _ => (rootGives different).2.2.2⟩,
    maximum, fun _ => rootGives, ?_⟩
  have rootAncestor (x r : Option Nat) :
      RootAncestor r x (ActualEsseCause (rankedProfile g)) ↔ r = g := by
    constructor
    · intro h
      by_contra different
      exact h.2 g (rootGives different)
    · intro equal
      subst r
      refine ⟨?_, rootUncaused g⟩
      by_cases same : x = g
      · subst x
        exact .refl
      · exact .single (rootGives same)
  refine ⟨rootAncestor, fun x _ => ⟨g, trivial, ?_⟩⟩
  exact (TruthCore.Results.Causality.SupplierAuditCertificates.positiveCertificate
    (ActualEsseCause (rankedProfile g)) g x).mp ((rootAncestor x g).mpr rfl)

private theorem agreesAwayFrom {h c x : Option Nat}
    (hidden : h ≠ none) (hc : c ≠ h) (hx : x ≠ h) :
    ActualEsseCause (rankedProfile none) c x ↔ ActualEsseCause (rankedProfile h) c x := by
  rw [actualCauseIff, actualCauseIff]
  by_cases hcNone : c = none
  · by_cases hxNone : x = none
    · subst c x
      exact ⟨fun edge => (Nat.lt_irrefl _ edge).elim, fun edge => (Nat.lt_irrefl _ edge).elim⟩
    · simp only [rank, hcNone, hxNone, hidden, Ne.symm hidden, hx, or_self, false_or,
        true_or, ite_true, ite_false]
      exact ⟨fun _ => Nat.lt_succ_self 1, fun _ => Nat.zero_lt_succ 0⟩
  · by_cases hxNone : x = none
    · simp only [rank, hcNone, hxNone, hidden, Ne.symm hidden, hc, or_self, false_or,
        true_or, ite_true, ite_false]
      exact ⟨fun edge => (Nat.not_lt_zero _ edge).elim,
        fun edge => (Nat.not_lt_of_ge (Nat.le.step Nat.le.refl) edge).elim⟩
    · simp only [rank, hcNone, hxNone, hidden, hc, hx, or_self, true_or,
        ite_true, ite_false]
      exact ⟨fun edge => (Nat.lt_irrefl _ edge).elim, fun edge => (Nat.lt_irrefl _ edge).elim⟩

theorem finitePairGiverControl : FinitePairGiverControl := by
  refine ⟨rankedGiverProfile, ?_⟩
  intro tested finite
  obtain ⟨h, fresh⟩ := ((finite.image Prod.fst).union (finite.image Prod.snd)).insert none
    |>.exists_notMem
  have hidden : h ≠ none := fun equal => fresh (equal ▸ Set.mem_insert _ _)
  have freshPair {c x : Option Nat} (observed : (c, x) ∈ tested) : c ≠ h ∧ x ≠ h :=
    ⟨fun equal => fresh (equal ▸ Set.mem_insert_of_mem _ (.inl ⟨(c, x), observed, rfl⟩)),
      fun equal => fresh (equal ▸ Set.mem_insert_of_mem _ (.inr ⟨(c, x), observed, rfl⟩))⟩
  have supplies : ActualEsseCause (rankedProfile h) h none := rootGives (Ne.symm hidden)
  exact ⟨h, hidden, fun c x observed =>
    ⟨(freshPair observed).1, (freshPair observed).2,
      agreesAwayFrom hidden (freshPair observed).1 (freshPair observed).2⟩,
    supplies, fun h => h.2 _ supplies⟩

end TruthCore.Results.Aquinas.DeEnte.UnobservedGiver
