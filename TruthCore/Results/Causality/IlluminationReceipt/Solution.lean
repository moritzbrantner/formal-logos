module
public import TruthCore.Causality.IlluminationReceipt
@[expose] public section
namespace TruthCore.Results.Causality.IlluminationReceipt
open TruthCore.Causality.IlluminationReceipt
open TruthCore.Causality.PreservationMeaning

private theorem sumPositive (m n : Nat) : 0 < m + n ↔ 0 < m ∨ 0 < n := by
  constructor
  · intro h
    cases m
    · rw [Nat.zero_add] at h
      exact Or.inr h
    · exact Or.inl (Nat.zero_lt_succ _)
  · intro h
    rcases h with h | h
    · exact Nat.add_pos_left h n
    · exact Nat.add_pos_right m h

theorem responseLaw : ResponseLaw := by
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h : s.receptive
    · change (0 < (if s.receptive then solarInput s + lampInput s else 0)) ↔ _
      rw [h]
      constructor
      · intro bad
        cases bad
      · intro bad
        cases bad.2
    · change (0 < (if s.receptive then solarInput s + lampInput s else 0)) ↔ _
      rw [h]
      exact ⟨fun hp => ⟨(sumPositive _ _).mp hp, rfl⟩,
        fun hp => (sumPositive _ _).mpr hp.1⟩
  · intro h
    unfold solarInput transmit
    rw [h]
    cases s.solarPath <;> rfl
  · intro h
    unfold solarInput transmit
    rw [h]
    rfl
  · unfold solarInput transmit
    cases h : s.solarPath
    · constructor
      · intro bad
        cases bad
      · intro bad
        cases bad.2
    · exact ⟨fun hp => ⟨hp, rfl⟩, fun hp => hp.1⟩

private theorem solarAvailable (i : Bool) (a s : Scenario) (p : Bool → Prop)
    (u : 0 < solarInput s) (r : s.receptive = true) :
    AvailableRecord (model i a p) s .illumination := by
  refine ⟨false, Or.inl rfl, rfl, ⟨.solarArrival, rfl⟩, ?_⟩
  intro e he
  rcases he with he | he
  · have h : e = .solarArrival := he
    subst e
    exact u
  · have h : e = .receptivity := he
    subst e
    exact r

private theorem lampAvailable (a s : Scenario) (p : Bool → Prop)
    (u : 0 < lampInput s) (r : s.receptive = true) :
    AvailableRecord (model true a p) s .illumination := by
  refine ⟨true, Or.inr rfl, rfl, ⟨.lampArrival, rfl⟩, ?_⟩
  intro e he
  rcases he with he | he
  · have h : e = .lampArrival := he
    subst e
    exact u
  · have h : e = .receptivity := he
    subst e
    exact r

theorem recordAnalysis : RecordAnalysis := by
  intro a p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i s scope occurrence
    obtain ⟨hu | hu, hr⟩ := (responseLaw s).1.mp occurrence
    · exact solarAvailable i a s p hu hr
    · rcases scope with hi | absent
      · subst i
        exact lampAvailable a s p hu hr
      · rw [absent] at hu
        cases hu
  · intro g admitted _
    cases g
    · exact ⟨.solarArrival, rfl, rfl⟩
    · rcases admitted with bad | bad <;> cases bad
  · intro cut
    obtain ⟨e, he, hb⟩ := cut true (Or.inr rfl) rfl
    have h : e = .lampArrival := he
    subst e
    cases hb
  · intro cut
    obtain ⟨e, he, hb⟩ := cut false (Or.inl rfl) rfl
    have h : e = .solarArrival := he
    subst e
    cases hb
  · intro i scope correspondence
    refine ⟨scope, ?_⟩
    intro g exercised
    obtain ⟨admitted, input, receptive⟩ := correspondence g exercised
    refine ⟨admitted, ?_, ?_⟩
    · intro e he
      rcases he with he | he
      · cases g
        · have h : e = .solarArrival := he
          subst e
          exact input
        · have h : e = .lampArrival := he
          subst e
          exact input
      · have h : e = .receptivity := he
        subst e
        exact receptive
    · apply (responseLaw a).1.mpr
      cases g
      · exact ⟨Or.inl input, receptive⟩
      · exact ⟨Or.inr input, receptive⟩

  · intro i s g _ members
    apply (responseLaw s).1.mpr
    refine ⟨?_, members .receptivity (Or.inr rfl)⟩
    cases g
    · exact Or.inl (members .solarArrival (Or.inl rfl))
    · exact Or.inr (members .lampArrival (Or.inl rfl))

theorem controls : Controls := by
  have coherent : (model false bright (fun g => g = false)).coherent := by
    apply (recordAnalysis bright (fun g => g = false)).2.2.2.2.1 false (Or.inr rfl)
    intro g hg
    subst g
    exact ⟨Or.inl rfl, by decide, rfl⟩
  have inactive : SourceInactive (model true bright (fun g => g = false)) lampLit .sun := by
    intro g e _ he hb
    cases g
    · have h : e = .solarArrival := he
      subst e
      change ¬ (0 < 0)
      intro bad
      cases bad
    · have h : e = .lampArrival := he
      subst e
      cases hb
  refine ⟨coherent, ⟨solarAvailable false bright bright _ (by decide) rfl,
    (recordAnalysis bright _).2.1⟩, rfl, ⟨Or.inr rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨Or.inl rfl, ?_, rfl, inactive⟩,
    ⟨rfl, rfl, rfl, ?_⟩, rfl, ?_, ?_, solarAvailable false bright bright _ (by decide) rfl, ?_⟩
  · intro scope
    rcases scope with bad | bad <;> cases bad
  · apply (recordAnalysis bothLit (fun _ => True)).2.2.2.2.1 true (Or.inl rfl)
    intro g _
    refine ⟨Or.inr rfl, ?_, rfl⟩
    cases g <;> decide
  · intro bad
    cases bad
  · exact ⟨Or.inr rfl, fun _ bad => False.elim bad⟩
  · intro g bad
    exact bad
end TruthCore.Results.Causality.IlluminationReceipt
