module

public import TruthCore.Causality.RelationalReceipt

@[expose] public section

namespace TruthCore.Results.Causality.RelationalReceipt

open TruthCore.Causality.RelationalReceipt
open TruthCore.Causality.PresentReceipt
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)
open TruthCore.Modal.TemporalHistory (History BeginsAt)

/-- Accompaniment and giving by the term give weak concurrent actualization
`40a97664`: a received-esse thing present at `t` bears the origin relation to
something at `t`, and that term gives it being at `t`. -/
theorem concurrentOfTermGiving {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (O : OriginRelation W B T) (EsseReceivedIn : B → P → Prop)
    (hAccompanies : RelationAccompaniesEsse h O EsseReceivedIn)
    (hGives : TermGives G O) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  intro v x t z hz hx
  obtain ⟨g, hr⟩ := hAccompanies v x z t hz hx
  exact ⟨g, hGives v x g t hr⟩

/-- On the relational sense the present-tense reading is accompaniment. -/
theorem relationalPresentIsAccompaniment : RelationalPresentIsAccompaniment := by
  intro W B T P h O E
  refine ⟨fun hP v x z t hz hx => (hP v x z t hz hx).2.2, ?_⟩
  intro hA v x z t hz hx
  exact ⟨hz, hx, hA v x z t hz hx⟩

/-- On the relational sense, given accompaniment, correlativity is weak
concurrent actualization. -/
theorem relationalReadingIsTheCrux : RelationalReadingIsTheCrux := by
  intro W B T P h G O E hA
  refine ⟨?_, ?_⟩
  · intro hC v x t z hz hx
    exact hC v z x t ⟨hz, hx, hA v x z t hz hx⟩
  · intro hCA v z x t hr
    exact hCA v x t z hr.1 hr.2.1

/-- Some founded, accompanying origin relation whose term gives exists iff weak
concurrent actualization holds: forward by `concurrentOfTermGiving`, backward
with the relation to whatever is giving being at the moment. -/
theorem someRelationCarriesTheCrux : SomeRelationCarriesTheCrux := by
  intro W B T P h G E
  refine ⟨fun ⟨O, _, hA, hG⟩ => concurrentOfTermGiving h G O E hA hG, fun hCA => ?_⟩
  refine ⟨⟨fun v x g t => (∃ z, E x z) ∧ h.IsAt v x t ∧ G.GivesAt v g x t⟩,
    fun _ _ _ _ hr => ⟨hr.1, hr.2.1⟩, ?_, fun _ _ _ _ hr => hr.2.2⟩
  intro v x z t hz hx
  obtain ⟨g, hg⟩ := hCA v x t z hz hx
  exact ⟨g, ⟨z, hz⟩, hx, hg⟩

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.RelationalReceipt.Control

/-- Controls (`Control.Certificate`). -/
theorem controls : TruthCore.Causality.RelationalReceipt.Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- (1) creator present throughout, giving at onset only, persisting relation
  · rintro v x g t ⟨rfl, rfl, ht⟩
    exact ⟨⟨(), rfl⟩, Or.inr ⟨rfl, ht⟩⟩
  · rintro v x z t rfl hx
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · rintro v x g t ⟨_, rfl, _⟩
    exact Or.inl rfl
  · rintro v x z b rfl ⟨hb, hfirst⟩
    rcases hb with h | ⟨_, hb1⟩
    · exact Bool.noConfusion h
    · have : b = 1 := by
        by_contra hne
        exact hfirst 1 (by omega) (Or.inr ⟨rfl, le_refl 1⟩)
      exact ⟨true, rfl, rfl, this⟩
  · rintro v x z t rfl hx
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨rfl, Or.inr ⟨rfl, ht⟩, true, rfl, rfl, ht⟩
  · intro hG
    have := hG () false true 2 ⟨rfl, rfl, by decide⟩
    exact absurd this.2.2 (by decide)
  · intro hC
    obtain ⟨_, _, _, h2⟩ := hC () () false 2
      ⟨rfl, Or.inr ⟨rfl, by decide⟩, true, rfl, rfl, by decide⟩
    exact absurd h2 (by decide)
  · intro hA
    obtain ⟨_, _, _, h2⟩ := hA () false 2 () rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  -- (2) same history and giving, relation at onset only
  · rintro v x g t ⟨rfl, rfl, rfl⟩
    exact ⟨⟨(), rfl⟩, Or.inr ⟨rfl, le_refl 1⟩⟩
  · rintro v x g t ⟨_, rfl, _⟩
    exact Or.inl rfl
  · rintro v x g t ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · rintro v z x t ⟨_, _, g, rfl, rfl, rfl⟩
    exact ⟨true, rfl, rfl, rfl⟩
  · intro hA
    obtain ⟨_, _, _, h2⟩ := hA () false () 2 rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  · intro hP
    obtain ⟨_, _, _, _, _, h2⟩ := hP () false () 2 rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  · intro hA
    obtain ⟨_, _, _, h2⟩ := hA () false 2 () rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  -- (3) term absent after onset, persisting relation
  · rintro v x g t ⟨rfl, rfl, ht⟩
    exact ⟨⟨(), rfl⟩, Or.inr ⟨rfl, ht⟩⟩
  · rintro v x z t rfl hx
    rcases hx with ⟨h, _⟩ | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · intro hT
    rcases hT () false true 2 ⟨rfl, rfl, by decide⟩ with ⟨_, h2⟩ | ⟨h, _⟩
    · exact absurd h2 (by decide)
    · exact Bool.noConfusion h
  -- (4) sustaining, persisting relation
  · rintro v x g t ⟨rfl, rfl, ht⟩
    exact ⟨⟨(), rfl⟩, Or.inr ⟨rfl, ht⟩⟩
  · rintro v x z t rfl hx
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · rintro v x g t ⟨_, rfl, _⟩
    exact Or.inl rfl
  · rintro v x g t ⟨rfl, rfl, ht⟩
    exact ⟨rfl, rfl, ht⟩
  · rintro v z x t ⟨_, _, g, rfl, rfl, ht⟩
    exact ⟨true, rfl, rfl, ht⟩
  · rintro v x t z rfl hx
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩

/-- Foundation, accompaniment, coexistence of the term and received onset given
do not entail weak concurrent actualization: `Control` part 1 is a
counterexample. -/
theorem coexistentTermDoesNotCarryTheCrux : CoexistentTermDoesNotCarryTheCrux := by
  intro hAll
  obtain ⟨⟨hF, hA, hT, hO, -, -, -, hNot⟩, -⟩ := controls
  exact hNot (hAll Unit Bool Nat Unit sustained inertiaGiving persistingOrigin falseReceived
    hF hA hT hO)

end TruthCore.Results.Causality.RelationalReceipt
