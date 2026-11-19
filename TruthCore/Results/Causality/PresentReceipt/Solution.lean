module

public import TruthCore.Causality.PresentReceipt

@[expose] public section

namespace TruthCore.Results.Causality.PresentReceipt

open TruthCore.Causality.PresentReceipt
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)
open TruthCore.Modal.TemporalHistory (History BeginsAt)

/-- Present-tense reception and correlativity give weak concurrent
actualization `40a97664`: a received-esse thing present at `t` is receiving its
esse at `t`, and whatever is receiving at `t` is given being at `t`. -/
theorem concurrentOfPresentReceipt {W B T P : Type} (h : History W B T)
    (G : BeingGiving W B T) (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop)
    (hPresent : ReceptionIsPresent h R EsseReceivedIn)
    (hCorrelative : ReceivingIsCorrelativeWithGiving G R) :
    ConcurrentlyActualized h G EsseReceivedIn :=
  fun v x t z hz hx => hCorrelative v z x t (hPresent v x z t hz hx)

/-- The onset reading and correlativity give received onset is given
`fa3e228b`. -/
theorem onsetOfOnsetReceipt {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop)
    (hOnset : ReceptionAtOnset h R EsseReceivedIn)
    (hCorrelative : ReceivingIsCorrelativeWithGiving G R) :
    ReceivedOnsetIsGiven h G EsseReceivedIn :=
  fun v x z b hz hb => hCorrelative v z x b (hOnset v x z b hz hb)

/-- Strength order: the present-tense reading entails the onset reading. -/
theorem onsetOfPresentReceipt {W B T P : Type} [Preorder T] (h : History W B T)
    (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop)
    (hPresent : ReceptionIsPresent h R EsseReceivedIn) :
    ReceptionAtOnset h R EsseReceivedIn :=
  fun v x z b hz hb => hPresent v x z b hz hb.1

/-- On the passion sense correlativity holds by definition and the
present-tense reading is weak concurrent actualization. -/
theorem passionReadingIsTheCrux : PassionReadingIsTheCrux := by
  intro W B T P h G E
  refine ⟨fun _ _ _ _ hr => hr.2, ⟨fun hP v x t z hz hx => (hP v x z t hz hx).2, ?_⟩⟩
  intro hC v x z t hz hx
  exact ⟨hz, hC v x t z hz hx⟩

/-- On the standing sense the present-tense reading holds by definition and
correlativity is weak concurrent actualization. -/
theorem standingReadingIsTheCrux : StandingReadingIsTheCrux := by
  intro W B T P h G E
  refine ⟨fun _ _ _ _ hz hx => ⟨hz, hx⟩, ⟨?_, ?_⟩⟩
  · intro hC v x t z hz hx
    exact hC v z x t ⟨hz, hx⟩
  · intro hA v z x t hr
    exact hA v x t z hr.1 hr.2

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.PresentReceipt.Control

/-- Omission, rival-reading, separation and nonvacuity controls
(`Control.Certificate`). -/
theorem controls : TruthCore.Causality.PresentReceipt.Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- (1) inertia, past-tense receipt
  · rintro v x z b rfl ⟨hb, hfirst⟩
    refine ⟨rfl, ?_⟩
    rcases hb with ⟨h, _⟩ | ⟨_, hb1⟩
    · exact Bool.noConfusion h
    · by_contra hne
      exact hfirst 1 (by omega) (Or.inr ⟨rfl, le_refl 1⟩)
  · rintro v z x t ⟨rfl, rfl⟩
    exact ⟨true, rfl, rfl, rfl⟩
  · intro hP
    have := hP () false () 2 rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd this.2 (by decide)
  · intro hA
    obtain ⟨g, _, _, h2⟩ := hA () false 2 () rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  · rintro v x z b rfl ⟨hb, hfirst⟩
    rcases hb with ⟨h, _⟩ | ⟨_, hb1⟩
    · exact Bool.noConfusion h
    · have : b = 1 := by
        by_contra hne
        exact hfirst 1 (by omega) (Or.inr ⟨rfl, le_refl 1⟩)
      exact ⟨true, rfl, rfl, this⟩
  -- (2) inertia, standing receipt
  · intro v x z t hz hx; exact ⟨hz, hx⟩
  · intro v x z b hz hb; exact ⟨hz, hb.1⟩
  · intro hC
    obtain ⟨g, _, _, h2⟩ := hC () () false 2 ⟨rfl, Or.inr ⟨rfl, by decide⟩⟩
    exact absurd h2 (by decide)
  · intro hA
    obtain ⟨g, _, _, h2⟩ := hA () false 2 () rfl (Or.inr ⟨rfl, by decide⟩)
    exact absurd h2 (by decide)
  -- (3) sustaining, no receipt
  · rintro v x t z rfl hx
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · intro hP; exact hP () false () 1 rfl (Or.inr ⟨rfl, le_refl 1⟩)
  · intro hO
    refine hO () false () 1 rfl ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs hxs => ?_⟩
    rcases hxs with h | ⟨_, h1⟩
    · exact Bool.noConfusion h
    · omega
  · intro _ _ _ _ hr; exact hr.elim
  -- (4) inertia, no giving, no receipt
  · intro _ _ _ _ hr; exact hr.elim
  · intro hO
    refine hO () false () 1 rfl ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs hxs => ?_⟩
    rcases hxs with ⟨h, _⟩ | ⟨_, h1⟩
    · exact Bool.noConfusion h
    · omega
  · intro hO
    obtain ⟨_, hg⟩ := hO () false () 1 rfl ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs hxs => by
      rcases hxs with ⟨h, _⟩ | ⟨_, h1⟩
      · exact Bool.noConfusion h
      · omega⟩
    exact hg
  -- (5) inertia, no giving, standing receipt
  · intro v x z b hz hb; exact ⟨hz, hb.1⟩
  · intro hC
    obtain ⟨_, hg⟩ := hC () () false 1 ⟨rfl, Or.inr ⟨rfl, le_refl 1⟩⟩
    exact hg
  · intro hO
    obtain ⟨_, hg⟩ := hO () false () 1 rfl ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs hxs => by
      rcases hxs with ⟨h, _⟩ | ⟨_, h1⟩
      · exact Bool.noConfusion h
      · omega⟩
    exact hg
  -- (6) sustaining, standing receipt
  · intro v x z t hz hx; exact ⟨hz, hx⟩
  · intro v x z b hz hb; exact ⟨hz, hb.1⟩
  · rintro v z x t ⟨rfl, hx⟩
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · rintro v x t z rfl hx
    rcases hx with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩

end TruthCore.Results.Causality.PresentReceipt
