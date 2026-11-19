module

public import TruthCore.Causality.SustainingDependence

@[expose] public section

namespace TruthCore.Results.Causality.SustainingDependence

open TruthCore.Causality.SustainingDependence
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization
open TruthCore.Causality.Round2Grounding (EsseEffectDependsOnItsCause)
open TruthCore.Modal.TemporalHistory (History BeginsAt)

/-- The sustaining sibling from contact and the co-presence bridge. If `c`,
distinct from `x`, causes `x`'s esse and gives `x` being at every moment at
which `x` is present, in every history, then by contact `c` is present at each
such moment; the co-presence bridge gives dependence. -/
theorem sustainingSiblingOfCoPresence {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop)
    (hContact : GiverPresentWhenGiving h G)
    (hBridge : CoPresentEsseCauseIsDependedOn h CausesIn esse DependsForBeing) :
    SustainingEsseCauseIsDependedOn h G CausesIn esse DependsForBeing := by
  intro c x hcx hC hGives
  exact hBridge c x hcx hC fun v t hxt => hContact v c x t (hGives v t hxt)

/-- The esse-dependence premise `2068f91c` from the weak sustaining reading
`ce55210c` and the sustaining sibling: a distinct cause of `x`'s esse sustains
`x` in every history in which `x` is present, so the sibling applies. -/
theorem esseDependenceOfSustaining {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop)
    (hSustaining : CausingAnothersBeingIsSustaining h G CausesIn esse)
    (hSibling : SustainingEsseCauseIsDependedOn h G CausesIn esse DependsForBeing) :
    EsseEffectDependsOnItsCause CausesIn esse DependsForBeing :=
  fun c x hcx hC => hSibling c x hcx hC fun v t hxt =>
    (hSustaining v c x hcx hC ⟨t, hxt⟩).2 t hxt

/-- Strength order: `2068f91c` entails its sustaining sibling. -/
theorem sustainingSiblingOfEsseDependence {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (DependsForBeing : B → B → Prop)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse DependsForBeing) :
    SustainingEsseCauseIsDependedOn h G CausesIn esse DependsForBeing :=
  fun c x hcx hC _ => hDep c x hcx hC

/-- Onset and parity give concurrent actualization for begun things. -/
theorem onceBegunOfOnsetParity {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop)
    (hOnset : ReceivedOnsetIsGiven h G EsseReceivedIn)
    (hParity : PersistenceParity h G EsseReceivedIn) :
    ConcurrentlyActualizedOnceBegun h G EsseReceivedIn :=
  fun v x z b hz hb => hParity v x z b hz hb (hOnset v x z b hz hb)

/-- Strength order: the weak concurrent actualization `40a97664` entails
concurrent actualization for begun things. -/
theorem onceBegunOfConcurrentlyActualized {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (EsseReceivedIn : B → P → Prop)
    (hActualized : ConcurrentlyActualized h G EsseReceivedIn) :
    ConcurrentlyActualizedOnceBegun h G EsseReceivedIn :=
  fun v x z _ hz _ t ht => hActualized v x t z hz ht

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.SustainingDependence.Control

/-- Omission, rival-reading, strictness and nonvacuity controls
(`Control.Certificate`). -/
theorem controls : TruthCore.Causality.SustainingDependence.Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  -- (1) parent and child
  · rintro v c x t ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, le_refl 1⟩
  · intro c x _ _ hCo; exact hCo
  · rintro c x _ ⟨rfl, rfl⟩ hGives
    have := hGives () 2 (Or.inr ⟨rfl, by decide⟩)
    exact absurd this.2.2 (by decide)
  · intro hS
    have := (hS () true false (by decide) ⟨rfl, rfl⟩ ⟨1, Or.inr ⟨rfl, le_refl 1⟩⟩).2 2
      (Or.inr ⟨rfl, by decide⟩)
    exact absurd this.2.2 (by decide)
  · intro hD
    have := hD true false (by decide) ⟨rfl, rfl⟩ () 2 (Or.inr ⟨rfl, by decide⟩)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · exact Bool.noConfusion h
  -- (2) no dependence
  · rintro v c x _ ⟨rfl, rfl⟩ hx
    exact ⟨hx, fun t ht => by
      rcases ht with h | ⟨_, ht⟩
      · exact Bool.noConfusion h
      · exact ⟨rfl, rfl, ht⟩⟩
  · rintro v c x t ⟨rfl, rfl, _⟩
    exact Or.inl rfl
  · intro hB
    exact hB true false (by decide) ⟨rfl, rfl⟩ fun _ _ _ => Or.inl rfl
  · intro hS
    refine hS true false (by decide) ⟨rfl, rfl⟩ fun v t ht => ?_
    rcases ht with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨rfl, rfl, ht⟩
  · intro hD; exact hD true false (by decide) ⟨rfl, rfl⟩
  -- (3) absent giver
  · rintro v c x _ ⟨rfl, rfl⟩ hx
    exact ⟨hx, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro c x _ _ hCo; exact hCo
  · intro hC
    have := hC () true false 0 ⟨rfl, rfl⟩
    exact Bool.noConfusion this.1
  · intro hS
    have := hS true false (by decide) ⟨rfl, rfl⟩ (fun _ _ _ => ⟨rfl, rfl⟩)
      () 1 ⟨rfl, le_refl 1⟩
    exact Bool.noConfusion this.1
  · intro hD
    have := hD true false (by decide) ⟨rfl, rfl⟩ () 1 ⟨rfl, le_refl 1⟩
    exact Bool.noConfusion this.1
  -- (4) nonvacuity
  · rintro v c x _ ⟨rfl, rfl⟩ hx
    exact ⟨hx, fun t ht => by
      rcases ht with h | ⟨_, ht⟩
      · exact Bool.noConfusion h
      · exact ⟨rfl, rfl, ht⟩⟩
  · rintro v c x t ⟨rfl, rfl, _⟩
    exact Or.inl rfl
  · intro c x _ _ hCo; exact hCo
  · intro c x _ hC _
    obtain ⟨rfl, rfl⟩ := hC
    intro _ _ _; exact Or.inl rfl
  · rintro c x _ ⟨rfl, rfl⟩ _ _ _
    exact Or.inl rfl
  · intro _ _ _; exact Or.inl rfl
  -- (5) inertia: onset given, parity fails
  · rintro v x z b rfl ⟨hb, hfirst⟩
    rcases hb with ⟨h, _⟩ | ⟨_, hb1⟩
    · exact Bool.noConfusion h
    · have : b = 1 := by
        by_contra hne
        exact hfirst 1 (by omega) (Or.inr ⟨rfl, le_refl 1⟩)
      subst this
      exact ⟨true, rfl, rfl, rfl⟩
  · intro hP
    obtain ⟨g, hg⟩ := hP () false () 1 rfl
      ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs h => by
        rcases h with ⟨h, _⟩ | ⟨_, h⟩
        · exact Bool.noConfusion h
        · omega⟩
      ⟨true, rfl, rfl, rfl⟩ 2 (Or.inr ⟨rfl, by decide⟩)
    exact absurd hg.2.2 (by decide)
  · intro hA
    obtain ⟨g, hg⟩ := hA () false () 1 rfl
      ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs h => by
        rcases h with ⟨h, _⟩ | ⟨_, h⟩
        · exact Bool.noConfusion h
        · omega⟩ 2 (Or.inr ⟨rfl, by decide⟩)
    exact absurd hg.2.2 (by decide)
  -- (6) inertia with no giving
  · rintro v x z b _ _ ⟨_, h⟩
    exact h.elim
  · intro hO
    obtain ⟨_, h⟩ := hO () false () 1 rfl
      ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs h => by
        rcases h with ⟨h, _⟩ | ⟨_, h⟩
        · exact Bool.noConfusion h
        · omega⟩
    exact h
  · intro hA
    obtain ⟨_, h⟩ := hA () false () 1 rfl
      ⟨Or.inr ⟨rfl, le_refl 1⟩, fun s hs h => by
        rcases h with ⟨h, _⟩ | ⟨_, h⟩
        · exact Bool.noConfusion h
        · omega⟩ 1 (Or.inr ⟨rfl, le_refl 1⟩)
    exact h
  -- (7) sustained
  · rintro v x z b rfl ⟨hb, _⟩
    rcases hb with h | ⟨_, hb1⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, hb1⟩
  · rintro v x z b rfl _ _ t ht
    rcases ht with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩
  · rintro v x z b rfl _ t ht
    rcases ht with h | ⟨_, ht⟩
    · exact Bool.noConfusion h
    · exact ⟨true, rfl, rfl, ht⟩

end TruthCore.Results.Causality.SustainingDependence
