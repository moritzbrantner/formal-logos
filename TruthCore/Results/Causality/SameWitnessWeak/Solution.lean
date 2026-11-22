module

public import TruthCore.Causality.ExistenceAccountIntegration

/-! Weaker sibling of the same-witness underived argument
(`TruthCore.Results.Causality.ExistenceAccountIntegration.sameWitnessUnderived`):
the two bridges `NoContingentGroundOfNecessary` and `NoNovelNecessarySupport`
replace `NecessaryPredecessorLifting`, with no actual reflexivity. The
identification of the necessary supporter with the actual exemplar supplies
the supporter's actual existence, which lifting supplied in the original.
Found in review of #1825; the proof follows the reviewer's sketch. -/

@[expose] public section

namespace TruthCore.Results.Causality.SameWitnessWeak

open TruthCore.Causality.ExistenceAccountIntegration
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived

/-- The actual concrete profile exemplar is necessary and underived, from the
two weaker bridges. A putative supporter is necessary (no contingent ground),
hence most real and identical with the exemplar; the exemplar exists actually,
and no novel necessary support moves the self-support edge to the actual world,
contradicting well-founded actual support. -/
theorem sameWitnessUnderivedFromBridges {W B : Type} (m : Profile W B) (p : RealityProfile B)
    (support : W → B → B → Prop) (w : W)
    (hActual : ActualConcreteProfile m p w)
    (hPopulation : NecessaryProfilePopulation m p w)
    (hUnique : MostRealUnique p)
    (hIdentify : NecessaryIsMostReal m.ontic p w)
    (hWF : WellFoundedPresentEsseSupport m.ontic support w)
    (hNoContingent : NoContingentGroundOfNecessary m.ontic support w)
    (hNoNovel : NoNovelNecessarySupport m.ontic support w) :
    UnderivedConcreteProfile m p support w := by
  obtain ⟨n, hc, he, hp⟩ := hActual
  have hn : NecessaryAt m.ontic w n := by
    intro v hv
    obtain ⟨y, hy, hyp⟩ := hPopulation v hv
    exact (hUnique n y hp hyp).symm ▸ hy
  refine ⟨n, hc, he, hp, hn, ?_⟩
  intro v source hSource hEdge
  have hSourceNecessary := hNoContingent v source n hSource hn hEdge
  have hSame : source = n := hUnique source n (hIdentify source hSourceNecessary) hp
  subst source
  have hActualEdge : PresentEsseSupport m.ontic support w n n :=
    ⟨he, hNoNovel v n n hSourceNecessary hn hSource hEdge⟩
  have noSelf : ∀ x, Acc (PresentEsseSupport m.ontic support w) x →
      ¬ PresentEsseSupport m.ontic support w x x := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hxx
      exact ih x hxx hxx
  exact noSelf n (hWF.apply n) hActualEdge

/-- Omission controls: each bridge is needed by this argument, given the other
inputs. -/
theorem weakSiblingOmissions : WeakSiblingOmissions := by
  refine ⟨⟨⟨(), trivial, trivial, fun _ => trivial⟩, fun _ _ => ⟨(), trivial, fun _ => trivial⟩,
      fun _ _ _ _ => rfl, fun _ _ _ => trivial,
      ⟨fun a => ⟨a, fun _ h => Bool.noConfusion h.2⟩⟩,
      fun _ _ _ _ _ _ => fun _ _ => trivial, ?_, ?_⟩,
    ⟨⟨false, trivial, Or.inl rfl, fun _ => rfl⟩, fun _ _ => ⟨false, Or.inl rfl, fun _ => rfl⟩,
      fun x y hx hy => (hx ()).trans (hy ()).symm, ?_,
      ⟨fun a => ⟨a, fun _ h => Bool.noConfusion h.2.1⟩⟩, ?_, ?_, ?_⟩⟩
  · intro h
    exact Bool.noConfusion (h true () () (fun _ _ => trivial) (fun _ _ => trivial) trivial rfl)
  · rintro ⟨n, _, _, _, _, hNo⟩
    exact hNo true n trivial rfl
  · intro x hx _
    rcases hx false trivial with h | h
    · exact h
    · exact Bool.noConfusion h
  · intro w s t hs _ _ hEdge
    obtain ⟨_, rfl, _⟩ := hEdge
    rcases hs false trivial with h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  · intro h
    have := h true true false (Or.inr rfl) (fun _ _ => Or.inl rfl) ⟨rfl, rfl, rfl⟩ false trivial
    rcases this with h | h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  · rintro ⟨n, _, _, hp, _, hNo⟩
    have hn : n = false := hp ()
    subst hn
    exact hNo true true (Or.inr rfl) ⟨rfl, rfl, rfl⟩

end TruthCore.Results.Causality.SameWitnessWeak
