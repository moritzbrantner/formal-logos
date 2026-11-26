module

public import TruthCore.Causality.PerSeRegressCardinality
public import TruthCore.Results.Causality.WorldSourceRegress.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PerSeRegressCardinality
open TruthCore.Causality.PerSeRegressCardinality
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.Regress
open TruthCore.Results.Causality.WorldSourceRegress (chain_injective)

private theorem background_of_edge {Being : Type} (edge prior : Being → Being → Prop)
    (populated : ∃ cause effect, edge cause effect) (subset : edge ≤ prior)
    (irrefl : ∀ x, ¬ prior x x) : SecondWayBackground edge prior := by
  obtain ⟨cause, effect, link⟩ := populated
  exact ⟨⟨cause, effect, (), link⟩, fun _ _ _ h => subset _ _ h, irrefl,
    fun _ _ _ _ he ⟨earlier, _, hp⟩ => ⟨he, earlier, hp⟩⟩

private theorem noCycles_of_order {Being : Type} {edge prior : Being → Being → Prop}
    [IsTrans Being prior] (subset : edge ≤ prior) (irrefl : ∀ x, ¬ prior x x) :
    Graph.NoCycles ⟨edge⟩ := by
  intro x cycle
  exact irrefl x (Relation.transGen_minimal subset x x cycle)

theorem successorOrientationAndFiniteCycle : SuccessorOrientationAndFiniteCycle := by
  let forward := successorEdge
  let backward := Function.swap successorEdge
  have forwardPrior : forward ≤ (· < ·) := by
    intro cause effect link
    exact (show effect = cause + 1 from link) ▸ Nat.lt_succ_self cause
  have backwardPrior : backward ≤ (· > ·) := fun _ _ link => forwardPrior _ _ link
  have forwardAcyclic := noCycles_of_order forwardPrior Nat.lt_irrefl
  let : IsTrans Nat (· > ·) := ⟨fun _ _ _ ab bc => Nat.lt_trans bc ab⟩
  have backwardAcyclic := noCycles_of_order backwardPrior (fun x => Nat.lt_irrefl x)
  have anchored (x : Nat) : AnchoredRegress ⟨asCaused backward⟩ x := by
    let f : Nat → Nat := fun n => x + n
    have step : ∀ n, asCaused backward (f (n + 1)) (f n) := fun n =>
      ⟨rfl, f (n + 1) + 1, rfl⟩
    have subset : asCaused backward ≤ backward := fun _ _ h => h.1
    have acyclic : Graph.NoCycles ⟨asCaused backward⟩ := fun node cycle =>
      backwardAcyclic node (Relation.TransGen.mono subset node node cycle)
    exact ⟨f, Nat.add_zero x, chain_injective ⟨asCaused backward⟩ acyclic f step, step⟩
  refine ⟨⟨background_of_edge forward (· < ·) ⟨0, 1, rfl⟩ forwardPrior Nat.lt_irrefl,
    forwardAcyclic, ?_, ?_⟩,
    ⟨background_of_edge backward (· > ·) ⟨1, 0, rfl⟩ backwardPrior
      (fun x => Nat.lt_irrefl x), backwardAcyclic, anchored, ?_, ?_⟩, ?_⟩
  · exact (Subrelation.wf (fun h => forwardPrior _ _ h.1) Nat.lt_wfRel.wf).apply
  · exact ⟨⟨1, (), rfl⟩, fun c _ h => Nat.not_lt_zero c (forwardPrior c 0 h)⟩
  · intro wellFounded
    obtain ⟨f, startsAtZero, _, step⟩ := anchored 0
    exact not_acc_iff_exists_descending_chain.mpr ⟨f, startsAtZero, step⟩ (wellFounded 0)
  · rintro ⟨first, _, noCause⟩
    exact noCause (first + 1) () rfl
  · let edge := asCaused (fun cause effect : Bool => cause ≠ effect)
    have flipLink : ∀ x, edge (!x) x := by
      intro x
      exact ⟨by cases x <;> decide, x, by cases x <;> decide⟩
    let f : Nat → Bool := fun n => Nat.rec false (fun _ x => !x) n
    have step : ∀ n, edge (f (n + 1)) (f n) := fun n => flipLink (f n)
    refine ⟨inferInstance, fun x h => h.1 rfl, ?_, ⟨f, step⟩,
      not_injective_infinite_finite, ?_⟩
    · exact ⟨false, (Relation.TransGen.single (flipLink true)).tail (flipLink false)⟩
    · intro wellFounded
      exact not_acc_iff_exists_descending_chain.mpr ⟨f, rfl, step⟩ (wellFounded false)

end TruthCore.Results.Causality.PerSeRegressCardinality
