module

public import TruthCore.Causality.SelectedPlgTheory
public import TruthCore.Results.Modern.Fine.InfiniteDescent.Solution
public import TruthCore.Results.Modern.Fine.StrictGroundAcyclic.Solution

@[expose] public section

namespace TruthCore.Results.Causality.SelectedPlgTheory

open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.SelectedPlgTheory
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.InfiniteDescent
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open Relation Sequent

private theorem strictEdgeDerivable {Atom : Type} {S : Set (Sequent Atom)} {a b : Atom}
    (edge : StrictEdge S a b) : StrictlyGrounds S a b := by
  rcases edge with h | ⟨premises, h, member⟩
  · exact Derivable.assumption h
  · exact Derivable.subsumptionStrictFullPartial (Derivable.assumption h) member

private theorem weakPathDerivable {Atom : Type} {S : Set (Sequent Atom)} {a b : Atom}
    (path : ReflTransGen (WeakEdge S) a b) : Derivable S (weakPartial a b) := by
  induction path with
  | refl => exact Derivable.subsumptionWeakFullPartial (Derivable.identity a) rfl
  | tail _ edge ih =>
    apply Derivable.transWeakWeak ih
    rcases edge with h | ⟨premises, h, member⟩ | h
    · exact Derivable.assumption h
    · exact Derivable.subsumptionWeakFullPartial (Derivable.assumption h) member
    · exact Derivable.subsumptionStrictPartial (strictEdgeDerivable h)

private theorem strictPathDerivable {Atom : Type} {S : Set (Sequent Atom)} {a b : Atom}
    (path : StrictPath S a b) : StrictlyGrounds S a b := by
  obtain ⟨u, v, before, step, after⟩ := path
  exact Derivable.transStrictWeak
    (Derivable.transWeakStrict (weakPathDerivable before) (strictEdgeDerivable step))
    (weakPathDerivable after)

theorem consistentOfNoStrictReturn {Atom : Type} (S : Set (Sequent Atom))
    (populated : PopulatedAtomType Atom) (noReturn : NoStrictReturn S) : Consistent S := by
  let rank (b : Atom) : Set Atom := {a | ReflTransGen (WeakEdge S) a b}
  have weakRank {a b} (edge : WeakEdge S a b) : rank a ⊆ rank b :=
    fun _ path => path.tail edge
  have strictRank {a b} (edge : StrictEdge S a b) : rank a ⊂ rank b :=
    (Set.ssubset_iff_of_subset (weakRank (Or.inr (Or.inr edge)))).mpr
      ⟨b, .refl, noReturn a b edge⟩
  have allAssumptions : ∀ s ∈ S, HoldsAtRank rank s := by
    intro s member
    cases s with
    | weakFull premises b => exact fun a h => weakRank (Or.inr (Or.inl ⟨premises, member, h⟩))
    | weakPartial a b => exact weakRank (Or.inl member)
    | strictFull premises b => exact fun a h => strictRank (Or.inr ⟨premises, member, h⟩)
    | strictPartial a b => exact strictRank (Or.inl member)
  obtain ⟨a⟩ := populated
  exact ⟨strictPartial a a, fun h => lt_irrefl _ (holdsAtRank_of_derivable rank allAssumptions h)⟩

theorem consistencyCriterion : ConsistencyCriterion := by
  intro Atom inhabited S
  constructor
  · intro consistent a b edge back
    exact strictIrrefl consistent a
      (Derivable.transStrictWeak (strictEdgeDerivable edge) (weakPathDerivable back))
  · exact consistentOfNoStrictReturn S inhabited

private def PathHolds {Atom : Type} (S : Set (Sequent Atom)) : Sequent Atom → Prop
  | weakFull premises b => ∀ a ∈ premises, ReflTransGen (WeakEdge S) a b
  | weakPartial a b => ReflTransGen (WeakEdge S) a b
  | strictFull premises b => ∀ a ∈ premises, StrictPath S a b
  | strictPartial a b => StrictPath S a b

private theorem pathHoldsOfDerivable {Atom : Type} {S : Set (Sequent Atom)}
    (consistent : Consistent S) {s : Sequent Atom} (h : Derivable S s) : PathHolds S s := by
  have weaken {a b} (path : StrictPath S a b) : ReflTransGen (WeakEdge S) a b := by
    obtain ⟨_, _, before, step, after⟩ := path
    exact (before.tail (Or.inr (Or.inr step))).trans after
  induction h with
  | assumption member =>
    rename_i s
    cases s with
    | weakFull premises _ => exact fun _ h => .single (Or.inr (Or.inl ⟨premises, member, h⟩))
    | weakPartial _ _ => exact .single (Or.inl member)
    | strictFull premises _ => exact fun a b => ⟨a, _, .refl, Or.inr ⟨premises, member, b⟩, .refl⟩
    | strictPartial a b => exact ⟨a, b, .refl, Or.inl member, .refl⟩
  | subsumptionStrictFull _ ih => exact fun a ha => weaken (ih a ha)
  | subsumptionStrictPartial _ ih => exact weaken ih
  | subsumptionStrictFullPartial _ ha ih => exact ih _ ha
  | subsumptionWeakFullPartial _ ha ih => exact ih _ ha
  | cut A Δ _ _ ihPremises ihCut =>
    intro a ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact (ihPremises i a hi).trans (ihCut (A i) ⟨i, rfl⟩)
  | transWeakWeak _ _ first second => exact first.trans second
  | transWeakStrict _ _ first second =>
    obtain ⟨u, v, before, step, after⟩ := second
    exact ⟨u, v, first.trans before, step, after⟩
  | transStrictWeak _ _ first second =>
    obtain ⟨u, v, before, step, after⟩ := first
    exact ⟨u, v, before, step, after.trans second⟩
  | identity a =>
    intro b hb
    change b = a at hb
    cases hb
    exact .refl
  | nonCircularity _ self _ => exact False.elim (strictIrrefl consistent _ self)
  | reverseSubsumption _ _ _ ihStrict => exact ihStrict

theorem strictDerivabilityCriterion : StrictDerivabilityCriterion := by
  intro Atom S consistent a b
  exact ⟨pathHoldsOfDerivable consistent, strictPathDerivable⟩

theorem mapOfStrictPaths {B Atom : Type} (D : B → B → Prop) (label : B → Atom)
    (S : Set (Sequent Atom)) (paths : DependenceHasStrictPaths D label S) :
    DependenceMapsToStrictExistenceGround D label S := by
  intro x y ne edge
  exact strictPathDerivable (paths x y ne edge)

open TruthCore.Causality.SelectedPlgTheory.Control

theorem presentationControls : PresentationControls := by
  have noStrict : ∀ a b, ¬ StrictEdge weakOnly a b := by
    intro a b
    simp [StrictEdge, weakOnly]
  have weakConsistent :=
    consistentOfNoStrictReturn weakOnly ⟨false⟩ (fun a b edge => (noStrict a b edge).elim)
  have forwardEdge : StrictEdge strictForward false true :=
    Or.inr ⟨{false}, rfl, rfl⟩
  have forwardNoReturn : NoStrictReturn strictForward := by
    intro a b edge back
    have endpoints : a = false ∧ b = true := by
      rcases edge with edge | ⟨premises, member, ha⟩
      · simp [strictForward] at edge
      · simp [strictForward] at member
        rcases member with ⟨rfl, rfl⟩
        exact ⟨ha, rfl⟩
    obtain ⟨rfl, rfl⟩ := endpoints
    have staysTrue {c : Bool} (path : ReflTransGen (WeakEdge strictForward) true c) : c = true := by
      induction path with
      | refl => rfl
      | tail _ step ih =>
        subst_vars
        simp [WeakEdge, StrictEdge, strictForward] at step
    cases staysTrue back
  have cycleEdge : StrictEdge withWeakReturn false true :=
    Or.inr ⟨{false}, Or.inr rfl, rfl⟩
  have returnEdge : WeakEdge withWeakReturn true false :=
    Or.inr (Or.inl ⟨{true}, Or.inl rfl, rfl⟩)
  refine ⟨weakConsistent, ?_, consistentOfNoStrictReturn strictForward ⟨false⟩ forwardNoReturn,
    ?_, ?_, ?_⟩
  · intro mapped
    obtain ⟨a, b, _, step, _⟩ :=
      (strictDerivabilityCriterion weakOnly weakConsistent false true).mp
        (mapped true false (by decide) ⟨rfl, rfl⟩)
    exact noStrict a b step
  · rintro _ _ _ ⟨rfl, rfl⟩
    exact strictEdgeDerivable forwardEdge
  · intro consistent
    exact (consistencyCriterion withWeakReturn).mp consistent false true cycleEdge (.single returnEdge)
  · rintro _ _ _ ⟨rfl, rfl⟩
    exact strictEdgeDerivable cycleEdge

end TruthCore.Results.Causality.SelectedPlgTheory
