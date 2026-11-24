module

public import TruthCore.Causality.StrictGroundRepresentation
public import TruthCore.Results.Causality.DependenceStrictGroundMapStrength.Solution

@[expose] public section
namespace TruthCore.Results.Causality.StrictGroundRepresentation

open TruthCore.Causality.StrictGroundRepresentation
open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.DependenceStrictGroundMapStrength
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open TruthCore.Results.Modern.Fine.InfiniteDescent
open Relation

private theorem generatedMap {B Atom : Type} (D : B → B → Prop) (label : B → Atom) :
    DependenceMapsToStrictExistenceGround D label (edgeTheory D label) := by
  intro x y hne hD
  exact Derivable.assumption ⟨_, _, ⟨x, y, ⟨hne, hD⟩, rfl, rfl⟩, rfl⟩

private theorem pathToGround {B Atom : Type} {D : B → B → Prop} {label : B → Atom}
    {S : Set (Sequent Atom)} (hMap : DependenceMapsToStrictExistenceGround D label S)
    {a b : Atom} (path : TransGen (Projected D label) a b) : StrictlyGrounds S a b := by
  apply transGen_strict
  apply TransGen.mono _ _ _ path
  rintro _ _ ⟨x, y, ⟨hne, hD⟩, rfl, rfl⟩
  exact hMap x y hne hD

/-- Rank a label by the set of labels that reach it. Each acyclic step
strictly enlarges this set: its target was absent from the source's set. -/
private theorem generatedExact {B Atom : Type} [Nonempty Atom]
    (D : B → B → Prop) (label : B → Atom)
    (acyclic : ∀ a, ¬ TransGen (Projected D label) a a) :
    Consistent (edgeTheory D label) ∧
    ∀ a b, StrictlyGrounds (edgeTheory D label) a b ↔ TransGen (Projected D label) a b := by
  let reach := Projected D label
  let rank (v : Atom) : Set Atom := {u | ReflTransGen reach u v}
  have valid : ∀ s ∈ edgeTheory D label, HoldsAtRank rank s := by
    rintro _ ⟨a, b, step, rfl⟩
    change rank a ⊂ rank b
    refine (Set.ssubset_iff_of_subset (fun _ h => ReflTransGen.tail h step)).mpr ?_
    exact ⟨b, ReflTransGen.refl, fun back => acyclic b (TransGen.tail' back step)⟩
  have reflects {a b : Atom} (h : StrictlyGrounds (edgeTheory D label) a b) :
      TransGen reach a b := by
    have lt : rank a ⊂ rank b := holdsAtRank_of_derivable rank valid h
    have path : ReflTransGen reach a b := lt.le (show a ∈ rank a from ReflTransGen.refl)
    rcases reflTransGen_iff_eq_or_transGen.mp path with eq | path
    · subst b
      exact False.elim ((lt_irrefl _) lt)
    · exact path
  obtain ⟨v⟩ := ‹Nonempty Atom›
  exact ⟨⟨.strictPartial v v, fun h => acyclic v (reflects h)⟩,
    fun _ _ => ⟨reflects, pathToGround (generatedMap D label)⟩⟩

theorem fixedLabelCriterion : FixedLabelCriterion := by
  intro B Atom _ D label
  constructor
  · rintro ⟨S, consistent, mapped⟩ a cycle
    exact strictIrrefl consistent a (pathToGround mapped cycle)
  · intro acyclic
    exact ⟨edgeTheory D label, (generatedExact D label acyclic).1, generatedMap D label⟩

theorem identityRepresentation : IdentityRepresentation := by
  intro B _ D
  have reverse : Projected D id = Function.swap (DistinctEdge D) := by
    funext a b
    apply propext
    constructor
    · rintro ⟨x, y, h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨b, a, h, rfl, rfl⟩
  constructor
  · intro acyclic
    have paths (a b : B) : TransGen (Projected D id) a b ↔ TransGen (DistinctEdge D) b a := by
      rw [reverse, transGen_swap]
    obtain ⟨consistent, exactPaths⟩ := generatedExact D id (fun a h => acyclic a ((paths a a).mp h))
    exact ⟨consistent, fun a b => (exactPaths a b).trans (paths a b)⟩
  · rintro ⟨consistent, _⟩
    exact DependenceStrictGroundMapStrength.mapForcesDistinctDependenceAcyclic
      D id (edgeTheory D id) consistent (generatedMap D id)

theorem labelCycle : Control.LabelCycle := by
  open TruthCore.Causality.StrictGroundRepresentation.Control in
    have endpoints : ∀ {x y}, TransGen (DistinctEdge twoPairs) x y → twoPairs x y := by
      intro x y path
      induction path with
      | single h => exact h.2
      | tail _ step ih => exact ⟨ih.1, step.2.2.1, ih.2.2.trans step.2.2.2⟩
    refine ⟨fun x h => ?_, fun x y path => ?_, fun represented => ?_⟩
    · have h' := endpoints h
      exact Bool.noConfusion (h'.1.symm.trans h'.2.1)
    · obtain ⟨x, u⟩ := x
      obtain ⟨y, v⟩ := y
      obtain ⟨hu, hv, hxy⟩ := endpoints path
      change u = false at hu
      change v = true at hv
      change x = y at hxy
      subst u
      subst v
      subst y
      cases x <;> decide
    · have ab : Projected twoPairs sharedLabel false true :=
        ⟨(true,false), (true,true), ⟨by decide, rfl, rfl, rfl⟩, rfl, rfl⟩
      have ba : Projected twoPairs sharedLabel true false :=
        ⟨(false,false), (false,true), ⟨by decide, rfl, rfl, rfl⟩, rfl, rfl⟩
      exact (fixedLabelCriterion twoPairs sharedLabel).mp represented false ((TransGen.single ab).tail ba)

theorem nonmutualOfAcyclic {B : Type} (D : B → B → Prop)
    (acyclic : DistinctDependenceAcyclic D) : DistinctBeingsNotMutuallyDependent D := by
  intro x y ne xy yx
  exact acyclic x ((TransGen.single ⟨ne, xy⟩).tail ⟨ne.symm, yx⟩)

open TruthCore.Latin.Aquinas.SummaTheologiae

theorem foundedFromAncestralLabels {B Atom : Type} (cause D : B → B → Prop)
    (label : B → Atom) (S : Set (Sequent Atom))
    (consistent : Consistent S) (mapped : DependenceMapsToStrictExistenceGround D label S)
    (links : PerSeDependenceLinks cause D) (finiteLabels : FiniteAncestralLabels cause label) :
    NoInfinitePerSeEfficientCauseSeriesReading cause := by
  intro x
  let labels := label '' {y | ReflTransGen cause y x}
  let R (a b : labels) := StrictlyGrounds S a.val b.val
  let : Finite labels := finiteLabels x
  let : IsTrans labels R := ⟨fun _ _ _ => Modern.Fine.PlgDerivedRules.strictTrans⟩
  let : Std.Irrefl R := ⟨fun a => strictIrrefl consistent a.val⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl R
  have liftAcc (a : labels) : ∀ y, ReflTransGen cause y x → label y = a.val → Acc cause y := by
    induction a using wf.induction with
    | h a ih =>
      intro y path eq
      constructor
      intro z step
      have before := path.head step
      let b : labels := ⟨label z, z, before, rfl⟩
      apply ih b _ z before rfl
      have dep := links z y step
      change StrictlyGrounds S (label z) a.val
      rw [← eq]
      exact mapped y z dep.1 dep.2
  exact liftAcc ⟨label x, x, .refl, rfl⟩ x .refl rfl

end TruthCore.Results.Causality.StrictGroundRepresentation
