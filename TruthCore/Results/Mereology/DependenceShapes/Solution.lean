module

public import TruthCore.Mereology.DependenceShapes
public import TruthCore.Results.Mereology.AtomlessFusionProfile.Solution
public import TruthCore.Results.Mereology.SumOneComplementation.Solution

@[expose] public section
namespace TruthCore.Results.Mereology.DependenceShapes
open TruthCore.Mereology.DependenceShapes
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.AtomlessFusionProfile
open TruthCore.Logic.Regress TruthCore.Causality

theorem shapeControl : ShapeControl := by
  let G : Graph Unit := ⟨fun _ _ => True⟩
  refine ⟨fun _ H h => H.controls_of_wellFounded h, ?_, Nat.lt_succ_self,
    Nat.lt_irrefl, fun _ _ _ h₁ h₂ => h₁.trans h₂, ?_⟩
  · refine ⟨G, fun _ => trivial, ?_, ?_, fun x => .intrinsic x trivial, ?_, ?_⟩
    · rintro ⟨f, hf⟩
      exact Nat.zero_ne_one (hf (Subsingleton.elim (f 0) (f 1)))
    · intro hw
      exact ((G.controls_of_wellFounded hw).1 ()) (.single trivial)
    · apply le_antisymm ?_ (Set.empty_subset _)
      apply (G.transmission (fun _ => False)).lfp_le
      intro x hx
      rcases hx with hi | ⟨y, _, hy⟩
      · exact hi.elim
      · exact hy
    · apply le_antisymm (Set.subset_univ _) ?_
      apply (G.transmission (fun _ => False)).le_gfp
      intro x _
      exact Or.inr ⟨(), trivial, trivial⟩
  · intro hw
    exact hw.not_rightTotal (fun n => ⟨n + 1, Nat.lt_succ_self n⟩)

private theorem noAcc_of_composite {B : Type} [PartialOrder B]
    (h : ∀ x : B, Composite x) : ∀ x : B, ¬ Acc (fun y x : B => y < x) x := by
  intro x hx
  induction hx with
  | intro x _ ih =>
    obtain ⟨p, hp⟩ := h x
    exact ih p hp

private theorem star_wf {B : Type} (u : B) : WellFounded (wholeStar u).edge := by
  have hu : Acc (wholeStar u).edge u :=
    .intro u (fun _ h => (h.2 rfl).elim)
  exact ⟨fun x => .intro x (fun y h => h.1 ▸ hu)⟩

private theorem reverse_not_wf : ¬ WellFounded (fun y x : Region => x < y) := by
  classical
  let Proper := {x : RegionAlgebra // x ≠ ⊥ ∧ x ≠ ⊤}
  have hc := TruthCore.Results.Mereology.AtomlessFusionProfile.gunkModel.2.2.1
  obtain ⟨U⟩ := TruthCore.Results.Mereology.AtomlessFusionProfile.gunkModel.1
  obtain ⟨p, hp⟩ := hc U
  have proper_below (x : Region) (y : Region) (hy : y < x) : y.val ≠ ⊤ := by
    exact ne_top_of_lt (lt_of_lt_of_le hy le_top)
  let : Nonempty Proper := ⟨⟨p.val, p.property, proper_below U p hp⟩⟩
  have hall : ∀ x : Proper, Composite x := by
    intro x
    obtain ⟨y, hy⟩ := hc ⟨x.val, x.property.1⟩
    exact ⟨⟨y.val, y.property, proper_below _ y hy⟩, hy⟩
  let down : Graph Proper := ⟨fun y x => y < x⟩
  let up : Graph Region := ⟨fun y x => x < y⟩
  let flip : down.Map up :=
    ⟨fun x => ⟨x.valᶜ, by simpa using x.property.2⟩,
      fun {y x} h => by
        change x.valᶜ < y.valᶜ
        exact compl_lt_compl_iff_lt.mpr (show y.val < x.val from h)⟩
  intro hw
  exact (noAcc_of_composite hall (Classical.choice inferInstance))
    ((flip.wellFounded hw).apply _)

theorem priorityControl : PriorityControl := by
  classical
  have hg := TruthCore.Results.Mereology.AtomlessFusionProfile.gunkModel
  have hc := hg.2.2.1
  have noAcc := noAcc_of_composite hc
  refine ⟨hg, ?_, ?_, ?_, reverse_not_wf, ?_, ?_, inferInstance, inferInstance⟩
  · intro U
    obtain ⟨f, hf, hs⟩ := not_acc_iff_exists_descending_chain.mp (noAcc U)
    exact ⟨f, hf, (strictAnti_nat_of_succ_lt hs).injective, hs⟩
  · intro hw
    obtain ⟨U⟩ := hg.1
    exact noAcc U (hw.apply U)
  · intro f hf n
    exact (hf n).not_gt
  · have hn : (⊤ : RegionAlgebra) ≠ ⊥ := by
      obtain ⟨U⟩ := hg.1
      exact ne_bot_of_le_ne_bot U.property le_top
    let u : Region := ⟨⊤, hn⟩
    refine ⟨u, fun _ => (show _ ≤ (⊤ : RegionAlgebra) from le_top), star_wf u, ?_, ?_⟩
    · intro x
      constructor
      · intro hs
        by_contra h
        exact hs ⟨u, rfl, h⟩
      · intro h ⟨y, _, hn⟩
        exact hn h
    · intro h
      obtain ⟨x, hx⟩ := hc u
      obtain ⟨p, hp⟩ := hc x
      have he := (h p x hp).1
      exact hx.ne he
  · intro U hU
    obtain ⟨p, hp⟩ := hc ⟨U, hU.ne_bot⟩
    exact p.property (hU.2 p.val hp)

private theorem min_same {B : Type} [PartialOrder B] (x y : B)
    (hx : IsMin x) (hy : IsMin y) : SameProperParts x y := by
  intro p
  exact ⟨fun h => (h.not_ge (hx h.le)).elim,
    fun h => (h.not_ge (hy h.le)).elim⟩

private theorem composite_extensional {B : Type} [PartialOrder B]
    (hs : TruthCore.Mereology.SupplementationFusion.StrongSupplementation B) :
    CompositeExtensionality B := by
  have lower {x y : B} (hx : Composite x) (same : SameProperParts x y) : x ≤ y := by
    by_contra hxy
    obtain ⟨z, hzx, hno⟩ := hs x y hxy
    by_cases he : z = x
    · obtain ⟨p, hp⟩ := hx
      exact hno ⟨p, he ▸ hp.le, ((same p).mp hp).le⟩
    · have hz : z < x := lt_of_le_of_ne hzx he
      exact hno ⟨z, le_rfl, ((same z).mp hz).le⟩
  intro x y hx hy same
  exact le_antisymm (lower hx same) (lower hy (fun p => (same p).symm))

private theorem atom_min (b : Bool) : IsMin (atom b) := by
  intro p hp
  obtain ⟨c, hc⟩ := p.property
  have hcb : c = b := hp hc
  have hbp : b ∈ p.val := hcb ▸ hc
  intro d hd
  exact (Set.mem_singleton_iff.mp hd) ▸ hbp

private theorem atoms_distinct : atom false ≠ atom true := by
  intro h
  have hf : false ∈ (atom true).val := h ▸ (show false ∈ (atom false).val from rfl)
  exact Bool.noConfusion hf

theorem extensionalityControl : ExtensionalityControl := by
  have ha := TruthCore.Results.Mereology.AtomlessFusionProfile.atomicModel
  have hs := TruthCore.Results.Mereology.SumOneComplementation.strongOfComplementation
    Body ha.2.1.1
  refine ⟨?_, fun _ _ hs => composite_extensional hs, ha,
    composite_extensional hs, atom_min false, atom_min true, atoms_distinct,
    min_same _ _ (atom_min false) (atom_min true), ?_⟩
  · intro B _ h x y hx hy
    exact h x y (min_same x y hx hy)
  · intro h
    exact atoms_distinct (h _ _ (min_same _ _ (atom_min false) (atom_min true)))

end TruthCore.Results.Mereology.DependenceShapes
