module

public import TruthCore.Causality.ActualAncestralSource
public import TruthCore.Results.Causality.NarGrafts.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ActualAncestralSource
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.ConcreteRootAccess (UniversalRootAccess)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.ActualAncestralSource
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.GodMaximalCausal (GodCausesBeingOfAllOthers)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Case.Catholicism (GodExists)
open TruthCore.Logic (ExcludedMiddle)

open TruthCore.Causality (FiniteCausalPath)
open TruthCore.Causality.CogitoNecessaryConcrete (GroundAncestor ActualConcreteGround)
open TruthCore.Causality.ConcreteRootAccess (RootAccess)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)

private theorem sourceIffRoot {W B : Type} (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) : (graph m w).Source x ↔ ActualRoot m w x.val := by
  constructor
  · intro hs
    refine ⟨x.property, fun y hy => hs ⟨⟨y, hy.1, hy.2.1⟩, hy.2.2⟩⟩
  · rintro ⟨_, hr⟩ ⟨y, hy⟩
    exact hr y.val ⟨y.property.1, y.property.2, hy⟩

theorem commonAncestryOfUniqueAndAccess {W B : Type} (m : Profile W B) (w : W)
    (hUnique : UniqueActualRootAt m w) (hAccess : UniversalRootAccess m w) :
    CommonActualGroundingAncestry m w := by
  obtain ⟨n, hn, unique⟩ := hUnique
  let root : {b // ActualConcrete m w b} := ⟨n, hn.1⟩
  refine ⟨root, (sourceIffRoot m w root).mpr hn, fun y hy =>
    Subtype.ext (unique y.val ((sourceIffRoot m w y).mp hy)), ?_⟩
  have path {x : B} (h : RootAccess m w x) : ∀ hx : ActualConcrete m w x,
      FiniteCausalPath (graph m w).edge ⟨x, hx⟩ root := by
    induction h with
    | root hr =>
      intro _
      obtain rfl := unique _ hr
      exact .same _
    | @step y x _ _ hg ih =>
      intro hx
      let supplier : {b // ActualConcrete m w b} := ⟨y, hg.1, hg.2.1⟩
      have edge : (graph m w).edge supplier ⟨x, hx⟩ := hg.2.2
      exact .link edge (ih supplier.property)
  exact fun x => path (hAccess x.val x.property) x.property

theorem rootAccessOfCommonAncestry {W B : Type} (m : Profile W B) (w : W)
    (h : CommonActualGroundingAncestry m w) : UniversalRootAccess m w := by
  obtain ⟨s, hs, _, reach⟩ := h
  have access {x y : {b // ActualConcrete m w b}}
      (p : FiniteCausalPath (graph m w).edge x y) : ActualRoot m w y.val → RootAccess m w x.val := by
    induction p with
    | same => exact fun hr => .root hr
    | @link x y z hEdge _ ih =>
      exact fun hr => .step (ih hr) x.property ⟨y.property.1, y.property.2, hEdge⟩
  intro x hx
  exact access (reach ⟨x, hx⟩) ((sourceIffRoot m w s).mp hs)

theorem uniqueOfCommonAncestry {W B : Type} (m : Profile W B) (w : W)
    (h : CommonActualGroundingAncestry m w) : UniqueActualRootAt m w := by
  obtain ⟨s, hs, one, _⟩ := h
  refine ⟨s.val, (sourceIffRoot m w s).mp hs, fun x hx => ?_⟩
  exact congrArg Subtype.val (one ⟨x, hx.1⟩ ((sourceIffRoot m w ⟨x, hx.1⟩).mpr hx))

theorem ancestralNamingOfDirectCausing {W B R : Type} (m : Profile W B) (w : W)
    (IsGod : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hCausal : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hGround : EsseCauseIsActualConcreteGround m w CausesIn esse) (em : ExcludedMiddle) :
    GodReachesActualConcreta m w IsGod := by
  intro g hg x hx
  cases em (x = g) with
  | inl he => exact he ▸ Relation.ReflTransGen.refl
  | inr hne => exact .single (hGround g x (Ne.symm hne) hx (hCausal g x hg hne))

theorem namedRootOfReach {W B : Type} (m : Profile W B) (w : W) (IsGod : B → Prop)
    (hReach : GodReachesActualConcreta m w IsGod) (g n : B)
    (hg : IsGod g) (hn : ActualRoot m w n) : g = n := by
  obtain path := hReach g hg n hn.1
  cases path with
  | refl => rfl
  | tail _ edge => exact False.elim (hn.2 _ edge)

theorem commonAncestryOfNamedSource {W B : Type} (m : Profile W B) (w : W)
    (IsGod : B → Prop) (hGod : GodExists IsGod) (hRoot : ActualRootExistsAt m w)
    (hReach : GodReachesActualConcreta m w IsGod) : CommonActualGroundingAncestry m w := by
  obtain ⟨g, hg⟩ := hGod
  obtain ⟨n, hn⟩ := hRoot
  obtain rfl := namedRootOfReach m w IsGod hReach g n hg hn
  apply commonAncestryOfUniqueAndAccess m w
  · exact ⟨g, hn, fun x hx => (namedRootOfReach m w IsGod hReach g x hg hx).symm⟩
  · have access {x : B} (p : GroundAncestor m w g x) : ActualConcrete m w x → RootAccess m w x := by
      induction p with
      | refl => exact fun _ => .root hn
      | tail _ edge ih => exact fun hx => .step (ih ⟨edge.1, edge.2.1⟩) hx edge
    exact fun x hx => access (hReach g hg x hx) hx

open TruthCore.Causality.NarDerivation.Model (chainG chainGrounds)
open TruthCore.Causality.FirstMoverNecessity (groundProfile)
open TruthCore.Modal.PrussPowerPremises.Model (Bg allC)

theorem mediatedChain : MediatedControl := by
  refine ⟨TruthCore.Results.Causality.NarGrafts.mediatedOptimum, ?_⟩
  let m := groundProfile chainG allC chainGrounds
  have actual (x : Bg) : ActualConcrete m false x := by
    cases x with
    | g => exact ⟨trivial, Or.inl rfl⟩
    | d => exact ⟨trivial, Or.inr (Or.inl rfl)⟩
    | c => exact ⟨trivial, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have root : ActualRoot m false .d := by
    refine ⟨actual .d, fun x hx => ?_⟩
    rcases hx.2.2 with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he
  have dg : ActualConcreteGround m false .d .g := ⟨(actual .d).1, (actual .d).2, Or.inl ⟨rfl, rfl⟩⟩
  have gc : ActualConcreteGround m false .g .c := ⟨(actual .g).1, (actual .g).2, Or.inr ⟨rfl, rfl⟩⟩
  apply commonAncestryOfUniqueAndAccess m false
  · refine ⟨.d, root, fun x hx => ?_⟩
    cases x with
    | g => exact False.elim (hx.2 _ dg)
    | c => exact False.elim (hx.2 _ gc)
    | d => rfl
  · have middle : RootAccess m false .g := .step (.root root) (actual .g) dg
    intro x _
    cases x with
    | g => exact middle
    | c => exact .step middle (actual .c) gc
    | d => exact .root root

end TruthCore.Results.Causality.ActualAncestralSource
