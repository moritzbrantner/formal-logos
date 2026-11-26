module

public import TruthCore.Causality.GivingChoice
public import TruthCore.Results.Causality.BenefitPlanWitness.Solution
public import TruthCore.Results.Causality.GivingChoice.Solution

/-! Finite controls of the local STIT semantics. Two choices can be
independently combined in the product frame. The same outcome valuation
also distinguishes success, settling, and the ability to prevent success. -/

@[expose] public section

namespace TruthCore.Models.STITControls

open TruthCore.Modal.STIT
open TruthCore.Modal.DeonticFutureBoundary (Ought Can)
open TruthCore.Causality.GivingChoice
open TruthCore.Causality.ThroughWill (RationallyGivesAt)
open TruthCore.Causality.ThroughWill.Control (model agency)
open TruthCore.Causality.NarDerivation (FixedTowardAt)
open TruthCore.Causality.WillVersusChance (WilledTwoWayAt)
open TruthCore.Modal.WillChoiceCensus (Output includes optimal quality tiedOptima)

abbrev Hist := Bool × Bool

/-- A common decision node and four distinct leaves. The switches let us
test the two additional frame constraints on otherwise identical cells. -/
def decision (correlated sharedFuture : Bool) : BranchingFrame (Fin 5) Hist Bool where
  traverses m h := m = 0 ∨ sharedFuture = true ∨ m.val = 1 + h.1.toNat * 2 + h.2.toNat
  choice _ a := Setoid.ker fun h => if correlated || !a then h.val.1 else h.val.2

def here (correlated sharedFuture : Bool) (h : Hist) :
    (decision correlated sharedFuture).Through 0 :=
  ⟨h, Or.inl rfl⟩

def actual := here false false (true, true)
def left (k : (decision false false).Through 0) : Prop := k.val.1 = true
def right (k : (decision false false).Through 0) : Prop := k.val.2 = true

theorem independent : Independent (decision false false) 0 := by
  intro selected
  refine ⟨here false false ((selected false).val.1, (selected true).val.2), ?_⟩
  intro a
  cases a <;> rfl

theorem correlated_not_independent : ¬ Independent (decision true false) 0 := by
  intro independent
  obtain ⟨k, hk⟩ := independent (fun a => here true false (a, false))
  have hFalse : false = k.val.1 := hk false
  have hTrue : true = k.val.1 := hk true
  cases hFalse.trans hTrue.symm

theorem noChoiceBetweenUndivided : NoChoiceBetweenUndivided (decision false false) 0 := by
  intro a h k
  rintro ⟨n, hn, hh, hk⟩
  have nonzero : n ≠ 0 := ne_of_gt hn
  rcases hh with hz | impossible | hh
  · exact (nonzero hz).elim
  · cases impossible
  rcases hk with hz | impossible | hk
  · exact (nonzero hz).elim
  · cases impossible
  have equal : h.val = k.val := by
    obtain ⟨⟨a₁, b₁⟩, _⟩ := h
    obtain ⟨⟨a₂, b₂⟩, _⟩ := k
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;>
      simp at hh hk ⊢ <;> omega
  exact congrArg (fun v : Hist => if false || !a then v.1 else v.2) equal

theorem canSplitUndivided : ¬ NoChoiceBetweenUndivided (decision false true) 0 := by
  intro noSplit
  have related := noSplit false (here false true (false, false)) (here false true (true, false))
    ⟨1, by decide, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
  change false = true at related
  cases related

/-- The first agent does not settle the second coordinate even though the
observed outcome succeeds and is historically possible. -/
theorem accidental : right actual ∧ Can (historical _ _) actual right ∧
    ¬ Cstit false actual right ∧ ¬ CanEnsure (historical _ _) false actual right := by
  refine ⟨rfl, ⟨actual, trivial, rfl⟩, ?_, ?_⟩
  · intro ensure
    exact Bool.noConfusion (ensure (here false false (true, false)) rfl)
  · rintro ⟨k, _, ensure⟩
    exact Bool.noConfusion (ensure (here false false (k.val.1, false)) rfl)

theorem forced : Cstit false actual (fun _ => True) ∧ ¬ Dstit false actual (fun _ => True) :=
  ⟨necessary_cstit (fun _ => trivial), necessary_not_dstit (fun _ => trivial)⟩

theorem alternatives : Dstit false actual left ∧
    CanEnsure (historical _ _) false actual (fun k => ¬ left k) := by
  have positive : Cstit false actual left := fun _ hk => hk.symm
  have negative : CanEnsure (historical _ _) false actual (fun k => ¬ left k) :=
    ⟨here false false (false, true), trivial, fun _ hk yes => Bool.noConfusion (hk.trans yes)⟩
  exact ⟨dstit_of_canEnsure_not positive negative, negative⟩

/-- Someone can ensure success by choosing the left coordinate. Failure is
possible, but every cell includes a success via the right coordinate. -/
theorem dstitWithoutPreventing :
    Dstit false actual (fun k => left k ∨ right k) ∧
    ¬ CanEnsure (historical _ _) false actual (fun k => ¬ (left k ∨ right k)) := by
  refine ⟨⟨fun _ hk => Or.inl hk.symm, ?_⟩, ?_⟩
  · intro settled
    exact (settled (here false false (false, false))).elim Bool.noConfusion Bool.noConfusion
  · rintro ⟨k, _, prevent⟩
    exact prevent (here false false (k.val.1, true)) rfl (Or.inr rfl)

/-- An ideal that asks for the left coordinate to be false, and a feasible
relation permitting only left=true cells, yield obligation without feasible
fulfillment in this assignment. Both successor sets are nonempty. -/
theorem obligationBlocked :
    let ideal : TruthCore.Modal.Frame ((decision false false).Through 0) := ⟨fun _ k => ¬ left k⟩
    let available : TruthCore.Modal.Frame ((decision false false).Through 0) := ⟨fun _ k => left k⟩
    Ought ideal actual (fun k => ¬ left k) ∧
      Can (historical _ _) actual (fun k => ¬ left k) ∧
      Can available actual left ∧ ¬ Can available actual (fun k => ¬ left k) := by
  exact ⟨fun _ hk => hk, ⟨here false false (false, false), trivial, Bool.noConfusion⟩,
    ⟨actual, rfl, rfl⟩, fun ⟨_, feasible, success⟩ => success feasible⟩

/-- The same actual exercise of rational giving as in ThroughWill persists
across all represented continuations, even though the decision frame has
multiple available cells. This also preserves the universal scope at w. -/
theorem fixedRational :
    TruthCore.Causality.ThroughWill.Control.rational true false (some true) ∧
    RationallyGivesAt (model true false) (agency (some true)) false false true ∧
    FixedTowardAt (model true false) false false true ∧
    Cstit false actual (Produces (model true false) (fun k => k.val.2) false true) ∧
    ¬ Dstit false actual (Produces (model true false) (fun k => k.val.2) false true) ∧
    ¬ WilledTwoWayAt (model true false) (agency (some true)) false false := by
  have settled : Necessary (F := decision false false) (m := 0)
      (Produces (model true false) (fun k => k.val.2) false true) :=
    fun _ => ⟨(), rfl, rfl, rfl⟩
  refine ⟨?_, ⟨true, rfl, rfl, ⟨(), rfl, rfl, rfl⟩, rfl, rfl, rfl⟩,
    ⟨⟨(), rfl, rfl, rfl⟩, fun _ _ _ => ⟨(), rfl, rfl, rfl⟩⟩,
    necessary_cstit settled, necessary_not_dstit settled, ?_⟩
  · intro g _ hw _ x hx _
    change g = false at hw
    subst g
    cases x
    · exact (hx rfl).elim
    · exact ⟨true, rfl, rfl, ⟨(), rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  · rintro ⟨_, p, x, v, _, _, _, _, _, ⟨⟨t, gives⟩, _⟩, withholds⟩
    exact withholds ⟨t, gives⟩

/-- Treat the two tied outputs from the existing census as outputs constant on the first agent’s cells.
Each optional recipient (indices 1 and 2) is individually omissible, and
every feasible cell still creates a recipient (index 0). -/
def tiedOutput (k : (decision false false).Through 0) : Output :=
  if k.val.1 then 3 else 5

theorem tiedNoEmptyChoice :
    (∀ k, optimal quality (tiedOutput k) = true) ∧
    CanEnsure (historical _ _) false actual (fun k => includes (tiedOutput k) 1 = false) ∧
    CanEnsure (historical _ _) false actual (fun k => includes (tiedOutput k) 2 = false) ∧
    ¬ CanEnsure (historical _ _) false actual
      (fun k => ∀ x, includes (tiedOutput k) x = false) := by
  have includesFirst (k : (decision false false).Through 0) :
      includes (tiedOutput k) 0 = true := by
    rcases k with ⟨⟨a, _⟩, _⟩
    cases a
    · change includes 5 0 = true
      decide +kernel
    · change includes 3 0 = true
      decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have h3 : (3 : Output) ∈ TruthCore.Modal.WillChoiceCensus.outputs.filter (optimal quality) := by
      rw [tiedOptima.1]
      simp
    have h5 : (5 : Output) ∈ TruthCore.Modal.WillChoiceCensus.outputs.filter (optimal quality) := by
      rw [tiedOptima.1]
      simp
    unfold tiedOutput
    split
    · exact (List.mem_filter.mp h3).2
    · exact (List.mem_filter.mp h5).2
  · refine ⟨here false false (false, false), trivial, fun k hk => ?_⟩
    change false = k.val.1 at hk
    simp [tiedOutput, ← hk]
    decide +kernel
  · refine ⟨actual, trivial, fun k hk => ?_⟩
    change true = k.val.1 at hk
    simp [tiedOutput, ← hk]
    decide +kernel
  · intro ensure
    obtain ⟨k, _, absent⟩ := canEnsure_can ensure
    exact Bool.noConfusion ((includesFirst k).symm.trans (absent 0))

/-- Here accessibility can exclude the withholding world without altering
any STIT choice or outcome. This keeps the modal interpretation testable. -/
def variableGiving (blocked : Bool) : TruthCore.Causality.Frame.CausalityFrame Bool Bool Unit Unit :=
  let base := model true false
  { base with
    history := { base.history with
      ontic := { base.history.ontic with
        frame := ⟨fun _ v => blocked = false ∨ v = true⟩
        ExistsAt := fun v b => b = false ∨ v = true }
      IsAt := fun v b _ => b = false ∨ v = true }
    GivesAt := fun v g x _ => v = true ∧ g = false ∧ x = true }

def choiceWorld (k : (decision false false).Through 0) : Bool := k.val.1

/-- The existence and production readings align in both interpretations.
Dstit therefore survives restricting metaphysical access. Only the unrestricted
interpretation can use the withholding cell to defeat modal fixity. -/
theorem worldAlignment :
    (∀ blocked, Dstit false actual (Produces (variableGiving blocked) choiceWorld false true) ∧
      CanEnsure (historical _ _) false actual
        (fun k => ¬ Produces (variableGiving blocked) choiceWorld false true k)) ∧
    Admissible (variableGiving false) choiceWorld true false ∧
    ¬ FixedTowardAt (variableGiving false) true false true ∧
    FixedTowardAt (variableGiving true) true false true ∧
    ¬ Admissible (variableGiving true) choiceWorld true false ∧
    WilledTwoWayAt (variableGiving false) (agency (some true)) true false := by
  have choice (blocked : Bool) :
      Dstit false actual (Produces (variableGiving blocked) choiceWorld false true) ∧
        CanEnsure (historical _ _) false actual
          (fun k => ¬ Produces (variableGiving blocked) choiceWorld false true k) := by
    have track : TracksExistence (variableGiving blocked) choiceWorld false true := by
      intro k
      constructor
      · rintro ⟨_, v, _, _⟩
        exact Or.inr v
      · rintro (impossible | v)
        · cases impossible
        · exact ⟨(), v, rfl, rfl⟩
    exact gives_and_can_refrain_of_existence track
      (fun _ hk => Or.inr hk.symm)
      ⟨here false false (false, false), trivial, fun _ hk yes =>
        yes.elim Bool.noConfusion (fun yes => Bool.noConfusion (hk.trans yes))⟩
  have admit : Admissible (variableGiving false) choiceWorld true false :=
    fun _ => ⟨Or.inl rfl, Or.inl rfl⟩
  refine ⟨choice, admit, dstit_excludes_fixed admit (choice false).1, ?_, ?_, ?_⟩
  · refine ⟨⟨(), rfl, rfl, rfl⟩, ?_⟩
    intro _ accessible _
    rcases accessible with impossible | there
    · cases impossible
    · exact ⟨(), there, rfl, rfl⟩
  · intro admits
    exact (admits (here false false (false, false))).1.elim Bool.noConfusion Bool.noConfusion
  · exact willed_two_way_of_cell (A := agency (some true)) (h := actual) (x := true)
      (Or.inl rfl) admit (fun _ => ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩)
      ⟨true, rfl, rfl, ⟨(), rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ (choice false).2

/-- Two nonempty outputs with no shared recipient. Either recipient can be
omitted individually, but every available cell produces exactly one. -/
theorem pointwiseNotJoint :
    (∀ x : Bool, CanEnsure (historical _ _) false actual (fun k => choiceWorld k ≠ x)) ∧
    ¬ CanEnsure (historical _ _) false actual (fun k => ∀ x, choiceWorld k ≠ x) := by
  constructor
  · intro x
    refine ⟨here false false (!x, false), trivial, fun k hk yes => ?_⟩
    have impossible : (!x) = x := hk.trans yes
    cases x <;> cases impossible
  · intro ensure
    obtain ⟨k, _, absent⟩ := canEnsure_can ensure
    exact absent (choiceWorld k) rfl

/-- A governing plan can require recipient benefit even when giving being
to that recipient remains fixed throughout the modal frame. -/
theorem governingBenefitWithFixedGiving :
    let M := TruthCore.Causality.BenefitPlanWitness.Control.plans true
    TruthCore.Causality.BenefitPlanWitness.SomeGoverningPlanRejectsBenefitOmission
      (model true false) M TruthCore.Causality.ThroughWill.Control.acts
      TruthCore.Causality.ThroughWill.Control.will false ∧
    FixedTowardAt (model true false) false false true ∧
    ¬ WilledTwoWayAt (model true false) (agency (some true)) false false := by
  have benefit := TruthCore.Results.Causality.BenefitPlanWitness.controls.2.2.2.2.2.1
  exact ⟨benefit, fixedRational.2.2.1, fixedRational.2.2.2.2.2⟩

/-- A single actual edge from false to true and both beings concrete. -/
def ground (_ : Bool) (g x : Bool) : Prop := g = false ∧ x = true

/-- The registered premises jointly cover the grounded recipient of a real
root in this assignment. Changing only modal access defeats the first
premise and the conclusion while preserving the withholding cell. -/
theorem rootWithholdingAlignment :
    TruthCore.Causality.NarDerivation.ActualRootsWithholdEachGrounded
      (variableGiving false) (fun _ => True) ground true ∧
    RootsHaveWithholdingCells (variableGiving true) choiceWorld (fun _ => True) ground true ∧
    ¬ RootHistoriesAdmissible (variableGiving true) choiceWorld (fun _ => True) ground true ∧
    ¬ TruthCore.Causality.NarDerivation.ActualRootsWithholdEachGrounded
      (variableGiving true) (fun _ => True) ground true := by
  have cells (blocked : Bool) :
      RootsHaveWithholdingCells (variableGiving blocked) choiceWorld (fun _ => True) ground true := by
    intro g x _ _ edge
    have hg : g = false := edge.2.2.1
    cases hg
    exact ⟨here false false (false, false), fun _ hk ⟨_, gives, _, _⟩ =>
      Bool.noConfusion (hk.trans gives)⟩
  have root (blocked : Bool) : TruthCore.Causality.NecessaryRootFork.ActualRoot
      (TruthCore.Causality.FirstMoverNecessity.groundProfile (variableGiving blocked)
        (fun _ => True) ground) true false :=
    ⟨⟨trivial, Or.inl rfl⟩, fun _ edge => Bool.noConfusion edge.2.2.2⟩
  have admissible :
      RootHistoriesAdmissible (variableGiving false) choiceWorld (fun _ => True) ground true := by
    intro g hg _
    cases g
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact (hg.2 false ⟨trivial, Or.inl rfl, rfl, rfl⟩).elim
  refine ⟨TruthCore.Results.Causality.GivingChoice.root_withholding_of_cells admissible (cells false),
    cells true, ?_, ?_⟩
  · exact fun admits => worldAlignment.2.2.2.2.1 (admits false (root true))
  · intro withholds
    obtain ⟨v, accessible, _, absent⟩ :=
      withholds false true (root true) ⟨trivial, Or.inr rfl⟩
        ⟨trivial, Or.inl rfl, rfl, rfl⟩
    rcases accessible with impossible | there
    · cases impossible
    · exact absent ⟨(), there, rfl, rfl⟩

end TruthCore.Models.STITControls
