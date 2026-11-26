module

public import TruthCore.Causality.SelectedConeSupply
public import TruthCore.Results.Causality.SelectedConeSupply.Solution
public import TruthCore.Causality.MathlibBridges
public import TruthCore.Results.Causality.SelectedConeRegress.Solution
public import TruthCore.Results.Causality.SelectedSourcePath.Solution
public import TruthCore.Results.Causality.FiniteThroughput.Solution
public import TruthCore.Results.Causality.ReceiptMatching.Solution
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Nat.Cast.WithTop

@[expose] public section

open scoped ENNReal

namespace TruthCore.Results.Causality.SelectedConeSupplyControls
open TruthCore.Causality (FiniteCausalPath finiteCausalPath_iff_reflTransGen)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.FiniteThroughput
open TruthCore.Causality.GroundedOccupantRegress
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.ReceiptMatching
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.SelectedConeSupply
open TruthCore.Results.Causality.SelectedConeSupply (sourcePath_of_receiptExit)
open TruthCore.Causality.SelectedSourcePath
open TruthCore.Causality.WorldSourceRegress (SourcePath overlap)
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic.RootDescent (acc_of_map acc_of_subtype)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

variable {W B E N : Type}

theorem coneWellFounded_iff_noInfiniteWalk (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) :
    ConeWellFounded m w x.val ↔ NoInfiniteWalkFrom (graph m w) x := by
  classical
  have equiv : Acc (graph m w).edge x ↔ Acc (ActualConcreteGround m w) x.val :=
    ⟨acc_of_subtype (fun _ _ _ edge => ⟨⟨edge.1, edge.2.1⟩, edge.2.2⟩) x,
      acc_of_map Subtype.val (fun y _ edge => ⟨y.property.1, y.property.2, edge⟩)⟩
  constructor
  · intro wf chain
    exact not_acc_iff_exists_descending_chain.mpr chain
      (equiv.mpr (accessibleOfConeWellFounded m w x.val x.property wf))
  · intro noChain
    have start := equiv.mp (not_not.mp (fun bad => noChain (not_acc_iff_exists_descending_chain.mp bad)))
    have inheritAcc (y : B) (path : GroundAncestor m w y x.val) :
        Acc (ActualConcreteGround m w) y := by
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl => exact start
      | head edge _ ih => exact ih.inv edge
    exact (coneWellFounded_iff_acc m w x.val).mpr fun y h => inheritAcc y h.2

theorem coneWalkCriterion : ConeWalkCriterion :=
  coneWellFounded_iff_noInfiniteWalk

theorem coneWellFounded_iff_localAcyclic_and_noInjectiveRegress (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b}) :
    ConeWellFounded m w x.val ↔
      (coneGraph m w x.val).NoCycles ∧ NoAnchoredConcreteGroundingRegress m w x := by
  constructor
  · intro wf
    exact ⟨wf.transGen.irrefl.irrefl,
      SelectedConeRegress.noAnchoredRegress_of_coneWellFounded m w x wf⟩
  · rintro ⟨acyclic, noRegress⟩
    apply (coneWellFounded_iff_noInfiniteWalk m w x).mpr
    rintro ⟨f, hStart, step⟩
    have ancestor (n : Nat) : Cone m w x.val (f n).val := by
      refine ⟨(f n).property, ?_⟩
      induction n with
      | zero => rw [hStart]; exact .refl
      | succ n ih =>
        exact .head ⟨(f (n + 1)).property.1, (f (n + 1)).property.2, step n⟩ ih
    let lift (n : Nat) : {b // Cone m w x.val b} := ⟨(f n).val, ancestor n⟩
    have injective := WorldSourceRegress.chain_injective (coneGraph m w x.val) acyclic lift step
    exact noRegress ⟨f, hStart, fun _ _ equal =>
      injective (Subtype.ext (congrArg (fun b => b.val) equal)), step⟩

theorem natRank_of_sourcePath_and_oneStep (m : Profile W B) (w : W)
    (x : {b // ActualConcrete m w b})
    (path : HasSelectedSourcePath m w x) (forks : SelectedForksJoinInOneStep m w x) :
    HasNatRank (coneGraph m w x.val) := by
  classical
  let G := coneGraph m w x.val
  let : Quiver _ := supplierQuiver G
  have wf : WellFounded G.edge := SelectedSourcePath.coneWellFounded_of_sourcePath m w x path forks
  have quiverPath {s y} (h : FiniteCausalPath G.edge y s) : Nonempty (SupplierPath G s y) := by
    induction h with
    | same => exact ⟨.nil⟩
    | link edge _ ih =>
      obtain ⟨p⟩ := ih
      exact ⟨.cons p ⟨edge⟩⟩
  have witness (y) : ∃ s, G.Source s ∧ Nonempty (SupplierPath G s y) := by
    obtain ⟨s, hp, hs⟩ := WorldSourceRegress.sourcePath_of_acc G y (wf.apply y)
    exact ⟨s, hs, quiverPath hp⟩
  choose source hs paths using witness
  let route (y) := (paths y).some
  refine ⟨fun y => (route y).length, ?_⟩
  intro y z edge
  have pq := (SelectedSourcePath.maximalPathsAgree G forks (hs y) (hs z)
    (.cons (route y) ⟨edge⟩) (route z)).2
  change (route y).length + 1 = (route z).length at pq
  change (route y).length < (route z).length
  rw [← pq]
  exact Nat.lt_succ_self _

theorem sourcePath_and_oneStep_fail_on_rankedFork :
    HasNatRank splitFork ∧ SourcePath splitFork 2 ∧ ¬ ForksJoinInOneStep splitFork := by
  have e0 : splitFork.edge 0 2 := ⟨by decide, rfl⟩
  have e1 : splitFork.edge 1 2 := ⟨by decide, rfl⟩
  refine ⟨⟨Fin.val, ?_⟩, ⟨0, .link e0 (.same 0), ?_⟩, ?_⟩
  · rintro y x ⟨hy, rfl⟩
    exact hy
  · rintro ⟨y, _, h⟩
    exact (by decide : (0 : Fin 3) ≠ 2) h
  · intro forks
    obtain ⟨k, _, h⟩ := forks 2 0 1 e0 e1 (by decide)
    exact (by decide : (1 : Fin 3) ≠ 2) h.2

theorem wellFoundedCone_withoutNatRank :
    ConeWellFounded topProfile () ⊤ ∧ ¬ HasNatRank (coneGraph topProfile () ⊤) := by
  have included (n : Nat) : Cone topProfile () ⊤ (n : WithTop Nat) :=
    ⟨⟨trivial, trivial⟩, .single ⟨trivial, trivial, WithTop.coe_lt_top n⟩⟩
  let nod (n : Nat) : {b // Cone topProfile () ⊤ b} := ⟨n, included n⟩
  let top : {b // Cone topProfile () ⊤ b} := ⟨⊤, ⟨trivial, trivial⟩, .refl⟩
  constructor
  · exact InvImage.wf Subtype.val wellFounded_lt
  · rintro ⟨rank, decreases⟩
    have lower (n : Nat) : n ≤ rank (nod n) := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        have edge : (nod n).val < (nod (n + 1)).val := by
          change (n : WithTop Nat) < ((n + 1 : Nat) : WithTop Nat)
          exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)
        have inc := decreases (y := nod n) (x := nod (n + 1)) edge
        exact Nat.le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt inc)
    have above := decreases (y := nod (rank top)) (x := top) (WithTop.coe_lt_top _)
    exact (not_lt_of_ge (lower (rank top))) above


private theorem raySourceHasNoGround (y : Option Nat) :
    ¬ ActualConcreteGround rayProfile true y raySource.val := by
  intro h
  cases y <;> exact h.2.2

/-- Both aligned ledgers book the same one real ground edge of the model
while omitting the ray edges. They yield a source path and leave a regress
in the very same cone at the very same recipient. -/
theorem alignedLedgers_allowAnchoredRegress :
    ContingentAt rayProfile.ontic true rayTip.val ∧
    SelectedReceiptExit rayProfile true rayTip raySender rayReceiver ∧
    GroundedCanMatch rayProfile true raySender rayReceiver ∧
    SelectedThroughputExit rayProfile true rayTip rayFlow ∧
    GroundedExportCovered rayProfile true rayFlow ∧
    HasSelectedSourcePath rayProfile true rayTip ∧
    AnchoredConcreteGroundingRegress rayProfile true rayTip := by
  classical
  have ne : rayTip ≠ raySource := by
    intro equal
    have h := congrArg Subtype.val equal
    cases h
  have receiptExit : SelectedReceiptExit rayProfile true rayTip raySender rayReceiver := by
    refine ⟨fun _ => trivial, (), rfl, ?_, inferInstance⟩
    intro path
    have stays {b} (p : Reaches raySender rayReceiver rayTip b) : b = rayTip := by
      induction p with
      | refl => rfl
      | tail _ step _ =>
        obtain ⟨_, _, e⟩ := step
        exact e.symm
    exact ne (stays path).symm
  have groundedAway (u : RayBearer) (grounded : ∃ y, ActualConcreteGround rayProfile true y u.val) :
      u ≠ raySource := by
    rintro rfl
    exact grounded.elim fun y hy => raySourceHasNoGround y hy
  have matchCovered : GroundedCanMatch rayProfile true raySender rayReceiver := by
    intro u ground
    have empty (e : {e // raySender e = u}) : False := groundedAway u ground e.property.symm
    exact ⟨⟨fun e => (empty e).elim, fun e _ _ => (empty e).elim⟩⟩
  have support {a b : RayBearer} (positive : 0 < rayFlow a b) :
      a = raySource ∧ b = rayTip := by
    by_contra h
    simp [rayFlow, h] at positive
  have ledgerExit : SelectedThroughputExit rayProfile true rayTip rayFlow := by
    refine ⟨?_, ?_, raySource, by simp [rayFlow], ?_⟩
    · intro a b positive
      obtain ⟨rfl, rfl⟩ := support positive
      trivial
    · change (∑' p : RayBearer × RayBearer, rayFlow p.1 p.2) ≠ ⊤
      have entry (p : RayBearer × RayBearer) :
          rayFlow p.1 p.2 = if p = (raySource, rayTip) then 1 else 0 := by
        simp [rayFlow, Prod.ext_iff]
      simp_rw [entry]
      rw [tsum_ite_eq (raySource, rayTip) (fun _ => (1 : ℝ≥0∞))]
      exact ENNReal.one_ne_top
    · intro path
      have stays {b} (p : Relation.ReflTransGen (fun a b => 0 < rayFlow a b) rayTip b) :
          b = rayTip := by
        induction p with
        | refl => rfl
        | tail _ edge _ => exact (support edge).2
      exact ne (stays path).symm
  have ledgerCovered : GroundedExportCovered rayProfile true rayFlow := by
    intro u ground
    simp [rayFlow, groundedAway u ground]
  refine ⟨⟨Or.inl rfl, false, trivial, by simp [rayProfile, rayTip]⟩, receiptExit, matchCovered, ledgerExit, ledgerCovered,
    sourcePath_of_receiptExit rayProfile true rayTip raySender rayReceiver ReceiptMatching.unmatchedUpstream
      matchCovered receiptExit, ?_⟩
  let f (n : Nat) : RayBearer := ⟨some n, trivial, Or.inl rfl⟩
  exact ⟨f, rfl, fun _ _ equal => Option.some.inj (congrArg Subtype.val equal), fun _ => rfl⟩

theorem wellFounded_of_natRank (G : Graph N) (ranked : HasNatRank G) : WellFounded G.edge := by
  obtain ⟨rank, decreases⟩ := ranked
  exact Subrelation.wf (fun edge => decreases edge) (measure rank).wf

open TruthCore.Latin.Aquinas.SummaTheologiae
  (NoInfinitePerSeEfficientCauseSeriesReading)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (NecessityCausedAmongNecessaries NoInfiniteRegressInCausedNecessariesReading)

/-- Both applications are on the represented cone carrier. Each relation
needs its own edge-inclusion proof. -/
theorem perSeRegressExcluded_on_cone {W B T : Type} {m : Profile W B} {w : W}
    {recipient : B} (wf : ConeWellFounded m w recipient)
    (causesAsCaused causesNecessity : {b // Cone m w recipient b} → {b // Cone m w recipient b} → Prop)
    (possible : (T → Prop) → Prop) (isAt : {b // Cone m w recipient b} → T → Prop)
    (perSeEdge : ∀ ⦃y x⦄, causesAsCaused y x → m.grounds w y.val x.val)
    (necessityEdge : ∀ ⦃y x⦄, NecessityCausedAmongNecessaries possible isAt causesNecessity y x →
      m.grounds w y.val x.val) :
    NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused ∧
      NoInfiniteRegressInCausedNecessariesReading possible isAt causesNecessity :=
  ⟨(Subrelation.wf (fun h => perSeEdge h) wf).apply, (Subrelation.wf (fun h => necessityEdge h) wf).apply⟩

end TruthCore.Results.Causality.SelectedConeSupplyControls
