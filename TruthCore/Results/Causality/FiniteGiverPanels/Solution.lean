module

public import TruthCore.Causality.FiniteGiverPanels
public import TruthCore.Results.Modal.FiniteHitting.Solution

@[expose] public section
namespace TruthCore.Results.Causality.FiniteGiverPanels

open TruthCore.Causality.FiniteGiverPanels
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (AbsenceAmalgamation)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Modal.FiniteHitting (component)

theorem universalGiver {Being : Type} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (finiteHitting : TruthCore.Modal.FiniteHitting.Package)
    (covered : EveryPanelCovered InAct MoreIn CausesIn esse)
    (pivot : FinitePivot InAct MoreIn CausesIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  classical
  let presence := PanelPresence InAct MoreIn CausesIn esse
  let panelFrame := component (Finset {x // InAct x esse})
  have amalgamation : AbsenceAmalgamation panelFrame presence ∅ := by
    intro left right _ _
    refine ⟨left ∪ right, trivial, ?_⟩
    intro giver passes
    exact ⟨fun x hx => passes x (Finset.mem_union_left right hx),
      fun x hx => passes x (Finset.mem_union_right left hx)⟩
  have laws : TruthCore.Modal.FiniteHitting.Laws := finiteHitting.2.1
  obtain ⟨giver, passesEveryPanel⟩ :=
    laws.2.2.1 _ _ presence ∅ (fun panel _ => covered panel) amalgamation pivot
  refine ⟨giver.val, giver.property, fun recipient distinct actual => ?_⟩
  let x : {x // InAct x esse} := ⟨recipient, actual⟩
  exact (passesEveryPanel {x} trivial x (Finset.mem_singleton_self x)).resolve_left distinct

theorem natPanelBoundary : NatPanelBoundary := by
  dsimp [NatPanelBoundary]
  have covered : EveryPanelCovered (fun _ _ => True) (fun _ _ _ => False)
      (fun (giver recipient : ℕ) _ => recipient < giver) () := by
    intro panel
    refine ⟨⟨panel.sup Subtype.val + 1, trivial, fun _ falseComparison => falseComparison⟩, ?_⟩
    intro recipient member
    exact Or.inr (Nat.lt_succ_of_le (Finset.le_sup (f := Subtype.val) member))
  have noUniversal : ¬ MaximeEnsCausesBeingOfAllReading (fun _ _ => True)
      (fun _ _ _ => False) (fun (giver recipient : ℕ) _ => recipient < giver) () := by
    rintro ⟨giver, _, causes⟩
    exact Nat.not_lt_of_ge (Nat.le_succ giver)
      (causes (giver + 1) (Nat.succ_ne_self giver) trivial)
  exact ⟨covered, fun pivot => noUniversal (universalGiver _ _ _ _
    TruthCore.Results.Modal.FiniteHitting.checks covered pivot), noUniversal⟩

/-- One missed actual recipient per listed candidate defeats them all. The
exhaustiveness hypothesis excludes candidates outside the list at the pivot. -/
theorem boundedRefutation {Being : Type} [DecidableEq Being] {Respect : Sort v}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (pivot : Finset {x // InAct x esse})
    (candidates : Finset {g // IsMaximumIn InAct MoreIn esse g})
    (exhaustive : ∀ giver, PanelPresence InAct MoreIn CausesIn esse giver pivot →
      giver ∈ candidates)
    (noUniversal : ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) :
    ∃ extra : Finset {x // InAct x esse}, extra.card ≤ candidates.card ∧
      ∀ giver, ¬ PanelPresence InAct MoreIn CausesIn esse giver (pivot ∪ extra) := by
  classical
  have misses (giver : {g // IsMaximumIn InAct MoreIn esse g}) :
      ∃ recipient : {x // InAct x esse},
        ¬ (recipient.val = giver.val ∨ CausesIn giver.val recipient.val esse) := by
    by_contra noMiss
    apply noUniversal
    refine ⟨giver.val, giver.property, fun x distinct actual => ?_⟩
    by_contra noGift
    exact noMiss ⟨⟨x, actual⟩, fun covered => covered.elim distinct noGift⟩
  choose missed fails using misses
  refine ⟨candidates.image missed, Finset.card_image_le, fun giver passes => ?_⟩
  have inCandidates := exhaustive giver (fun x hx => passes x (Finset.mem_union_left _ hx))
  exact fails giver (passes _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ inCandidates)))

theorem cyclicSharpness (k : ℕ) : CyclicPivotSharpness k := by
  classical
  let actual : Fin (k + 2) → Unit → Prop := fun _ _ => True
  let more : Unit → Fin (k + 2) → Fin (k + 2) → Prop := fun _ _ _ => False
  let gives : Fin (k + 2) → Fin (k + 2) → Unit → Prop :=
    fun giver recipient _ => recipient ≠ giver ∧ recipient ≠ finRotate (k + 2) giver
  let recipientEquiv : {x // actual x ()} ≃ Fin (k + 2) :=
    Equiv.subtypeUnivEquiv (fun _ => trivial)
  let giverEquiv : {g // IsMaximumIn actual more () g} ≃ Fin (k + 2) :=
    Equiv.subtypeUnivEquiv (fun _ => ⟨trivial, fun _ impossible => impossible⟩)
  let := Fintype.ofEquiv _ recipientEquiv.symm
  let := Fintype.ofEquiv _ giverEquiv.symm
  let missed := (giverEquiv.trans (finRotate (k + 2))).trans recipientEquiv.symm
  have rotationMoves (i : Fin (k + 2)) : finRotate (k + 2) i ≠ i := by
    intro fixedPoint
    rw [finRotate_apply] at fixedPoint
    have oneZero : (1 : Fin (k + 2)) = 0 := by
      exact add_left_cancel (fixedPoint.trans (add_zero i).symm)
    have values := congrArg Fin.val oneZero
    simp at values
  have passes (giver : {g // IsMaximumIn actual more () g})
      (panel : Finset {x // actual x ()}) :
      PanelPresence actual more gives () giver panel ↔ missed giver ∉ panel := by
    constructor
    · intro covers member
      rcases covers (missed giver) member with same | ⟨_, edge⟩
      · exact rotationMoves giver.val same
      · exact edge rfl
    · intro absent recipient member
      by_cases same : recipient.val = giver.val
      · exact Or.inl same
      · refine Or.inr ⟨same, fun next => absent ?_⟩
        have eqRecipient : recipient = missed giver := Subtype.ext next
        exact eqRecipient ▸ member
  let chosen := recipientEquiv.symm 0
  let pivot : Finset {x // actual x ()} := {chosen}
  let extra : Finset {x // actual x ()} := Finset.univ.erase chosen
  have recipientCard : Fintype.card {x // actual x ()} = k + 2 := by
    rw [Fintype.card_congr recipientEquiv, Fintype.card_fin]
  have giverCard : Fintype.card {g // IsMaximumIn actual more () g} = k + 2 := by
    rw [Fintype.card_congr giverEquiv, Fintype.card_fin]
  refine ⟨pivot, Finset.card_singleton _, ?_, ?_, ?_⟩
  · refine ⟨Finset.univ.erase (missed.symm chosen), ?_, fun giver => ?_⟩
    · have count := Finset.card_erase_add_one (Finset.mem_univ (missed.symm chosen))
      rw [Finset.card_univ, giverCard] at count
      omega
    · rw [passes]
      simp only [pivot, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ, and_true]
      exact not_congr (missed.eq_symm_apply).symm
  · intro additional fewer
    have smaller : (pivot ∪ additional).card < Fintype.card {x // actual x ()} := by
      have bound := Finset.card_union_le pivot additional
      rw [Finset.card_singleton] at bound
      omega
    have proper : pivot ∪ additional ≠ Finset.univ :=
      (Finset.card_lt_iff_ne_univ _).mp smaller
    have missing : ∃ x, x ∉ pivot ∪ additional := by
      by_contra noMissing
      apply proper (Finset.eq_univ_of_forall fun x => ?_)
      by_contra absent
      exact noMissing ⟨x, absent⟩
    obtain ⟨x, hx⟩ := missing
    exact ⟨missed.symm x, (passes _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hx)⟩
  · refine ⟨extra, ?_, fun giver covers => ?_⟩
    · change (Finset.univ.erase chosen).card = k + 1
      have count := Finset.card_erase_add_one (Finset.mem_univ chosen)
      rw [Finset.card_univ, recipientCard] at count
      omega
    · apply (passes _ _).mp covers
      by_cases same : missed giver = chosen
      · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr same)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨same, Finset.mem_univ _⟩)

open Classical in
/-- Pairing an independently underived maximal bearer with each actual
recipient tests direct causal coverage by that very bearer. -/
theorem underivedPivotPairs {Being : Type} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (m : Being) (maximum : IsMaximumIn InAct MoreIn esse m)
    (underived : ∀ g, g ≠ m → ¬ CausesIn g m esse) :
    (∀ x : {b // InAct b esse}, ∃ g,
      PanelPresence InAct MoreIn CausesIn esse g {⟨m, maximum.1⟩, x}) ↔
    CausesAllInGenus InAct CausesIn esse m := by
  classical
  let pivot : {b // InAct b esse} := ⟨m, maximum.1⟩
  constructor
  · intro covered x distinct actual
    let recipient : {b // InAct b esse} := ⟨x, actual⟩
    obtain ⟨g, passes⟩ := covered recipient
    have pin : m = g.val := by
      rcases passes pivot (Finset.mem_insert_self _ _) with same | gives
      · exact same
      · exact Classical.byContradiction fun different => underived g.val (Ne.symm different) gives
    exact pin.symm ▸ ((passes recipient (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).resolve_left
      (fun same => distinct (same.trans pin.symm)))
  · intro gives x
    refine ⟨⟨m, maximum⟩, ?_⟩
    intro y _
    by_cases same : y.val = m
    · exact Or.inl same
    · exact Or.inr (gives y.val same y.property)

end TruthCore.Results.Causality.FiniteGiverPanels
