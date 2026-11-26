module

public import TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.UniversalGiverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open PrimaPars.Question3.Article4 (Profile)
open TruthCore.Causality.GroundingEdgeScope (localForks_iff_only_source_parent)
open TruthCore.Causality.SelectedAncestry (Cone)
open TruthCore.Causality.SelectedSourcePath (coneGraph selectedNode)
open ClosedEsseSource (esseCauseGraph)

theorem sameGiverCriterionAtEsse {B P R : Type} (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hGiver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (hAscent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse) :
    SameGiverForkCriterion p MoreIn := by
  obtain ⟨s, hMax, hGives⟩ := hGiver
  have noIncoming (y : B) (hy : ActualEsseCause p y s) : False :=
    hMax.2 y (hAscent y s hy.1 hy.2.2.2)
  refine ⟨s, hMax, hGives, ?_⟩
  intro x
  let m := esseCauseGraph p
  let G := coneGraph m () x.val
  have parent {y : B} (hy : ActualEsseCause p y x.val) : Cone m () x.val y :=
    ⟨⟨hy.2.1, hy.2.1⟩, .single ⟨hy.2.1, hy.2.1, hy⟩⟩
  constructor
  · intro hFork y hy
    have hxs : x.val ≠ s := fun heq => noIncoming y (heq ▸ hy)
    have hsx : ActualEsseCause p s x.val :=
      ⟨Ne.symm hxs, hMax.1, x.property.1, hGives x.val hxs x.property.1⟩
    let root : {b // Cone m () x.val b} := ⟨s, parent hsx⟩
    have hSource : G.Source root := by
      rintro ⟨k, hk⟩
      exact noIncoming k.val hk
    have hOnly := (localForks_iff_only_source_parent G (s := root) (x := selectedNode m () x)
      hSource hsx).mp (hFork _)
    exact congrArg Subtype.val (hOnly ⟨y, parent hy⟩ hy)
  · intro hOnly
    have member {b : B} (hb : Cone m () x.val b) : b = x.val ∨ b = s := by
      have path := hb.2
      clear hb
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl => exact Or.inl rfl
      | head hEdge _ ih =>
        rcases ih with atRecipient | atSource
        · exact Or.inr (hOnly _ (atRecipient ▸ hEdge.2.2))
        · exact (noIncoming _ (atSource ▸ hEdge.2.2)).elim
    intro b y z hy hz hne
    change ActualEsseCause p y.val b.val at hy
    change ActualEsseCause p z.val b.val at hz
    rcases member b.property with atRecipient | atSource
    · rw [atRecipient] at hy hz
      exact (hne (Subtype.ext ((hOnly _ hy).trans (hOnly _ hz).symm))).elim
    · rw [atSource] at hy
      exact (noIncoming _ hy).elim

theorem sameGiverCriterion {B P R : Type} (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hGiver : MaximeEnsCausesBeingOfAllReading p.InAct MoreIn p.CausesIn p.esse)
    (hAscent : CauseOfQualityInAnotherIsMoreSuchReading p.CausesIn MoreIn) :
    SameGiverForkCriterion p MoreIn := by
  exact sameGiverCriterionAtEsse p MoreIn hGiver (fun y x => hAscent y x p.esse)

theorem secondaryGiverControl : SecondaryGiverControl := by
  have hGiver : MaximeEnsCausesBeingOfAllReading
      levelProfile.InAct levelMore levelProfile.CausesIn () := by
    refine ⟨none, ⟨trivial, ?_⟩, ?_⟩
    · intro y
      exact Nat.not_lt_zero _
    · rintro (_ | b) hne _
      · exact (hne rfl).elim
      · cases b with
        | false => exact Nat.zero_lt_succ 0
        | true => exact Nat.zero_lt_succ 1
  have hAscent : CauseOfQualityInAnotherIsMoreSuchReading levelProfile.CausesIn levelMore :=
    fun _ _ _ _ h => h
  have hm : ActualEsseCause levelProfile none (some false) :=
    ⟨by decide, trivial, trivial, Nat.zero_lt_succ 0⟩
  have hf : ActualEsseCause levelProfile none (some true) :=
    ⟨by decide, trivial, trivial, Nat.zero_lt_succ 1⟩
  have hs : ActualEsseCause levelProfile (some false) (some true) :=
    ⟨by decide, trivial, trivial, Nat.lt_succ_self 1⟩
  refine ⟨hGiver, hAscent, hm, hf, hs, ?_⟩
  intro hJoin
  obtain ⟨_, _, _, criterion⟩ := sameGiverCriterion levelProfile levelMore hGiver hAscent
  have only := (criterion ⟨some true, trivial, trivial⟩).mp hJoin
  cases (only _ hf).trans (only _ hs).symm

end TruthCore.Results.Aquinas.DeEnte.UniversalGiverFork
