module

public import TruthCore.Causality.SubtractionArgument

/-! The subtraction argument for metaphysical nihilism, free recombination and
the necessary-being nodes: the argument, the stage-one node against its
contingency premise, recombination as that premise's support, the strength
order of recombination, and laws and models. Analyst formulations; attribution
deferred. Zero-axiom: excluded middle enters only as the explicit premise
`TruthCore.Logic.ExcludedMiddle`. -/

@[expose] public section

namespace TruthCore.Results.Causality.SubtractionArgument
open TruthCore.Modal
open TruthCore.Causality.SubtractionArgument
open TruthCore.Causality.SubtractionArgument.Model
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.ModalSenseSupport (OnticFrameTransitive)
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Case.Catholicism (Signature)

/-- The subtraction argument: from a possible world with finitely many
concrete objects, subtract them one at a time. Each step needs S2 (the object
could fail to exist) and S3 (it could fail with no newcomer) at the current
world, and transitivity keeps every step accessible from `w`. Excluded middle
decides at each step whether the next listed object is present. -/
theorem subtraction {W B : Type} (m : Profile W B) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle) (hTrans : OnticFrameTransitive m)
    (h1 : PossiblyFinitelyManyConcrete m w) (h2 : EachConcreteCouldFailThroughout m w)
    (h3 : SubtractableThroughout m w) : PossiblyNoConcrete m w := by
  obtain ⟨v, hv, xs, hxs⟩ := h1
  induction xs generalizing v with
  | nil => exact ⟨v, hv, fun ⟨x, hx⟩ => nomatch hxs x hx⟩
  | cons a t ih =>
    rcases hEM (ConcretePresence m a v) with ha | ha
    · obtain ⟨u, hvu, hua, hnew⟩ := h3 v hv a ha (h2 v hv a ha)
      refine ih u (hTrans w v u hv hvu) ?_
      intro y hy
      cases hxs y (hnew y hy) with
      | head => exact absurd hy.2 hua
      | tail _ h => exact h
    · refine ih v hv ?_
      intro y hy
      cases hxs y hy with
      | head => exact absurd hy ha
      | tail _ h => exact h

/-- The stage-one node excludes S2 at its world: the necessary concrete
object present at `w` exists at every accessible world, so not every concrete
object present at `w` could fail to exist. The converse, with excluded middle,
is in the controls (`Laws`, 8): S2 at `w` is exactly the node's denial. -/
theorem necessaryConcreteExcludesContingencyPremise {W B : Type} (m : Profile W B) (w : W)
    (hnc : NecessaryConcreteAt m w) : NotEachConcreteCouldFailAt m w := by
  intro h
  obtain ⟨x, hc, he, hnec⟩ := hnc
  obtain ⟨u, hu, hnu⟩ := h x ⟨hc, he⟩
  exact hnu (hnec u hu)

/-- S2 at `w` is exactly the denial of the stage-one node (excluded middle for
the backward direction). -/
theorem contingencyPremiseExact {W B : Type} (m : Profile W B) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle) : ContingencyPremiseIsNoNecessaryConcretum m w := by
  constructor
  · intro h hnc
    exact necessaryConcreteExcludesContingencyPremise m w hnc h
  · intro hn x hx
    rcases hEM (TruthCore.Isabelle.AFP.GoedelGod.Dia m.ontic.frame
        (fun u => ¬ m.ontic.ExistsAt u x) w) with hd | hd
    · exact hd
    · exfalso
      apply hn
      refine ⟨x, hx.1, hx.2, fun v hv => ?_⟩
      rcases hEM (m.ontic.ExistsAt v x) with h | h
      · exact h
      · exact absurd ⟨v, hv, h⟩ hd

/-- Unrestricted recombination gives S2 at `w` when every concrete candidate
has a distinct possible concrete companion: `x` without `y` is possible, so
`y`'s absence is. -/
theorem recombinationGivesContingency {W B : Type} (m : Profile W B) (w : W)
    (hR : UnrestrictedRecombinationAt m w) (hC : ConcreteCompanionsAt m w) :
    EachConcreteCouldFailAt m w := by
  intro y hy
  obtain ⟨x, hne, hcx, hdx⟩ := hC y hy.1
  obtain ⟨v, hv, _, hnv⟩ := hR x y hcx hy.1 hne hdx
  exact ⟨v, hv, hnv⟩

/-- Unrestricted recombination strengthens contingent recombination. -/
theorem unrestrictedToContingentRecombination {W B : Type} (m : Profile W B) (w : W)
    (h : UnrestrictedRecombinationAt m w) : ContingentRecombinationAt m w := by
  intro x y hx hy hne hdx _
  exact h x y hx hy hne hdx

/-- Certified difference (#1598): unrestricted recombination is exactly
contingent recombination together with the possible absence of every
companioned concrete candidate. Premise-free, constructive. -/
theorem recombinationFactorsExact : RecombinationFactorsExact := by
  intro W B m w
  constructor
  · intro h
    refine ⟨unrestrictedToContingentRecombination m w h, ?_⟩
    intro y hy hcomp
    obtain ⟨x, hne, hcx, hdx⟩ := hcomp
    obtain ⟨v, hv, _, hn⟩ := h x y hcx hy hne hdx
    exact ⟨v, hv, hn⟩
  · intro hcd x y hx hy hne hdx
    exact hcd.1 x y hx hy hne hdx (hcd.2 y hy ⟨x, hne, hx, hdx⟩)

/-- Every member of a list of naturals is at most its sum. -/
theorem le_sum_of_mem : ∀ {k : Nat} {xs : List Nat}, k ∈ xs → k ≤ xs.foldr (· + ·) 0
  | _, _ :: _, .head _ => Nat.le_add_right _ _
  | _, x :: _, .tail _ h => Nat.le_trans (le_sum_of_mem h) (Nat.le_add_left _ x)

/-- The analyst formulation of Lowe's reply: a non-concrete candidate existing
at every accessible world, co-existing there with some concretum, excludes
"possibly no concrete object". -/
theorem lowe {W B : Type} (m : Profile W B) (w : W)
    (hA : NecessaryAbstractumAt m w) (hD : AbstractaNeedConcretaThroughout m w) :
    NotPossiblyNoConcrete m w := by
  intro hP
  obtain ⟨a, hna, hbox⟩ := hA
  obtain ⟨v, hv, hn⟩ := hP
  exact hn (hD v hv a hna (hbox v hv))

theorem laws : Model.Laws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun W B m w hEM => contingencyPremiseExact m w hEM, ?_⟩
  · intro W B m w hnc hP
    obtain ⟨x, hc, _, hnec⟩ := hnc
    obtain ⟨v, hv, hn⟩ := hP
    exact hn ⟨x, hc, hnec v hv⟩
  · intro W σ m w CN hK hP
    obtain ⟨n, hbox, hroot⟩ := hK
    obtain ⟨⟨⟨hc, _⟩, _⟩, _⟩ := hroot
    obtain ⟨v, hv, hn⟩ := hP
    exact hn ⟨n, hc, hbox v hv⟩
  · intro W B m v
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx _ => h x hx⟩
      obtain ⟨u, hu, hnu, _⟩ := h x hx
      exact ⟨u, hu, hnu⟩
    · intro h x hx
      exact h.2 x hx (h.1 x hx)
  · intro W B m w hE
    obtain ⟨v, hv, hval⟩ := hE (fun _ => False)
    refine ⟨v, hv, fun hx => ?_⟩
    obtain ⟨x, _, hex⟩ := hx
    exact Eq.mp (congrFun hval x) hex
  · intro W B m w h v hv
    exact recombinationGivesContingency m v (h v hv).1 (h v hv).2
  · intro W B m w hA hD
    exact lowe m w hA hD
  · intro W B m w hEM hTrans h1 hA hD h23
    exact lowe m w hA hD (subtraction m w hEM hTrans h1 h23.1 h23.2)
  · intro W B m w hC hD hx
    obtain ⟨x, hc, hbox⟩ := hx
    obtain ⟨y, hne, hcy, hdy⟩ := hC x hc
    obtain ⟨u, hu, hn⟩ := hD x hc ⟨y, hne, hcy, hdy⟩
    exact hn (hbox u hu)

theorem models : Model.Models := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- nonvacuity
    refine ⟨⟨true, trivial, [()], fun x _ => ?_⟩, ?_, ?_, ?_, ?_⟩
    · cases x; exact List.Mem.head _
    · intro v _ x _
      exact ⟨false, trivial, fun h => nomatch h⟩
    · intro v _ x _ _
      exact ⟨false, trivial, (fun h => nomatch h), (fun _ hy => nomatch hy.2)⟩
    · intro _ _ _ _ _
      trivial
    · exact ⟨false, trivial, fun ⟨_, _, h⟩ => nomatch h⟩
  · -- S1 omitted
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨v, _, xs, hxs⟩ := h
      have hle := le_sum_of_mem (hxs (v + xs.foldr (· + ·) 0 + 1) ⟨trivial, ?_⟩)
      · exact Nat.not_succ_le_self _
          (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left _ v)) hle)
      · exact Nat.le_trans (Nat.le_add_right v _) (Nat.le_succ _)
    · intro v _ x _
      exact ⟨x + 1, trivial, Nat.not_succ_le_self x⟩
    · intro v _ x hx _
      exact ⟨x + 1, trivial, Nat.not_succ_le_self x,
        fun y hy => ⟨trivial, Nat.le_trans (Nat.le_trans hx.2 (Nat.le_succ x)) hy.2⟩⟩
    · intro _ _ _ _ _
      trivial
    · intro h
      obtain ⟨v, _, hn⟩ := h
      exact hn ⟨v, trivial, Nat.le_refl v⟩
  · -- S3 omitted: pairwise recombination; Lowe's reply
    have aT : pairProfile.ontic.ExistsAt true .a := Or.inr (Or.inl ⟨rfl, rfl⟩)
    have bF : pairProfile.ontic.ExistsAt false .b := Or.inr (Or.inr ⟨rfl, rfl⟩)
    have aF : ¬ pairProfile.ontic.ExistsAt false .a := by
      intro h
      rcases h with h | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h
    have bT : ¬ pairProfile.ontic.ExistsAt true .b := by
      intro h
      rcases h with h | ⟨h, _⟩ | ⟨_, h⟩ <;> cases h
    have ca : pairProfile.concrete .a := fun h => nomatch h
    have cb : pairProfile.concrete .b := fun h => nomatch h
    refine ⟨⟨true, trivial, [.a, .b], fun x hx => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases x
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact absurd rfl hx.1
    · intro v _ x hx
      cases x
      · exact ⟨false, trivial, aF⟩
      · exact ⟨true, trivial, bT⟩
      · exact absurd rfl hx.1
    · intro _ _ _ _ _
      trivial
    · intro x y hx hy hne _
      cases x <;> cases y
      · exact absurd rfl hne
      · exact ⟨true, trivial, aT, bT⟩
      · exact absurd rfl hy
      · exact ⟨false, trivial, bF, aF⟩
      · exact absurd rfl hne
      · exact absurd rfl hy
      · exact absurd rfl hx
      · exact absurd rfl hx
      · exact absurd rfl hx
    · intro y hy
      cases y
      · exact ⟨.b, (fun h => nomatch h), cb, false, trivial, bF⟩
      · exact ⟨.a, (fun h => nomatch h), ca, true, trivial, aT⟩
      · exact absurd rfl hy
    · intro h3
      obtain ⟨u, _, hua, hnew⟩ := h3 true trivial .a ⟨ca, aT⟩ ⟨false, trivial, aF⟩
      cases u
      · exact bT (hnew .b ⟨cb, bF⟩).2
      · exact hua aT
    · intro h
      obtain ⟨v, _, hn⟩ := h
      cases v
      · exact hn ⟨.b, cb, bF⟩
      · exact hn ⟨.a, ca, aT⟩
    · exact ⟨.s, (fun h => h rfl), (fun _ _ => Or.inl rfl)⟩
    · intro v _ _ _ _
      cases v
      · exact ⟨.b, cb, bF⟩
      · exact ⟨.a, ca, aT⟩
    · intro h
      obtain ⟨x, hc, _, hnec⟩ := h
      cases x
      · exact aF (hnec false trivial)
      · exact bT (hnec true trivial)
      · exact hc rfl
  · -- transitivity omitted
    refine ⟨⟨.one, Or.inl ⟨rfl, rfl⟩, [()], fun x _ => ?_⟩, ?_, ?_, ?_, ?_⟩
    · cases x; exact List.Mem.head _
    · intro v hv x _
      rcases hv with ⟨_, rfl⟩ | ⟨h, _⟩
      · exact ⟨.two, Or.inr ⟨rfl, rfl⟩, fun h => h rfl⟩
      · cases h
    · intro v hv x _ _
      rcases hv with ⟨_, rfl⟩ | ⟨h, _⟩
      · exact ⟨.two, Or.inr ⟨rfl, rfl⟩, (fun h => h rfl), (fun _ hy => absurd rfl hy.2)⟩
      · cases h
    · intro h
      rcases h .zero .one .two (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) with ⟨_, h⟩ | ⟨h, _⟩
        <;> cases h
    · intro h
      obtain ⟨v, hv, hn⟩ := h
      rcases hv with ⟨_, rfl⟩ | ⟨h, _⟩
      · exact hn ⟨(), trivial, fun h => nomatch h⟩
      · cases h
  · -- the theist model
    have gAll : ∀ v, theistProfile.ontic.ExistsAt v true := fun _ => Or.inl rfl
    have cF : ¬ theistProfile.ontic.ExistsAt false false := by
      intro h
      rcases h with h | h <;> cases h
    have cT : theistProfile.ontic.ExistsAt true false := Or.inr rfl
    have hS5 : OnticFrameS5 theistProfile := ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩
    have hRoot : RootFacts pairSignature theistProfile true true :=
      ⟨⟨⟨trivial, gAll true⟩, fun _ hy => hy.2.2⟩, rfl, fun _ h => h, rfl⟩
    have hA2 : ¬ EachConcreteCouldFailAt theistProfile true := by
      intro h
      obtain ⟨_, _, hn⟩ := h true ⟨trivial, gAll true⟩
      exact hn (gAll _)
    refine ⟨hS5, fun _ _ _ _ _ => trivial, ⟨true, fun v _ => gAll v, hRoot⟩, ⟨true, ⟨hS5, fun v _ => gAll v⟩, hRoot⟩,
      ⟨true, trivial, gAll true, fun v _ => gAll v⟩,
      ⟨true, trivial, [true, false], fun x _ => ?_⟩, ?_, ?_, ?_, hA2,
      fun h => hA2 (h true trivial), ?_, ?_⟩
    · cases x
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact List.Mem.head _
    · intro v _ x _ hd
      cases x
      · refine ⟨false, trivial, cF, fun y hy => ⟨trivial, ?_⟩⟩
        rcases hy.2 with h | h
        · exact Or.inl h
        · cases h
      · obtain ⟨_, _, hn⟩ := hd
        exact absurd (gAll _) hn
    · intro x y _ _ hne _ hdy
      obtain ⟨_, _, hnu⟩ := hdy
      cases y
      · cases x
        · exact absurd rfl hne
        · exact ⟨false, trivial, gAll false, cF⟩
      · exact absurd (gAll _) hnu
    · intro y _
      cases y
      · exact ⟨true, (fun h => nomatch h), trivial, true, trivial, gAll true⟩
      · exact ⟨false, (fun h => nomatch h), trivial, true, trivial, cT⟩
    · intro h
      obtain ⟨_, _, _, hn⟩ := h false true trivial trivial (fun h => nomatch h) ⟨true, trivial, cT⟩
      exact hn (gAll _)
    · intro h
      obtain ⟨_, _, hn⟩ := h
      exact hn ⟨true, trivial, gAll _⟩

/-- Batch controls (premise-free). -/
theorem controls : Model.Controls := ⟨laws, models⟩

end TruthCore.Results.Causality.SubtractionArgument
