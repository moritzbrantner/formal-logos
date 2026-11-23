module

public import TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause
public import TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Solution
public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
public import TruthCore.Logic.ExcludedMiddle

/-! The totality-cause route to CCR and its controls (#1724). No classical
axiom, well-foundedness, efficient cause or modal premise; excluded middle
appears only as an explicit premise of `maximalCausesOfCommon`. -/

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.AggregateEsseCause

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.DeEnte.AggregateEsseCause
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInBeingCausesAllBeingsReading)
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer (CauseOfBeingIsMoreInBeing)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

/-- With whole-to-members and no self-causation of esse, a cause of the received
totality is not itself received: an internal totality cause would cause its own
esse. Helper; the converse (external, hence uncaused) is in `commonOfAggregate`. -/
theorem totalityCauseNotReceived (p : Profile B P R) (T : B → Prop)
    (hB : TotalityCauseCausesEachReceived p T)
    (hSelf : NothingCausesItsOwnBeing p.CausesIn p.esse) :
    ∀ e, T e → ¬ ReceivedActual p e :=
  fun e hT hr => hSelf e (hB e hT e hr)

/-- The effect of an actual esse cause is received. -/
theorem receivedOf' (p : Profile B P R) {c x : B} (h : ActualEsseCause p c x) :
    ReceivedActual p x :=
  ⟨h.2.2.1, fun hall => hall c h⟩

/-- The primitive is eliminable: some predicate satisfies A and B exactly when,
if anything is received, one actual bearer is a cause of every received
bearer's esse. So the content of the totality route lies in A and B jointly.
Helper, not a registered result. -/
theorem jointIffCommonCause (p : Profile B P R) :
    (∃ T : B → Prop, ReceivedTotalityHasAggregateCause p T ∧
      TotalityCauseCausesEachReceived p T) ↔
    ((∃ x, ReceivedActual p x) →
      ∃ e, p.InAct e p.esse ∧ ∀ m, ReceivedActual p m → p.CausesIn e m p.esse) := by
  constructor
  · rintro ⟨T, hA, hB⟩ hx
    obtain ⟨e, he, hT⟩ := hA hx
    exact ⟨e, he, hB e hT⟩
  · intro h
    refine ⟨fun e => p.InAct e p.esse ∧ ∀ m, ReceivedActual p m → p.CausesIn e m p.esse,
      fun hx => ?_, fun e hT => hT.2⟩
    obtain ⟨e, he, hall⟩ := h hx
    exact ⟨e, he, he, hall⟩

/-- A cause of the totality of received actual being (A), which causes each
received member's esse (B), with no self-causation of esse, is one uncaused
actual bearer that is a distinct actual cause of every received bearer. -/
theorem commonOfAggregate (p : Profile B P R) (T : B → Prop)
    (hA : ReceivedTotalityHasAggregateCause p T)
    (hB : TotalityCauseCausesEachReceived p T)
    (hSelf : NothingCausesItsOwnBeing p.CausesIn p.esse) :
    CommonUncausedCauseOfReceived p := by
  intro hx
  obtain ⟨e, he, hT⟩ := hA hx
  have notRec := totalityCauseNotReceived p T hB hSelf e hT
  have unc : ∀ c, ¬ ActualEsseCause p c e :=
    fun c hc => notRec ⟨he, fun h => h c hc⟩
  refine ⟨e, he, unc, fun m hm => ⟨?_, he, hm.1, hB e hT m hm⟩⟩
  intro hem
  subst hem
  exact notRec hm

/-- A common uncaused cause of every received actual bearer gives CCR: any
closed collection with a member contains that cause, which is a root. -/
theorem closedOfCommon (p : Profile B P R) (h : CommonUncausedCauseOfReceived p) :
    ClosedActualEsseCollectionsRooted p := by
  intro S hS hn x hx
  have hrec : ∀ y, S y → ReceivedActual p y := by
    intro y hy
    refine ⟨(hS.1 y hy).1, fun hall => hn y hy ⟨hS.1 y hy, fun c hc => hall c hc.2.2⟩⟩
  obtain ⟨e, he, hu, hall⟩ := h ⟨x, hrec x hx⟩
  have hSe : S e := hS.2 x e hx ⟨he, he, hall x (hrec x hx)⟩
  exact hn e hSe ⟨⟨he, he⟩, fun c hc => hu c hc.2.2⟩

/-- The common uncaused cause, distinct-esse coverage, identity uniqueness,
causal ascent at esse and excluded middle give the fixed-esse maximum
principle consumed by the GOD_4 existence bundle. Unlike
`MaximalFromEsseSource.maximalCauses`, no CCR, population or esse-cause
composition premise is used: the common cause already causes every received
bearer, and uniqueness shows every other actual bearer is received. -/
theorem maximalCausesOfCommon (p : Profile B P R) (MoreIn : R → B → B → Prop)
    (hCommon : CommonUncausedCauseOfReceived p)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p)
    (hAscent : CauseOfBeingIsMoreInBeing p.CausesIn MoreIn p.esse)
    (hEM : ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse := by
  -- An uncaused actual bearer has esse equal to essence.
  have identity : ∀ x, p.InAct x p.esse → (∀ c, ¬ ActualEsseCause p c x) →
      p.esseOf x = p.essenceOf x := by
    intro x hx hu
    rcases hEM (p.esseOf x = p.essenceOf x) with h | h
    · exact h
    · obtain ⟨c, hcx, hc, hcause⟩ := hOther x ⟨hx, h⟩
      exact (hu c ⟨hcx, hc, hx, hcause⟩).elim
  intro m hm x hxm hx
  rcases hEM (∃ y, ReceivedActual p y) with hRec | hNone
  · obtain ⟨e, he, hu, hall⟩ := hCommon hRec
    -- Every actual bearer other than e is received.
    have hRecv : ∀ y, p.InAct y p.esse → y ≠ e → ReceivedActual p y := by
      intro y hy hye
      refine ⟨hy, fun hyu => hye ?_⟩
      exact hOne y e hy he (identity y hy hyu) (identity e he hu)
    have hme : m = e := by
      rcases hEM (m = e) with h | hne
      · exact h
      · exact (hm.2 e (hAscent e m (fun h => hne h.symm)
          (hall m (hRecv m hm.1 hne)).2.2.2)).elim
    subst hme
    exact (hall x (hRecv x hx hxm)).2.2.2
  · -- Nothing is received, so every actual bearer is an identity bearer.
    have unc : ∀ y, p.InAct y p.esse → ∀ c, ¬ ActualEsseCause p c y :=
      fun y hy c hc => hNone ⟨y, receivedOf' p hc⟩
    exact (hxm (hOne x m hx hm.1 (identity x hx (unc x hx))
      (identity m hm.1 (unc m hm.1)))).elim

namespace Control

/-- A nonempty collection of actual bearers, closed under actual esse causes,
every member of which has one, refutes CCR. -/
theorem notClosedOfReceivedClosed (p : Profile B P R) (S : B → Prop)
    (hAct : ∀ x, S x → p.InAct x p.esse)
    (hClosed : ∀ x y, S x → ActualEsseCause p y x → S y)
    (hCaused : ∀ x, S x → ∃ c, ActualEsseCause p c x) (x₀ : B) (h₀ : S x₀) :
    ¬ ClosedActualEsseCollectionsRooted p := by
  intro h
  refine h S ⟨fun x hx => ⟨hAct x hx, hAct x hx⟩, fun x y hx hy => hClosed x y hx hy.2.2⟩
    ?_ x₀ h₀
  intro x hx hr
  obtain ⟨c, hc⟩ := hCaused x hx
  exact hr.2 c ⟨hc.2.1, hc.2.1, hc⟩

theorem someNe (n : Nat) : (some n : Option Nat) ≠ none := fun h => nomatch h

theorem succNe (n : Nat) : n + 1 ≠ n := Nat.succ_ne_self n

/-- (1) Positive joint model with a root-backed infinite descent. -/
theorem jointModel : ∃ (p : Profile (Option Nat) Bool Unit) (T : Option Nat → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ TotalityCauseCausesEachReceived p T ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ (∃ x, ReceivedActual p x) ∧
    CommonUncausedCauseOfReceived p ∧ ClosedActualEsseCollectionsRooted p ∧
    ¬ NoInfiniteActualEsseCauseRegress p := by
  let p := controlProfile commonRootEdge
  have hnone : ∀ c, ¬ commonRootEdge c none := by
    intro c hc
    rcases hc with h | ⟨n, _, hn⟩
    · exact h.2 rfl
    · exact nomatch hn
  have h := TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.Control.rooted commonRootEdge
    (fun x hx => Or.inl ⟨rfl, hx⟩) hnone
  have recNotNone : ∀ m, ReceivedActual p m → m ≠ none := by
    intro m hm hmn
    subst hmn
    exact hm.2 (fun c hc => hnone c hc.2.2.2)
  have hA : ReceivedTotalityHasAggregateCause p (· = none) :=
    fun _ => ⟨none, trivial, rfl⟩
  have hB : TotalityCauseCausesEachReceived p (· = none) := by
    intro e he m hm
    subst he
    exact Or.inl ⟨rfl, recNotNone m hm⟩
  have hSelf : NothingCausesItsOwnBeing p.CausesIn p.esse := by
    intro x hx
    rcases hx with h | ⟨n, hc, hn⟩
    · exact h.2 h.1
    · rw [hc] at hn
      exact succNe n (Option.some.inj hn)
  have hRec : ∃ x, ReceivedActual p x :=
    ⟨some 0, receivedOf' p (c := none)
      ⟨(someNe 0).symm, trivial, trivial, Or.inl ⟨rfl, someNe 0⟩⟩⟩
  refine ⟨p, (· = none), hA, hB, hSelf, h.2.1, h.2.2.1, hRec,
    commonOfAggregate p _ hA hB hSelf, h.1, ?_⟩
  apply TruthCore.Results.Causality.NecessarySupportCoverage.not_wf_of_pred
    (ActualEsseCause p) (fun x => ∃ n, x = some n) ?_ (some 0) ⟨0, rfl⟩
  rintro x ⟨n, rfl⟩
  refine ⟨some (n + 1), ⟨n + 1, rfl⟩, ?_, trivial, trivial, Or.inr ⟨n, rfl, rfl⟩⟩
  exact fun he => succNe n (Option.some.inj he)

/-- (2) Hume–Edwards regress: no predicate satisfies both A and B (otherwise
`commonOfAggregate` and `closedOfCommon` would give CCR); the distributive
reading satisfies A and fails B; the other listed conditions hold and CCR
fails. -/
theorem humeEdwardsRegress : ∃ p : Profile Nat Bool Unit,
    (∀ T : Nat → Prop,
      ¬ (ReceivedTotalityHasAggregateCause p T ∧ TotalityCauseCausesEachReceived p T)) ∧
    ReceivedTotalityHasAggregateCause p (DistributiveTotalityCause p) ∧
    ¬ TotalityCauseCausesEachReceived p (DistributiveTotalityCause p) ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ (∀ x, ReceivedActual p x) ∧
    (∀ x, ¬ Relation.TransGen (ActualEsseCause p) x x) ∧
    ¬ ClosedActualEsseCollectionsRooted p := by
  let p := regressProfile
  have edge : ∀ x, ActualEsseCause p (x + 1) x :=
    fun x => ⟨succNe x, trivial, trivial, rfl⟩
  have hRec : ∀ x, ReceivedActual p x := fun x => receivedOf' p (edge x)
  have below : ∀ {a b}, Relation.TransGen (ActualEsseCause p) a b → b < a := by
    intro a b hab
    induction hab with
    | single h =>
      have h' : _ = _ := h.2.2.2
      rw [h']
      exact Nat.lt_succ_self _
    | tail _ h ih =>
      have h' : _ = _ := h.2.2.2
      rw [h'] at ih
      exact Nat.lt_trans (Nat.lt_succ_self _) ih
  have hSelf : NothingCausesItsOwnBeing p.CausesIn p.esse :=
    fun x hx => (succNe x) hx.symm
  have hNot : ¬ ClosedActualEsseCollectionsRooted p :=
    notClosedOfReceivedClosed p (fun _ => True) (fun _ _ => trivial)
      (fun _ _ _ _ => trivial) (fun x _ => ⟨x + 1, edge x⟩) 0 trivial
  refine ⟨p, ?_, ?_, ?_, hSelf, ?_, ?_, hRec, ?_, hNot⟩
  · rintro T ⟨hA, hB⟩
    exact hNot (closedOfCommon p (commonOfAggregate p T hA hB hSelf))
  · intro _
    exact ⟨1, trivial, 0, hRec 0, edge 0⟩
  · intro hB
    have h : (1 : Nat) = 5 + 1 := hB 1 ⟨0, hRec 0, edge 0⟩ 5 (hRec 5)
    exact Nat.noConfusion h (fun h' => Nat.noConfusion h')
  · intro x _
    exact ⟨x + 1, succNe x, trivial, rfl⟩
  · intro x _ _ _ h _
    exact nomatch h
  · intro x hx
    exact Nat.lt_irrefl x (below hx)

/-- (3) Two-bearer loop whose members are each a totality cause: whole to
members fails (a member would cause itself); CCR fails. -/
theorem internalLoop : ∃ (p : Profile Bool Bool Unit) (T : Bool → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ ¬ TotalityCauseCausesEachReceived p T ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧ (∀ x, ReceivedActual p x) ∧
    ¬ ClosedActualEsseCollectionsRooted p := by
  let p := TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.sourceFreeFiniteCircle
  have edge : ∀ x : Bool, ActualEsseCause p (!x) x := by
    intro x
    refine ⟨?_, trivial, trivial, ?_⟩
    · cases x <;> decide
    · show (!x) ≠ x
      cases x <;> decide
  have hRec : ∀ x, ReceivedActual p x := fun x => receivedOf' p (edge x)
  refine ⟨p, fun _ => True, fun _ => ⟨true, trivial, trivial⟩, ?_, ?_, hRec, ?_⟩
  · intro hB
    exact (hB true trivial true (hRec true)) rfl
  · intro x hx
    exact hx rfl
  · exact notClosedOfReceivedClosed p (fun _ => True) (fun _ _ => trivial)
      (fun _ _ _ _ => trivial) (fun x _ => ⟨!x, edge x⟩) false trivial

/-- (4) An actual uncaused totality cause that supplies no member, beside a
rootless chain: whole to members fails; CCR fails. -/
theorem idleExplainer : ∃ (p : Profile (Option Nat) Bool Unit) (T : Option Nat → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ ¬ TotalityCauseCausesEachReceived p T ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    (∃ e, T e ∧ p.InAct e p.esse ∧ ∀ c, ¬ ActualEsseCause p c e) ∧
    ¬ ClosedActualEsseCollectionsRooted p := by
  let p := controlProfile idleRootEdge
  have edge : ∀ n, ActualEsseCause p (some (n + 1)) (some n) :=
    fun n => ⟨fun h => succNe n (Option.some.inj h), trivial, trivial, n, rfl, rfl⟩
  refine ⟨p, (· = none), fun _ => ⟨none, trivial, rfl⟩, ?_, ?_,
    ⟨none, rfl, trivial, fun c hc => ?_⟩, ?_⟩
  · intro hB
    obtain ⟨n, hn, _⟩ := hB none rfl (some 0) (receivedOf' p (edge 0))
    exact nomatch hn
  · intro x hx
    obtain ⟨n, hc, hn⟩ := hx
    rw [hc] at hn
    exact succNe n (Option.some.inj hn)
  · obtain ⟨_, _, hn⟩ := hc.2.2.2
    exact nomatch hn
  · refine notClosedOfReceivedClosed p (fun x => ∃ n, x = some n) (fun _ _ => trivial)
      ?_ ?_ (some 0) ⟨0, rfl⟩
    · rintro x y ⟨n, rfl⟩ ⟨_, _, _, k, hy, _⟩
      exact ⟨k + 1, hy⟩
    · rintro x ⟨n, rfl⟩
      exact ⟨some (n + 1), edge n⟩

/-- (5) A totality cause that causes its own esse: A and B hold, no
self-causation fails, CCR fails. -/
theorem selfCauser : ∃ (p : Profile Bool Bool Unit) (T : Bool → Prop),
    ReceivedTotalityHasAggregateCause p T ∧ TotalityCauseCausesEachReceived p T ∧
    ¬ NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ ClosedActualEsseCollectionsRooted p := by
  let p := selfCauserProfile
  have edge : ∀ x : Bool, ActualEsseCause p (!x) x := by
    intro x
    refine ⟨?_, trivial, trivial, trivial⟩
    cases x <;> decide
  refine ⟨p, fun _ => True, fun _ => ⟨true, trivial, trivial⟩,
    fun _ _ _ _ => trivial, fun h => h true trivial, ?_⟩
  exact notClosedOfReceivedClosed p (fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun x _ => ⟨!x, edge x⟩) false trivial

/-- Rank for the ascending chain: every actual cause has lower rank. -/
def rank : Option Nat → Nat
  | none => 0
  | some n => n + 1

/-- (6) CCR and the finite-path common source hold on an ascending rooted
chain, but no single bearer causes every received bearer. -/
theorem ccrWithoutCommonCause : ∃ p : Profile (Option Nat) Bool Unit,
    ClosedActualEsseCollectionsRooted p ∧ DistinctEsseHasOtherActualCause p ∧
    AtMostOneEsseIsEssence p ∧ CommonEsseIsEssenceSource p ∧
    (∃ x, ReceivedActual p x) ∧ ¬ CommonUncausedCauseOfReceived p := by
  let p := controlProfile ascendingEdge
  have first : ActualEsseCause p none (some 0) :=
    ⟨(someNe 0).symm, trivial, trivial, Or.inl ⟨rfl, rfl⟩⟩
  have next : ∀ n, ActualEsseCause p (some n) (some (n + 1)) :=
    fun n => ⟨fun h => succNe n (Option.some.inj h).symm, trivial, trivial,
      Or.inr ⟨n, rfl, rfl⟩⟩
  have noneUncaused : ∀ c, ¬ ActualEsseCause p c none := by
    intro c hc
    rcases hc.2.2.2 with h | ⟨_, _, h⟩
    · exact nomatch h.2
    · exact nomatch h
  have path : ∀ n, Relation.TransGen (ActualEsseCause p) none (some n) := by
    intro n
    induction n with
    | zero => exact .single first
    | succ n ih => exact .tail ih (next n)
  have wf : NoInfiniteActualEsseCauseRegress p := by
    refine Subrelation.wf (r := InvImage (· < ·) rank) ?_ (InvImage.wf rank Nat.lt_wfRel.wf)
    intro c x hc
    rcases hc.2.2.2 with ⟨rfl, rfl⟩ | ⟨n, rfl, rfl⟩
    · exact Nat.zero_lt_succ 0
    · exact Nat.lt_succ_self (n + 1)
  refine ⟨p, TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.closedOfWF p wf, ?_, ?_,
    ⟨none, trivial, rfl, noneUncaused, ?_⟩, ⟨some 0, receivedOf' p first⟩, ?_⟩
  · intro x hx
    cases x with
    | none => exact (hx.2 rfl).elim
    | some n =>
      cases n with
      | zero => exact ⟨none, first.1, trivial, first.2.2.2⟩
      | succ k => exact ⟨some k, (next k).1, trivial, (next k).2.2.2⟩
  · intro x y _ _ hx hy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => exact nomatch hy
    | some a => exact nomatch hx
  · intro x _ hx
    cases x with
    | none => exact (hx rfl).elim
    | some n => exact path n
  · intro hCommon
    obtain ⟨e, _, _, hall⟩ := hCommon ⟨some 0, receivedOf' p first⟩
    have h0 := (hall (some 0) (receivedOf' p first)).2.2.2
    have h1 := (hall (some 1) (receivedOf' p (next 0))).2.2.2
    rcases h0 with ⟨rfl, _⟩ | ⟨_, _, h⟩
    · rcases h1 with ⟨_, h⟩ | ⟨_, h, _⟩
      · exact nomatch h
      · exact nomatch h
    · exact nomatch h

/-- (7) Plural foundations: two independent identity roots, a transitively
closed relation, CCR and coverage, but no common uncaused cause. -/
theorem pluralRoots : ∃ p : Profile (Bool × Bool) Bool Unit,
    ClosedActualEsseCollectionsRooted p ∧ DistinctEsseHasOtherActualCause p ∧
    NothingCausesItsOwnBeing p.CausesIn p.esse ∧
    ¬ AtMostOneEsseIsEssence p ∧ (∃ x, ReceivedActual p x) ∧
    (∀ a b c, p.CausesIn a b p.esse → p.CausesIn b c p.esse → p.CausesIn a c p.esse) ∧
    ¬ CommonUncausedCauseOfReceived p := by
  let p := pluralRootsProfile
  have edge : ∀ i : Bool, ActualEsseCause p (false, i) (true, i) :=
    fun i => ⟨fun h => (nomatch congrArg Prod.fst h), trivial, trivial,
      show (false, i).1 = false ∧ (true, i).1 = true ∧ (false, i).2 = (true, i).2 from
        ⟨rfl, rfl, rfl⟩⟩
  have wf : NoInfiniteActualEsseCauseRegress p := by
    refine Subrelation.wf (r := InvImage (· < ·) (fun x : Bool × Bool => cond x.1 1 0)) ?_
      (InvImage.wf _ Nat.lt_wfRel.wf)
    intro c x hc
    obtain ⟨hc1, hx1, _⟩ := hc.2.2.2
    show cond c.1 1 0 < cond x.1 1 0
    rw [hc1, hx1]
    exact Nat.zero_lt_one
  refine ⟨p, TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource.closedOfWF p wf, ?_, ?_, ?_,
    ⟨(true, false), receivedOf' p (edge false)⟩, ?_, ?_⟩
  · rintro ⟨x1, x2⟩ hx
    cases x1 with
    | false => exact (hx.2 rfl).elim
    | true => exact ⟨(false, x2), (edge x2).1, trivial, (edge x2).2.2.2⟩
  · intro x hx
    have h1 : x.1 = false := hx.1
    have h2 : x.1 = true := hx.2.1
    rw [h1] at h2
    exact nomatch h2
  · intro h
    have := h (false, false) (false, true) trivial trivial rfl rfl
    exact nomatch congrArg Prod.snd this
  · intro a b c hab hbc
    have h1 : b.1 = true := hab.2.1
    have h2 : b.1 = false := hbc.1
    rw [h1] at h2
    exact nomatch h2
  · intro hCommon
    obtain ⟨e, _, _, hall⟩ := hCommon ⟨(true, false), receivedOf' p (edge false)⟩
    have h0 : e.2 = false := (hall (true, false) (receivedOf' p (edge false))).2.2.2.2.2
    have h1 : e.2 = true := (hall (true, true) (receivedOf' p (edge true))).2.2.2.2.2
    rw [h0] at h1
    exact nomatch h1

end Control

/-- The seven interpretations together. -/
theorem controls : AggregateEsseCauseControls :=
  ⟨Control.jointModel, Control.humeEdwardsRegress, Control.internalLoop,
    Control.idleExplainer, Control.selfCauser, Control.ccrWithoutCommonCause,
    Control.pluralRoots⟩

end TruthCore.Results.Aquinas.DeEnte.AggregateEsseCause
