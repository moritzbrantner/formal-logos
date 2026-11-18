module

public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
public import TruthCore.Results.Causality.ConcreteRootAccess.Solution

/-! Conditional CCR transfer, on one fixed esse/essence dictionary. No
well-foundedness, asymmetry, efficient cause or world-grounding bridge is used. -/

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ConcreteRootAccess (RootAccess)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

/-- Two actual beings imply the one-bearer population used below. -/
theorem populationOfTwo (p : Profile B P R) (h : TwoActualBeings p) :
    ActualEssePopulation p := by
  obtain ⟨x, _, _, hx, _⟩ := h
  exact ⟨x, hx⟩

/-- Read an existing finite root-access witness in the exact esse dictionary.
The root is uncaused before uniqueness is used; no cycle exclusion is needed. -/
theorem sourceOfAccess (p : Profile B P R)
    (hOther : DistinctEsseHasOtherActualCause p) (em : ExcludedMiddle)
    {x : B} (h : RootAccess (esseCauseGraph p) () x) :
    ∃ n, p.InAct n p.esse ∧ p.esseOf n = p.essenceOf n ∧
      (∀ c, ¬ ActualEsseCause p c n) ∧
      (n = x ∨ Relation.TransGen (ActualEsseCause p) n x) := by
  induction h with
  | @root n hn =>
    have hu : ∀ c, ¬ ActualEsseCause p c n := by
      intro c hc
      exact hn.2 c ⟨hc.2.1, hc.2.1, hc⟩
    have hi : p.esseOf n = p.essenceOf n := by
      rcases em (p.esseOf n = p.essenceOf n) with hi | hi
      · exact hi
      · obtain ⟨c, hcn, hc, hcause⟩ := hOther n ⟨hn.1.1, hi⟩
        exact (hu c ⟨hcn, hc, hn.1.1, hcause⟩).elim
    exact ⟨n, hn.1.1, hi, hu, Or.inl rfl⟩
  | @step y x _ _ hedge ih =>
    obtain ⟨n, hn, hi, hu, hp⟩ := ih
    refine ⟨n, hn, hi, hu, Or.inr ?_⟩
    rcases hp with rfl | hp
    · exact Relation.TransGen.single hedge.2.2
    · exact Relation.TransGen.tail hp hedge.2.2

/-- CCR replaces unrestricted well-foundedness in the distinct-esse step. -/
theorem distinctSourceOfClosed (p : Profile B P R)
    (hC : ClosedActualEsseCollectionsRooted p)
    (hOther : DistinctEsseHasOtherActualCause p) (em : ExcludedMiddle) :
    EveryDistinctEsseHasEsseIsEssenceSource p := by
  intro x hx
  have ha := TruthCore.Results.Causality.ConcreteRootAccess.accessOfClosed
    (esseCauseGraph p) () hC em x ⟨hx.1, hx.1⟩
  obtain ⟨n, hn, hi, _, hp⟩ := sourceOfAccess p hOther em ha
  refine ⟨n, hn, hi, ?_⟩
  rcases hp with rfl | hp
  · exact (hx.2 hi).elim
  · exact hp

/-- CCR, distinct-esse coverage, identity-bearer uniqueness, one actual
bearer and explicit excluded middle give the existing common-source endpoint. -/
theorem commonSourceOfClosed (p : Profile B P R)
    (hC : ClosedActualEsseCollectionsRooted p)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p) (hPop : ActualEssePopulation p)
    (em : ExcludedMiddle) : CommonEsseIsEssenceSource p := by
  obtain ⟨x, hx⟩ := hPop
  have access := TruthCore.Results.Causality.ConcreteRootAccess.accessOfClosed
    (esseCauseGraph p) () hC em
  obtain ⟨n, hn, hi, hu, _⟩ := sourceOfAccess p hOther em (access x ⟨hx, hx⟩)
  refine ⟨n, hn, hi, hu, ?_⟩
  intro y hy hyn
  obtain ⟨n', hn', hi', _, hp⟩ := sourceOfAccess p hOther em (access y ⟨hy, hy⟩)
  have heq : n' = n := hOne n' n hn' hn hi' hi
  subst n'
  rcases hp with hp | hp
  · exact (hyn hp.symm).elim
  · exact hp

/-- Unrestricted well-foundedness implies the weaker closed-collection premise. -/
theorem closedOfWF (p : Profile B P R) (h : NoInfiniteActualEsseCauseRegress p) :
    ClosedActualEsseCollectionsRooted p := by
  apply TruthCore.Results.Causality.ClosedGroundingRoots.closedRootedOfWF
  exact h.onFun

namespace Control

open TruthCore.Causality.ClosedGroundingRoots.Control

/-- Every root-backed control below retains the exact cause direction and
actuality guards. This helper concerns only the explicit all-actual profile. -/
theorem rooted {A : Type} (edge : Option A → Option A → Prop)
    (hroot : ∀ x, x ≠ none → edge none x)
    (hnone : ∀ c, ¬ edge c none) :
    ClosedActualEsseCollectionsRooted (controlProfile edge) ∧
    DistinctEsseHasOtherActualCause (controlProfile edge) ∧
    AtMostOneEsseIsEssence (controlProfile edge) ∧
    CommonEsseIsEssenceSource (controlProfile edge) := by
  have noCause : ∀ c, ¬ ActualEsseCause (controlProfile edge) c none :=
    fun c hc => hnone c hc.2.2.2
  have step : ∀ x, x ≠ none → ActualEsseCause (controlProfile edge) none x :=
    fun x hx => ⟨Ne.symm hx, trivial, trivial, hroot x hx⟩
  refine ⟨?_, ?_, ?_, ⟨none, trivial, rfl, noCause, fun x _ hx => .single (step x hx)⟩⟩
  · intro S hS hn x hx
    cases x with
    | none => exact hn none hx ⟨⟨trivial, trivial⟩,
        fun c hc => noCause c hc.2.2⟩
    | some a =>
      exact hn none (hS.2 (some a) none hx ⟨trivial, trivial, step _ (by intro he; cases he)⟩)
        ⟨⟨trivial, trivial⟩, fun c hc => noCause c hc.2.2⟩
  · intro x hx
    cases x with
    | none => exact (hx.2 rfl).elim
    | some a => exact ⟨none, (by intro he; cases he), trivial, hroot _ (by intro he; cases he)⟩
  · intro x y _ _ hx hy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => exact nomatch hy
    | some a => exact nomatch hx

theorem rootedInfinite : RootedInfiniteControl := by
  let edge := limitGrounder.grounds ()
  let p := controlProfile edge
  have h := rooted edge (fun x hx => Or.inl ⟨rfl, hx⟩) (by
    intro c hc
    rcases hc with h | ⟨n, _, hn⟩
    · exact h.2 rfl
    · exact nomatch hn)
  refine ⟨p, h.1, h.2.1, h.2.2.1,
    ⟨none, some 0, (by intro he; cases he), trivial, trivial⟩, h.2.2.2, ?_⟩
  apply TruthCore.Results.Causality.NecessarySupportCoverage.not_wf_of_pred
    (ActualEsseCause p) (fun x => ∃ n, x = some n) ?_ (some 0) ⟨0, rfl⟩
  rintro x ⟨n, rfl⟩
  refine ⟨some (n+1), ⟨n+1, rfl⟩, ?_, trivial, trivial, Or.inr ⟨n, rfl, rfl⟩⟩
  exact fun he => (Nat.ne_of_gt (Nat.lt_succ_self _)) (Option.some.inj he)

theorem rootedCycle : TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.RootedCycleControl := by
  let edge := TruthCore.Causality.ClosedGroundingRoots.Control.rootedCycle.grounds ()
  have h := rooted edge (fun x hx => Or.inl ⟨rfl, hx⟩) (by
    intro c hc
    rcases hc with h | h | h
    · exact h.2 rfl
    · exact nomatch h.2
    · exact nomatch h.2)
  exact ⟨controlProfile edge, h.1, h.2.1, h.2.2.1,
    ⟨none, some false, (by intro he; cases he), trivial, trivial⟩, h.2.2.2,
    ⟨by decide, trivial, trivial, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩,
    ⟨by decide, trivial, trivial, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩⟩

theorem rosterOnly : RosterOnlyControl := by
  let edge := mediateFoundation.grounds ()
  let p := controlProfile edge
  have hn : ∀ c, ¬ ActualEsseCause p c none := by
    rintro c ⟨_, _, _, k, _, hk⟩
    exact nomatch hk
  have hfirst : ∀ x, ¬ ActualEsseCause p none x := by
    rintro x ⟨_, _, _, k, hk, _⟩
    exact nomatch hk
  refine ⟨p, ⟨none, trivial, hn⟩, ?_, ?_,
    ⟨none, some 0, (by intro he; cases he), trivial, trivial⟩, ?_, ?_⟩
  · intro x hx
    cases x with
    | none => exact (hx.2 rfl).elim
    | some n =>
      refine ⟨some (n+1), ?_, trivial, n, rfl, rfl⟩
      exact fun he => (Nat.ne_of_gt (Nat.lt_succ_self _)) (Option.some.inj he)
  · intro x y _ _ hx hy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => exact nomatch hy
    | some a => exact nomatch hx
  · intro hc
    apply hc (fun x => ∃ n, x = some n) ?_ ?_ (some 0) ⟨0, rfl⟩
    · refine ⟨fun _ _ => ⟨trivial, trivial⟩, ?_⟩
      rintro x y ⟨n, rfl⟩ ⟨_, _, _, _, _, k, hy, _⟩
      exact ⟨k+1, hy⟩
    · rintro x ⟨n, rfl⟩ hr
      apply hr.2 (some (n+1))
      refine ⟨trivial, trivial, ?_, trivial, trivial, n, rfl, rfl⟩
      exact fun he => (Nat.ne_of_gt (Nat.lt_succ_self _)) (Option.some.inj he)
  · rintro ⟨n, _, hi, _, hall⟩
    have he : n = none := by
      cases n with
      | none => rfl
      | some a => exact nomatch hi
    subst n
    have hp := hall (some 0) trivial (by intro he; cases he)
    have starts : ∀ {a b}, Relation.TransGen (ActualEsseCause p) a b →
        ∃ c, ActualEsseCause p a c := by
      intro a b hab
      induction hab with
      | single h => exact ⟨_, h⟩
      | tail _ _ ih => exact ih
    obtain ⟨c, hc⟩ := starts hp
    exact hfirst c hc

theorem singletonPopulation : SingletonPopulationControl := by
  let p : Profile Unit Bool Unit := {
    InAct := fun _ _ => True
    CausesIn := fun _ _ _ => False
    essenceOf := fun _ => true
    esseOf := fun _ => true
    essentialPrinciplesAloneSufficeForEsse := fun _ => False
    esse := () }
  refine ⟨p, ⟨(), trivial⟩, ?_⟩
  rintro ⟨⟨⟩, ⟨⟩, hne, _, _⟩
  exact hne rfl

end Control

theorem controls : ClosedEsseControls :=
  ⟨Control.rootedInfinite, Control.rootedCycle, Control.rosterOnly,
    Control.singletonPopulation⟩

end TruthCore.Results.Aquinas.DeEnte.ClosedEsseSource
