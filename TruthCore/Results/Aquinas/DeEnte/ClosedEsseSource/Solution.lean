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


/-- A finite all-received cycle demonstrates that local esse-cause coverage,
population, and at-most-one identity bearer do not themselves yield CCR or a
common source. It does not show metaphysical possibility or productive supply. -/
theorem sourceFreeFiniteCircle : SourceFreeFiniteCircleControl := by
  let p := TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.sourceFreeFiniteCircle
  have hd : ∀ x, DistinctEsseAt p x := by
    intro x
    refine ⟨trivial, ?_⟩
    change true ≠ false
    decide
  have hs : ∀ x, ∃ c, ActualEsseCause p c x := by
    intro x
    cases x with
    | false =>
      refine ⟨true, ⟨by decide, trivial, trivial, ?_⟩⟩
      change true ≠ false
      decide
    | true =>
      refine ⟨false, ⟨by decide, trivial, trivial, ?_⟩⟩
      change false ≠ true
      decide
  have hOther : DistinctEsseHasOtherActualCause p := by
    intro x _
    obtain ⟨c, hc⟩ := hs x
    exact ⟨c, hc.1, hc.2.1, hc.2.2.2⟩
  have hOne : AtMostOneEsseIsEssence p := by
    intro x y _ _ h _
    cases h
  have hNotClosed : ¬ ClosedActualEsseCollectionsRooted p := by
    intro h
    have hS : TruthCore.Causality.ClosedGroundingRoots.GroundClosedActual
        (esseCauseGraph p) () (fun _ => True) := by
      constructor
      · intro _ _
        exact ⟨trivial, trivial⟩
      · intro _ _ _ _
        trivial
    have hn : ∀ x, (fun _ : Bool => True) x →
        ¬ ActualRoot (esseCauseGraph p) () x := by
      intro x _ hr
      obtain ⟨c, hc⟩ := hs x
      exact hr.2 c ⟨hc.2.1, hc.2.1, hc⟩
    exact (h (fun _ => True) hS hn false) trivial
  have hNoCommon : ¬ CommonEsseIsEssenceSource p := by
    rintro ⟨n, _, _, hUncaused, _⟩
    obtain ⟨c, hc⟩ := hs n
    exact hUncaused c hc
  refine ⟨hd, hOther, hOne, ⟨false, trivial⟩, hs, ?_, ?_, hNotClosed, hNoCommon⟩
  · refine ⟨by decide, trivial, trivial, ?_⟩
    change false ≠ true
    decide
  · refine ⟨by decide, trivial, trivial, ?_⟩
    change true ≠ false
    decide

/-- Pure transmission cannot select a populated world uniquely: the
all-absent state satisfies every rule that only activates from already-active
actual esse-cause suppliers. This holds on any carrier, with no WF assumption. -/
theorem emptyFixedOfEntirelyBorrowed (p : Profile B P R)
    (rule : (B → Prop) → B → Prop)
    (hBorrow : EntirelyBorrowedRule p rule) :
    SupplierStateFixed rule (fun _ => False) := by
  intro x
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ := hBorrow _ x h
    exact hc
  · intro h
    exact False.elim h

/-- If the same entirely borrowed rule admits an inhabited fixed state, it
also admits a distinct empty fixed state. In particular no mathematical
uniqueness claim can select that populated state under this precise rule.
This does NOT deny its possible actuality or any nonproductive feedback. -/
theorem populatedBorrowedStateNotUnique (p : Profile B P R)
    (rule : (B → Prop) → B → Prop) (state : B → Prop)
    (hBorrow : EntirelyBorrowedRule p rule)
    (hState : SupplierStateFixed rule state) (hPop : ∃ x, state x) :
    ∃ other : B → Prop,
      SupplierStateFixed rule state ∧ SupplierStateFixed rule other ∧ other ≠ state := by
  refine ⟨fun _ => False, hState, emptyFixedOfEntirelyBorrowed p rule hBorrow, ?_⟩
  intro hEq
  obtain ⟨x, hx⟩ := hPop
  have hEqAt := congrArg (fun f : B → Prop => f x) hEq
  exact hEqAt.mpr hx

/-- A UNIQUE populated fixed state under the seed-or-borrowed necessary
condition needs some seed. The proof does not identify that seed with an
actual bearer, or derive the actuality of the unique mathematical solution. -/
theorem uniquePopulatedStateNeedsSeed (p : Profile B P R)
    (seed : B → Prop) (rule : (B → Prop) → B → Prop) (state : B → Prop)
    (hRule : SeedOrBorrowedRule p seed rule)
    (hState : SupplierStateFixed rule state) (hPop : ∃ x, state x)
    (hUnique : ∀ other : B → Prop, SupplierStateFixed rule other → other = state) :
    ∃ x, seed x := by
  classical
  by_contra hNone
  have hBorrow : EntirelyBorrowedRule p rule := by
    intro proposed x hx
    rcases hRule proposed x hx with hSeed | hSupplier
    · exact (hNone ⟨x, hSeed⟩).elim
    · exact hSupplier
  obtain ⟨other, _, hOther, hNe⟩ :=
    populatedBorrowedStateNotUnique p rule state hBorrow hState hPop
  exact hNe (hUnique other hOther)

/-- One narrower sufficient source principle, without universal WF or CCR.
The additional OPEN bridges say that independent seed inputs really activate
in this fixed state and are actual, uncaused bearers in precisely the same
esse-cause relation. The result obtains ONE r-root in the state, not finite
root access for every other bearer or the same-source/God conclusion. -/
theorem uniquePopulatedStateHasActualRoot (p : Profile B P R)
    (seed : B → Prop) (rule : (B → Prop) → B → Prop) (state : B → Prop)
    (hRule : SeedOrBorrowedRule p seed rule)
    (hSeedRoot : SeedIsActualEsseRoot p seed)
    (hSeedActive : ∀ x, seed x → rule state x)
    (hState : SupplierStateFixed rule state) (hPop : ∃ x, state x)
    (hUnique : ∀ other : B → Prop, SupplierStateFixed rule other → other = state) :
    ∃ n, state n ∧ p.InAct n p.esse ∧ ∀ c, ¬ ActualEsseCause p c n := by
  obtain ⟨n, hn⟩ :=
    uniquePopulatedStateNeedsSeed p seed rule state hRule hState hPop hUnique
  obtain ⟨hActual, hUncaused⟩ := hSeedRoot n hn
  exact ⟨n, (hState n).mp (hSeedActive n hn), hActual, hUncaused⟩


/-- With InAct varying along with the state, the empty configuration has
no actual suppliers and satisfies the reciprocal support equation. It is
an instance of #1878's `emptyFixedOfEntirelyBorrowed`
(`emptyCircleStateFixedOfBorrowing` below): varying InAct preserves the
empty fixed point. Nothing about metaphysical applicability follows. -/
theorem emptyCircleStateFixed :
    CircleStateFixed (fun _ : Bool => False) := by
  intro x
  constructor
  · intro hx
    exact hx.elim
  · rintro ⟨c, hc⟩
    exact hc.2.2.1

/-- Both candidate bearers present: each has the other as a same-r input. -/
theorem fullCircleStateFixed :
    CircleStateFixed (fun _ : Bool => True) := by
  intro x
  constructor
  · intro _
    cases x with
    | false =>
      refine ⟨true, ?_, trivial, trivial, ?_⟩
      · change true ≠ false
        decide
      · change true ≠ false
        decide
    | true =>
      refine ⟨false, ?_, trivial, trivial, ?_⟩
      · change false ≠ true
        decide
      · change false ≠ true
        decide
  · intro _
    trivial

/-- Of the profiles satisfying the reciprocal equation and the additional
global population requirement, only the both-present configuration survives,
pointwise. This is an extensional claim; no propext or funext is used. -/
theorem populatedCircleAllBearers (state : Bool → Prop)
    (h : HolisticCircleAdmissible state) : ∀ x, state x := by
  obtain ⟨hFixed, ⟨w, hw⟩⟩ := h
  have hFalse : state false := by
    cases w with
    | false => exact hw
    | true =>
      obtain ⟨c, hc⟩ := (hFixed true).mp hw
      cases c with
      | false => exact hc.2.1
      | true => exact (hc.1 rfl).elim
  have hTrue : state true := by
    obtain ⟨c, hc⟩ := (hFixed false).mp hFalse
    cases c with
    | false => exact (hc.1 rfl).elim
    | true => exact hc.2.1
  intro x
  cases x with
  | false => exact hFalse
  | true => exact hTrue

/-- For the mode-unspecified r only: a unique admitted populated state of
the two-bearer circle has no r-root. The circle is excluded at the per se
productive scope by `noPerSeCausalLoop` once the priority bridge is
supplied. Actuality guards vary coherently, but productive exercise,
metaphysical admission of the nonempty whole, and collective full grounding
are not encoded. The nonemptiness requirement does the selection work. -/
theorem stateIndexedHolisticCircle : StateIndexedHolisticCircleControl := by
  have hAll : ∀ x,
      ∃ c, ActualEsseCause (circleAtState (fun _ => True)) c x := by
    intro x
    cases x with
    | false =>
      refine ⟨true, ?_, trivial, trivial, ?_⟩
      · change true ≠ false
        decide
      · change true ≠ false
        decide
    | true =>
      refine ⟨false, ?_, trivial, trivial, ?_⟩
      · change false ≠ true
        decide
      · change false ≠ true
        decide
  refine ⟨emptyCircleStateFixed,
    ⟨fullCircleStateFixed, ⟨false, trivial⟩⟩, ?_, hAll, ?_⟩
  · intro state hs
    exact populatedCircleAllBearers state hs
  · rintro ⟨n, hn⟩
    obtain ⟨c, hc⟩ := hAll n
    exact hn c hc

/-- The circle's supply rule is an #1878 entirely-borrowed rule for the
fixed all-actual circle profile. -/
theorem circleRuleEntirelyBorrowed :
    EntirelyBorrowedRule
      TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource.sourceFreeFiniteCircle
      circleRule := by
  rintro state x ⟨c, hne, hc, _, hcause⟩
  exact ⟨c, ⟨hne, trivial, trivial, hcause⟩, hc⟩

/-- `CircleStateFixed` is `SupplierStateFixed circleRule`, biconditional
flipped. -/
theorem circleStateFixedIff (state : Bool → Prop) :
    CircleStateFixed state ↔ SupplierStateFixed circleRule state :=
  ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

/-- The empty fixed point, obtained from #1878's general theorem. -/
theorem emptyCircleStateFixedOfBorrowing :
    CircleStateFixed (fun _ : Bool => False) :=
  (circleStateFixedIff _).mpr
    (emptyFixedOfEntirelyBorrowed _ circleRule circleRuleEntirelyBorrowed)

/-- Every tail is a fixed point of the acyclic analogue: `x + 1` supplies
`x`, and the reverse direction is the recipient guard. -/
theorem tailFromFixed (k : Nat) : TailStateFixed (tailFrom k) := by
  intro x
  constructor
  · intro hx
    exact ⟨x + 1, Nat.succ_ne_self x, Nat.le_succ_of_le hx, hx, rfl⟩
  · rintro ⟨_, hc⟩
    exact hc.2.2.1

/-- Nonempty admission does not select uniquely on the acyclic analogue. -/
theorem stateIndexedTail : StateIndexedTailControl := by
  have hCover : ∀ k x, tailFrom k x →
      ∃ c, ActualEsseCause (tailAtState (tailFrom k)) c x :=
    fun k x hx => ((tailFromFixed k) x).mp hx
  refine ⟨fun k => ⟨tailFromFixed k, k, Nat.le_refl k⟩, hCover, ?_,
    Nat.le_refl 0, Nat.not_succ_le_zero 0⟩
  rintro k ⟨n, hn, hRoot⟩
  obtain ⟨c, hc⟩ := hCover k n hn
  exact hRoot c hc

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
