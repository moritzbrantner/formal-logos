module

public import TruthCore.Latin.Aquinas.DeEnte.RootInterface
public import TruthCore.Results.Aquinas.DeEnte.EsseSource.Solution
public import TruthCore.Results.Causality.WholeRosterFoundation.Solution

/-!
# De ente: the first source at the root interface, and a per se regress (#1635)

* `uniqueActualRootFromDeEnte`: root existence from population and
  whole-roster nontrapping (`WholeRosterFoundation.actualRootExists`) composed
  with the #1628 uniqueness `atMostOneActualRootFromDeEnte` gives the
  root-uniqueness interface `UniqueActualRootAt`.
* `deEnteFirstSourceIsActualRoot`: the De ente first source is an actual
  concrete root at `w`, from the two OPEN bridges of `RootInterface`,
  existing-in-act and no self-causation of being.
* `uniqueActualRootFromDeEnteSource`: that root with at most one actual root
  gives `UniqueActualRootAt` without whole-roster nontrapping.
* `perSeRegressOfUnrestricted`: the unrestricted regress premise implies its
  per se version (strength order).
* `unrestrictedRegressFromPerSe`: the per se regress and the per se bridge
  give the unrestricted regress premise.

Nothing here supplies efficiency, conservation, modal necessity or God
identification.
-/

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.RootInterface

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {B P R : Type}

/-- Interface 1: an actual root exists (population, whole-roster nontrapping,
excluded middle) and, by De ente's other-cause step and at most one being
whose esse is its essence, every actual root equals it. -/
theorem uniqueActualRootFromDeEnte {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p) : UniqueActualRootAt m w := by
  obtain ⟨n, hn⟩ :=
    TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists m w hPop hWhole hEM
  exact ⟨n, hn, fun x hx =>
    TruthCore.Results.Aquinas.DeEnte.EsseSource.atMostOneActualRootFromDeEnte
      m w p hEM hExisting hEsse hOther hOne x n hx hn⟩

/-- Interface 2: the De ente first source is an actual concrete root at `w`.
It is concrete and exists at `w` by the concreteness bridge; an actual
concrete ground y of it would cause its esse (ground bridge), be in act
(existing-in-act) and differ from it (no self-causation), so y would be an
actual cause of its esse, which the first source has none of. -/
theorem deEnteFirstSourceIsActualRoot {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R)
    (hSource : CommonEsseIsEssenceSource p)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hConcrete : ActualEsseIsEssenceIsActualConcreteAt m w p)
    (hGround : GroundOfEsseIsEssenceBeingCausesItsEsse m w p)
    (hNoSelf : NothingCausesItsOwnBeing p.CausesIn p.esse) :
    DeEnteFirstSourceIsActualRootAt m w p := by
  obtain ⟨n, hn, hnId, hUncaused, hChain⟩ := hSource
  refine ⟨n, ⟨hConcrete n hn hnId, fun y hy => ?_⟩, hn, hnId, hUncaused, hChain⟩
  have hCause : p.CausesIn y n p.esse := hGround y n hy hn hnId
  have hne : y ≠ n := fun h => hNoSelf n (h ▸ hCause)
  exact hUncaused y ⟨hne, hExisting y hy.2.1, hn, hCause⟩

/-- The De ente first source as an actual root, with at most one actual root,
is the unique actual root at `w`. -/
theorem uniqueActualRootFromDeEnteSource {W : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    (p : Profile B P R)
    (hRoot : DeEnteFirstSourceIsActualRootAt m w p)
    (hAtMost : AtMostOneActualRootAt m w) : UniqueActualRootAt m w := by
  obtain ⟨n, hn, _⟩ := hRoot
  exact ⟨n, hn, fun x hx => hAtMost x n hx hn⟩

/-- Strength order: no infinite chain of actual causes of being gives no
infinite chain of per se actual causes of being, for any per se link. -/
theorem perSeRegressOfUnrestricted (p : Profile B P R) (AsCaused : B → B → Prop)
    (hRegress : NoInfiniteActualEsseCauseRegress p) :
    NoInfinitePerSeActualEsseCauseRegress p AsCaused :=
  Subrelation.wf (fun h => h.1) hRegress

/-- The per se regress and the per se bridge give the unrestricted regress.
By per se induction on x: an actual cause c of x that has an actual cause d
causes x per se (bridge), so the induction hypothesis covers c; an actual
cause with no actual cause is accessible outright. -/
theorem unrestrictedRegressFromPerSe (p : Profile B P R) (AsCaused : B → B → Prop)
    (hPerSe : NoInfinitePerSeActualEsseCauseRegress p AsCaused)
    (hBridge : CausedEsseCauseCausesAsCaused p AsCaused) :
    NoInfiniteActualEsseCauseRegress p := by
  refine ⟨fun x => ?_⟩
  induction x using hPerSe.induction with
  | _ x ih =>
    refine Acc.intro x (fun c hc => Acc.intro c (fun d hd => ?_))
    exact (ih c ⟨hc, hBridge c x hc ⟨d, hd⟩⟩).inv hd

/-! ## Controls -/

section Controls

open TruthCore.Results.Aquinas.DeEnte.EsseSource (regressProfile)

theorem perAccidensRegressControl : PerAccidensRegressControl := by
  refine ⟨regressProfile, fun _ _ => False,
    fun x _ => ⟨x + 1, Nat.succ_ne_self x, trivial, rfl⟩,
    ⟨fun a => Acc.intro a (fun _ h => h.2.elim)⟩, ?_, ?_, ?_⟩
  · intro hBridge
    exact hBridge 1 0 ⟨Nat.succ_ne_self 0, trivial, trivial, rfl⟩
      ⟨2, Nat.succ_ne_self 1, trivial, trivial, rfl⟩
  · intro hWF
    have hNoAcc : ∀ n, Acc (ActualEsseCause regressProfile) n → False := by
      intro n hAcc
      induction hAcc with
      | intro x _ ih => exact ih (x + 1) ⟨Nat.succ_ne_self x, trivial, trivial, rfl⟩
    exact hNoAcc 0 (hWF.apply 0)
  · intro h
    obtain ⟨_, _, hId, _⟩ := h 0 ⟨trivial, Bool.noConfusion⟩
    exact Bool.noConfusion hId

/-- `true` has esse equal to essence and causes the esse of `false`. -/
def sourceProfile : Profile Bool Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c = true ∧ x = false
  essenceOf := fun x => x
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- As `sourceProfile`, and `true` also causes its own esse. -/
def selfProfile : Profile Bool Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c _ _ => c = true
  essenceOf := fun x => x
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- Only `true` has esse equal to essence in these profiles. -/
theorem eq_true_of_id {n : Bool} (h : (fun _ : Bool => true) n = (fun x : Bool => x) n) :
    n = true := h.symm

theorem sourceCommon : CommonEsseIsEssenceSource sourceProfile := by
  refine ⟨true, trivial, rfl, fun c hc => ?_, fun x _ hx => ?_⟩
  · exact Bool.noConfusion hc.2.2.2.2
  · cases x
    · exact Relation.TransGen.single ⟨by decide, trivial, trivial, rfl, rfl⟩
    · exact (hx rfl).elim

theorem selfCommon : CommonEsseIsEssenceSource selfProfile := by
  refine ⟨true, trivial, rfl, fun c hc => hc.1 hc.2.2.2, fun x _ hx => ?_⟩
  cases x
  · exact Relation.TransGen.single ⟨by decide, trivial, trivial, rfl⟩
  · exact (hx rfl).elim

theorem nonCausalGroundControl : NonCausalGroundControl := by
  refine ⟨oneWorld (fun _ => True) (fun _ => True) (fun y x => y = false ∧ x = true),
    sourceProfile, sourceCommon, fun _ _ => trivial, fun _ _ _ => ⟨trivial, trivial⟩,
    fun x h => Bool.noConfusion (h.1.symm.trans h.2), ?_, ?_⟩
  · intro hGround
    exact Bool.noConfusion (hGround false true ⟨trivial, trivial, rfl, rfl⟩ trivial rfl).1
  · intro ⟨n, hr, _, hId, _⟩
    have hn : n = true := eq_true_of_id hId
    subst hn
    exact hr.2 false ⟨trivial, trivial, rfl, rfl⟩

theorem absentSourceControl : AbsentSourceControl := by
  refine ⟨oneWorld (fun _ => True) (fun x => x = false) (fun _ _ => False),
    sourceProfile, sourceCommon, fun _ _ => trivial, fun _ _ h => h.2.2.elim,
    fun x h => Bool.noConfusion (h.1.symm.trans h.2), ?_, ?_⟩
  · intro hConcrete
    exact Bool.noConfusion (hConcrete true trivial rfl).2
  · intro ⟨n, hr, _, hId, _⟩
    have hn : n = true := eq_true_of_id hId
    subst hn
    exact Bool.noConfusion hr.1.2

theorem selfGroundControl : SelfGroundControl := by
  refine ⟨oneWorld (fun _ => True) (fun _ => True) (fun y x => y = true ∧ x = true),
    selfProfile, selfCommon, fun _ _ => trivial, fun _ _ _ => ⟨trivial, trivial⟩,
    fun _ _ h _ _ => h.2.2.1, ?_, ?_⟩
  · intro hNoSelf
    exact hNoSelf true rfl
  · intro ⟨n, hr, _, hId, _⟩
    have hn : n = true := eq_true_of_id hId
    subst hn
    exact hr.2 true ⟨trivial, trivial, rfl, rfl⟩

/-- The nonvacuity grounding profile: `true` grounds `false`. -/
def groundsProfile : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Bool :=
  oneWorld (fun _ => True) (fun _ => True) (fun y x => y = true ∧ x = false)

theorem source_acc {r : Bool → Bool → Prop} (h : ∀ c x, r c x → c = true ∧ x = false) :
    WellFounded r := by
  have hTrue : Acc r true := Acc.intro true (fun c hc => Bool.noConfusion (h c true hc).2)
  refine ⟨fun x => ?_⟩
  cases x
  · exact Acc.intro false (fun c hc => by rw [(h c false hc).1]; exact hTrue)
  · exact hTrue

theorem rootInterfaceNonvacuity : RootInterfaceNonvacuity := by
  have hRoot : ∀ x, ActualRoot groundsProfile () x → x = true := by
    intro x hx
    cases x
    · exact (hx.2 true ⟨trivial, trivial, rfl, rfl⟩).elim
    · rfl
  have hFirst : DeEnteFirstSourceIsActualRootAt groundsProfile () sourceProfile :=
    deEnteFirstSourceIsActualRoot groundsProfile () sourceProfile sourceCommon
      (fun _ _ => trivial) (fun _ _ _ => ⟨trivial, trivial⟩)
      (fun _ _ h _ hId => Bool.noConfusion (h.2.2.2.symm.trans (eq_true_of_id hId)))
      (fun x h => Bool.noConfusion (h.1.symm.trans h.2))
  have hAtMost : AtMostOneActualRootAt groundsProfile () :=
    fun x y hx hy => (hRoot x hx).trans (hRoot y hy).symm
  refine ⟨groundsProfile, sourceProfile, fun _ _ => True, sourceCommon,
    fun _ _ => trivial, fun _ _ _ => ⟨trivial, trivial⟩,
    fun _ _ h _ hId => Bool.noConfusion (h.2.2.2.symm.trans (eq_true_of_id hId)),
    fun x h => Bool.noConfusion (h.1.symm.trans h.2), hFirst, hAtMost,
    uniqueActualRootFromDeEnteSource groundsProfile () sourceProfile hFirst hAtMost,
    source_acc (fun _ _ h => h.1.2.2.2), fun _ _ _ _ => trivial,
    source_acc (fun _ _ h => h.2.2.2)⟩

theorem rootInterfaceControls : RootInterfaceControls :=
  ⟨perAccidensRegressControl, nonCausalGroundControl, absentSourceControl,
    selfGroundControl, rootInterfaceNonvacuity⟩

end Controls

end TruthCore.Results.Aquinas.DeEnte.RootInterface
