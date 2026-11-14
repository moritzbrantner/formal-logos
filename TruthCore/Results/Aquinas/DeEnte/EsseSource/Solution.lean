module

public import TruthCore.Latin.Aquinas.DeEnte.EsseSource
public import TruthCore.Causality.RootPurity

/-!
# De ente: one first being whose esse is its essence (#1628)

Conditional derivations for the three stages of *De ente* c.3 [69874]
(Baur/Koch numbering; Leonine c.4) and their reconnection to the root routes.

* `atMostOneEsseIsEssenceFromPlurification`: the multiplication inventory, the
  exclusion of an added difference and of matter, the existing esse-reception
  premises and the OPEN shared-nature premise give at most one actual being
  whose esse is its essence.
* `distinctEsseHasEsseIsEssenceSource`: the #1629 step (another actual cause of
  being, mode unspecified), no infinite regress of actual causes of being and
  excluded middle give every actual distinct esse a chain of actual causes of
  being headed by a being whose esse is its essence.
* `commonEsseIsEssenceSource`: with at most one such being, two actual beings
  and no infinite regress, one and the same being whose esse is its essence
  has no actual cause of its esse and heads a chain to every other actual
  being. Distinct represented esse and essence (a real distinction only if
  equality of represented principles is read as real identity) for every
  other being is derived here from at-most-one, as in the passage's order.
* `rootPurityFromDeEnte`: sibling of the root-purity route in which the #1629
  step replaces the q.3 a.4 efficient-read dichotomy pair.
* `atMostOneActualRootFromDeEnte`: any two actual concrete roots are the same,
  from the #1629 step and at-most-one (the uniqueness half of the
  root-uniqueness route, in place of its genus principle and grades).

Nothing here supplies efficiency, conservation, necessity or God
identification.
-/

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.EsseSource

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.EsseReception
  (EsseReceivedOnlyInOwnEssence NothingInReceptivePotencyToItself)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

/-- Stage (b): at most one actual being has its esse identical with its
essence. -/
theorem atMostOneEsseIsEssenceFromPlurification (p : Profile B P R) (q : Plurification B)
    (EsseReceivedIn : B → P → Prop) (ReceptivePotencyTo : P → P → Prop)
    (hModes : PlurificationOnlyByThreeModesReading p q EsseReceivedIn)
    (hShare : EsseIsEssenceBeingsShareNature p q)
    (hDiff : EsseTantumReceivesNoDifferenceReading p q)
    (hMatter : EsseTantumNotInMatterReading p q)
    (hOwn : EsseReceivedOnlyInOwnEssence p.essenceOf EsseReceivedIn)
    (hPotency : ReceiverInPotencyToReceivedEsseReading p.esseOf EsseReceivedIn ReceptivePotencyTo)
    (hNotSelf : NothingInReceptivePotencyToItself ReceptivePotencyTo) :
    AtMostOneEsseIsEssence p := by
  have hUnreceived : ∀ z, p.esseOf z = p.essenceOf z → ¬ ∃ r, EsseReceivedIn z r := by
    intro z hz ⟨r, hr⟩
    have hp := hPotency z r hr
    rw [hOwn z r hr, ← hz] at hp
    exact hNotSelf _ hp
  intro x y hx hy hxe hye
  exact hModes x y hx hy hxe hye (hShare x y hx hy hxe hye)
    (fun h => h.elim (hDiff x hxe) (hDiff y hye))
    (fun h => h.elim (hMatter x hxe) (hMatter y hye))
    (fun h => h.elim (hUnreceived x hxe) (hUnreceived y hye))

/-- Stage (c): every actual distinct esse goes back, through actual causes of
being, to an actual being whose esse is its essence. -/
theorem distinctEsseHasEsseIsEssenceSource (p : Profile B P R)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hRegress : NoInfiniteActualEsseCauseRegress p) (hEM : ExcludedMiddle) :
    EveryDistinctEsseHasEsseIsEssenceSource p := by
  intro x
  induction x using hRegress.induction with
  | _ x ih =>
    intro hx
    obtain ⟨c, hcx, hc, hCause⟩ := hOther x hx
    have hStep : ActualEsseCause p c x := ⟨hcx, hc, hx.1, hCause⟩
    rcases hEM (p.esseOf c = p.essenceOf c) with hId | hDistinct
    · exact ⟨c, hc, hId, Relation.TransGen.single hStep⟩
    · obtain ⟨n, hn, hnId, hChain⟩ := ih c hStep ⟨hc, hDistinct⟩
      exact ⟨n, hn, hnId, Relation.TransGen.tail hChain hStep⟩

/-- A well-founded relation has no cycle through its transitive closure. -/
theorem not_transGen_self {α : Type} {r : α → α → Prop} (hWF : WellFounded r) (a : α) :
    ¬ Relation.TransGen r a a := by
  have hAcc : Acc (Relation.TransGen r) a := (hWF.apply a).transGen
  induction hAcc with
  | intro x _ ih => exact fun h => ih x h h

/-- Stages (a)-(c) together: one being whose esse is its essence has no
actual cause of its esse and heads a chain of actual causes of being to every
other actual being. -/
theorem commonEsseIsEssenceSource (p : Profile B P R)
    (hSource : EveryDistinctEsseHasEsseIsEssenceSource p)
    (hOne : AtMostOneEsseIsEssence p) (hTwo : TwoActualBeings p)
    (hRegress : NoInfiniteActualEsseCauseRegress p)
    (hEM : ExcludedMiddle) : CommonEsseIsEssenceSource p := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hTwo
  -- One of two different actual beings has distinct represented esse, by
  -- at-most-one.
  have hSome : ∃ z, DistinctEsseAt p z := by
    rcases hEM (p.esseOf x = p.essenceOf x) with hxe | hxd
    · exact ⟨y, hy, fun hye => hxy (hOne x y hx hy hxe hye)⟩
    · exact ⟨x, hx, hxd⟩
  obtain ⟨z, hz⟩ := hSome
  obtain ⟨n, hn, hnId, _⟩ := hSource z hz
  -- Every actual being other than n has distinct esse and descends from n.
  have hAll : ∀ u, p.InAct u p.esse → u ≠ n → Relation.TransGen (ActualEsseCause p) n u := by
    intro u hu hun
    have hud : DistinctEsseAt p u := ⟨hu, fun hue => hun (hOne u n hu hn hue hnId)⟩
    obtain ⟨n', hn', hn'Id, hChain⟩ := hSource u hud
    have hEq : n' = n := hOne n' n hn' hn hn'Id hnId
    exact hEq ▸ hChain
  refine ⟨n, hn, hnId, fun c hc => ?_, hAll⟩
  -- An actual cause of n would close a cycle n → … → c → n.
  exact not_transGen_self hRegress n
    (Relation.TransGen.tail (hAll c hc.2.1 hc.1) hc)

section Root
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.RootPurity
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Every actual root has its represented esse equal to its essence, from the
#1629 other-cause step (in place of the q.3 a.4 dichotomy pair). -/
theorem identityOfActualRootFromOtherCause {W : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (n : B) (hr : ActualRoot m w n) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p) :
    p.esseOf n = p.essenceOf n := by
  rcases hEM (p.esseOf n = p.essenceOf n) with h | h
  · exact h
  · obtain ⟨c, hc, _, hCause⟩ := hOther n ⟨hExisting n hr.1.2, h⟩
    exact (hr.2 c (hEsse c n hc hr.1 hCause)).elim

/-- Stage (d), uniqueness: any two actual concrete roots are the same, from the
#1629 step and at-most-one, in place of the genus principle and grades of the
root-uniqueness route. -/
theorem atMostOneActualRootFromDeEnte {W : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hOne : AtMostOneEsseIsEssence p) : AtMostOneActualRootAt m w := by
  intro x y hx hy
  exact hOne x y (hExisting x hx.1.2) (hExisting y hy.1.2)
    (identityOfActualRootFromOtherCause m w p x hx hEM hExisting hEsse hOther)
    (identityOfActualRootFromOtherCause m w p y hy hEM hExisting hEsse hOther)

/-- Stage (d), purity: the root-purity route with the #1629 step in place of
the q.3 a.4 dichotomy pair. -/
theorem rootPurityFromDeEnte {W D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hOther : DistinctEsseHasOtherActualCause p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hComponent : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hBridge : UnlimitedDeterminationsArePure Composite PriorSimply p.essenceOf p.esseOf Has Pure) :
    ActualRootDeterminationsArePure m w Has Pure := by
  intro n hr
  apply hBridge n
  have hIdentity := identityOfActualRootFromOtherCause m w p n hr hEM hExisting hEsse hOther
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  intro hLimited
  rcases hLimited with hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩
  · obtain ⟨part, hPart, hDistinct⟩ := hComponent n hComposite
    exact hDistinct (hFirst part (hPosterior part n hPart))
  · exact hDistinctEsse hIdentity
  · exact hDistinct (hFirst y hPriorY)

end Root

/-! ## Controls -/

section Controls

/-- The infinite-regress interpretation. -/
def regressProfile : Profile Nat Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c = x + 1
  essenceOf := fun _ => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

theorem infiniteRegressControl : InfiniteRegressControl := by
  refine ⟨regressProfile, fun x _ => ⟨x + 1, Nat.succ_ne_self x, trivial, rfl⟩,
    ⟨trivial, Bool.noConfusion⟩, ?_, ?_⟩
  · intro hWF
    have hNoAcc : ∀ n, Acc (ActualEsseCause regressProfile) n → False := by
      intro n hAcc
      induction hAcc with
      | intro x _ ih => exact ih (x + 1) ⟨Nat.succ_ne_self x, trivial, trivial, rfl⟩
    exact hNoAcc 0 (hWF.apply 0)
  · intro h
    obtain ⟨_, _, hId, _⟩ := h 0 ⟨trivial, Bool.noConfusion⟩
    exact Bool.noConfusion hId

/-- The uncaused-distinct-esse interpretation. -/
def uncausedProfile : Profile Bool Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun _ _ _ => False
  essenceOf := fun _ => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

theorem uncausedDistinctEsseControl : UncausedDistinctEsseControl := by
  refine ⟨uncausedProfile, ⟨trivial, Bool.noConfusion⟩,
    ⟨fun a => Acc.intro a (fun _ h => h.2.2.2.elim)⟩, ?_, ?_⟩
  · intro h
    obtain ⟨_, _, _, hc⟩ := h false ⟨trivial, Bool.noConfusion⟩
    exact hc
  · intro h
    obtain ⟨_, _, hId, _⟩ := h false ⟨trivial, Bool.noConfusion⟩
    exact Bool.noConfusion hId

open Four

/-- `a` and `b` have esse equal to essence; `a` causes `c`, `b` causes `d`. -/
def twoProfile : Profile Four Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun s x _ => (s = a ∧ x = c) ∨ (s = b ∧ x = d)
  essenceOf := fun x => match x with
    | a => true | b => true | c => false | d => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- No `ActualEsseCause` edge ends at a first being of `twoProfile`. -/
theorem two_noCauseOf_a (s : Four) : ¬ ActualEsseCause twoProfile s a := by
  intro ⟨_, _, _, h⟩
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact Four.noConfusion h

theorem two_noCauseOf_b (s : Four) : ¬ ActualEsseCause twoProfile s b := by
  intro ⟨_, _, _, h⟩
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact Four.noConfusion h

theorem two_acc : ∀ x, Acc (ActualEsseCause twoProfile) x := by
  have hA : Acc (ActualEsseCause twoProfile) a :=
    Acc.intro a (fun s h => (two_noCauseOf_a s h).elim)
  have hB : Acc (ActualEsseCause twoProfile) b :=
    Acc.intro b (fun s h => (two_noCauseOf_b s h).elim)
  intro x
  cases x with
  | a => exact hA
  | b => exact hB
  | c =>
    refine Acc.intro c (fun s h => ?_)
    rcases h.2.2.2 with ⟨hs, _⟩ | ⟨_, hx⟩
    · subst hs; exact hA
    · exact Four.noConfusion hx
  | d =>
    refine Acc.intro d (fun s h => ?_)
    rcases h.2.2.2 with ⟨_, hx⟩ | ⟨hs, _⟩
    · exact Four.noConfusion hx
    · subst hs; exact hB

theorem two_last {r : Four → Four → Prop} {n x : Four} (h : Relation.TransGen r n x) :
    ∃ s, r s x := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

theorem twoSourcesControl : TwoSourcesControl := by
  refine ⟨twoProfile, ⟨fun _ _ => False, fun _ => False, fun _ => False⟩,
    fun _ _ => False, fun _ _ => False,
    fun _ _ _ _ _ _ h _ _ _ => h.elim, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h, ?_, ?_, ⟨two_acc⟩, ?_,
    ⟨a, b, Four.noConfusion, trivial, trivial⟩, ?_, ?_⟩
  · intro h
    exact h a b trivial trivial rfl rfl
  · intro x hx
    cases x with
    | a => exact (hx.2 rfl).elim
    | b => exact (hx.2 rfl).elim
    | c => exact ⟨a, Four.noConfusion, trivial, Or.inl ⟨rfl, rfl⟩⟩
    | d => exact ⟨b, Four.noConfusion, trivial, Or.inr ⟨rfl, rfl⟩⟩
  · intro x hx
    cases x with
    | a => exact (hx.2 rfl).elim
    | b => exact (hx.2 rfl).elim
    | c => exact ⟨a, trivial, rfl, Relation.TransGen.single
        ⟨Four.noConfusion, trivial, trivial, Or.inl ⟨rfl, rfl⟩⟩⟩
    | d => exact ⟨b, trivial, rfl, Relation.TransGen.single
        ⟨Four.noConfusion, trivial, trivial, Or.inr ⟨rfl, rfl⟩⟩⟩
  · intro h
    exact Four.noConfusion (h a b trivial trivial rfl rfl)
  · intro ⟨n, _, hId, _, hAll⟩
    cases n with
    | a =>
      obtain ⟨s, hs⟩ := two_last (hAll b trivial Four.noConfusion)
      exact two_noCauseOf_b s hs
    | b =>
      obtain ⟨s, hs⟩ := two_last (hAll a trivial Four.noConfusion)
      exact two_noCauseOf_a s hs
    | c => exact Bool.noConfusion hId
    | d => exact Bool.noConfusion hId

/-- `a` has esse equal to essence and causes the esse of every other being. -/
def oneProfile : Profile Four Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun s x _ => s = a ∧ x ≠ a
  essenceOf := fun x => match x with
    | a => true | b => false | c => false | d => false
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

theorem one_id (x : Four) (h : oneProfile.esseOf x = oneProfile.essenceOf x) : x = a := by
  cases x with
  | a => rfl
  | b => exact Bool.noConfusion h
  | c => exact Bool.noConfusion h
  | d => exact Bool.noConfusion h

/-- Some difference is added to every nature except that of `a`. -/
def oneDiff : Four → Prop
  | a => False
  | b => True
  | c => True
  | d => True

theorem one_noDiff (x : Four) (h : ¬ oneDiff x) : x = a := by
  cases x with
  | a => rfl
  | b => exact (h trivial).elim
  | c => exact (h trivial).elim
  | d => exact (h trivial).elim

theorem one_ne (x : Four) (hx : DistinctEsseAt oneProfile x) : x ≠ a := by
  intro h
  subst h
  exact hx.2 rfl

theorem one_acc : ∀ x, Acc (ActualEsseCause oneProfile) x := by
  have hA : Acc (ActualEsseCause oneProfile) a :=
    Acc.intro a (fun _ h => (h.2.2.2.2 rfl).elim)
  intro x
  exact Acc.intro x (fun s h => by rw [h.2.2.2.1]; exact hA)

theorem one_step (x : Four) (hx : x ≠ a) : ActualEsseCause oneProfile a x :=
  ⟨fun h => hx h.symm, trivial, trivial, ⟨rfl, hx⟩⟩

/-- In `oneProfile` the represented esse of every being other than `a` differs
from its essence. -/
theorem one_distinct (x : Four) (hx : x ≠ a) : DistinctEsseAt oneProfile x :=
  ⟨trivial, fun h => hx (one_id x h)⟩

theorem esseSourceNonvacuity : EsseSourceNonvacuity := by
  refine ⟨oneProfile, ⟨fun _ _ => True, oneDiff, fun _ => False⟩,
    fun x r => x ≠ a ∧ r = oneProfile.essenceOf x, fun r s => r ≠ s,
    ?_, fun _ _ _ _ _ _ => trivial, ?_, fun _ _ h => h,
    fun _ _ h => h.2, ?_, fun _ h => h rfl, ⟨b, false, Four.noConfusion, rfl⟩, ?_,
    ⟨one_acc⟩, ⟨a, b, Four.noConfusion, trivial, trivial⟩, ?_, ?_, ?_⟩
  · intro x y _ _ _ _ _ hDiff _ _
    exact (one_noDiff x (fun h => hDiff (Or.inl h))).trans
      (one_noDiff y (fun h => hDiff (Or.inr h))).symm
  · intro x hx hD
    have h := one_id x hx
    subst h
    exact hD
  · intro x r ⟨hx, hr⟩ hEq
    exact hx (one_id x (hEq.symm.trans hr))
  · intro x hx
    have hne := one_ne x hx
    exact ⟨a, fun h => hne h.symm, trivial, rfl, hne⟩
  · intro x y hx hy hxe hye
    exact (one_id x hxe).trans (one_id y hye).symm
  · intro x hx
    exact ⟨a, trivial, rfl, Relation.TransGen.single (one_step x (one_ne x hx))⟩
  · exact ⟨a, trivial, rfl, fun _ h => h.2.2.2.2 rfl,
      fun x _ hx => Relation.TransGen.single (one_step x hx)⟩

/-- All four controls. -/
theorem esseSourceControls : EsseSourceControls :=
  ⟨infiniteRegressControl, uncausedDistinctEsseControl, twoSourcesControl,
    esseSourceNonvacuity⟩

end Controls

end TruthCore.Results.Aquinas.DeEnte.EsseSource
