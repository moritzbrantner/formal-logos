module

public import TruthCore.Explanation.BruteContingencyParity
public import TruthCore.Results.Explanation.StoppingPoints.Solution

/-! Brute contingency and the parity of brute-existence demands: two further
support options for B2 on the shared frame, the contingent-only weakening of
the local existence PSR, the parity argument, and laws and models. Analyst
formulations; attribution deferred. -/

@[expose] public section

namespace TruthCore.Results.Explanation.BruteContingencyParity
open TruthCore.Explanation.BruteContingencyParity
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.FirstMoverNecessity (ContingentHasDistinctEsseCause
  ContingentHasDistinctEsse groundProfile)
open TruthCore.Causality.FirstMoverNecessity.Model (bruteFirst conserved allConcrete
  noneConcrete noGround xGroundsF mk fContingent noCause noPrior xCausesF xPriorF)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.GradedSupportFoundation (ActualGroundIsDistinctEsseCause)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Explanation.ExistencePSR (Model Reason ExistenceFact)
open TruthCore.Explanation.NoBruteExistence (NoBruteExistenceAt)
open TruthCore.Explanation.PSRStrength (Arena Access Contingent Explained
  IrreflexiveContingent basic everywhere ofModel)
open TruthCore.Explanation.PSRSelfApplication (Stance BruteAt Uniform Selective Restricted)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- B2 from reasons for existence: a being `x` contingent at `w` has some reason
`r` for its existence (local existence PSR for contingents); the being `r` is
about is not `x` (BX1); so it causes `x`'s esse (BX2), and it is a distinct
CAUSE_2 of `x`'s esse. -/
theorem esseCauseFromExistenceReasons {W B T R : Type} (F : CausalityFrame W B T R)
    (ex : W → Reason B → ExistenceFact B → Prop) (w : W)
    (hPSR : NoBruteContingentExistenceAt (reasonModel F ex) w)
    (hSelf : ContingentExistenceNotSelfExplained (reasonModel F ex) w)
    (hSource : ExistenceReasonSourceCausesEsse F (reasonModel F ex) w) :
    ContingentHasDistinctEsseCause F w := by
  intro x hx
  obtain ⟨r, hr⟩ := hPSR x hx
  have hne : source r ≠ x := hSelf x r hx hr
  exact ⟨source r, hne, hSource x r hx hr hne⟩

/-- B2 from the selected-grounding closure: a being `x` contingent at `w` is
concrete (interface), so the closure gives it an actual concrete ground `y`
at `w`; the existing ground-to-cause bridge makes `y` distinct from `x` and a
cause of its esse. -/
theorem esseCauseFromGroundingClosure {W B T R : Type} (F : CausalityFrame W B T R)
    (concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hConcrete : ContingentsConcrete F concrete w)
    (hClosure : EveryContingentGroundedAt (groundProfile F concrete grounds) w)
    (hBridge : ActualGroundIsDistinctEsseCause (groundProfile F concrete grounds) w
      F.CausesIn F.esse) :
    ContingentHasDistinctEsseCause F w := by
  intro x hx
  have hxc : concrete x := hConcrete x hx
  obtain ⟨y, hyc, hyw, hg⟩ := hClosure x hxc hx.1 hx
  obtain ⟨hne, hc⟩ := hBridge y x ⟨hyc, hyw⟩ ⟨hxc, hx.1⟩ hg
  exact ⟨y, hne, hc⟩

/-- The local existence PSR for all existents gives its contingent-only form:
a contingent being exists there. -/
theorem noBruteContingentOfNoBrute {W B : Type} (m : Model W B) (w : W)
    (h : NoBruteExistenceAt m w) : NoBruteContingentExistenceAt m w :=
  fun x hx => h x hx.1

/-- The parity argument: if the stance's ontic demand is uniform in `k`, it
requires a reason why `t` obtains, and `t` and `o` agree on `k`, then it
requires a reason why `o` obtains; meeting its demand, it cannot accept `o` as a
brute contingent truth. -/
theorem parity {W B F : Type} (S : WhyStance F) (k : F → Prop) (A : Arena W B F)
    (w : W) (t o : F)
    (hUniform : FeatureUniform S k) (hReq : RequiresWhyFor S t)
    (hShare : ShareFeature k t o) :
    ExcludesBruteRival S A w o := by
  rintro ⟨hHonors, hAccepts, hBrute⟩
  exact hBrute.2 (hHonors o (hUniform t o hShare hReq) hAccepts)

/-! ## Laws and models -/

theorem reason_forall {p : Reason Bool → Prop} :
    (∀ r, p r) ↔ p (.intrinsic false) ∧ p (.intrinsic true) ∧
      p (.circumstance false) ∧ p (.circumstance true) :=
  ⟨fun h => ⟨h _, h _, h _, h _⟩, fun ⟨a, b, c, d⟩ r => by
    rcases r with (_ | _) | (_ | _) <;> assumption⟩

theorem reason_exists {p : Reason Bool → Prop} :
    (∃ r, p r) ↔ p (.intrinsic false) ∨ p (.intrinsic true) ∨
      p (.circumstance false) ∨ p (.circumstance true) :=
  ⟨fun ⟨r, h⟩ => by rcases r with (_ | _) | (_ | _) <;> simp_all, fun h => by
    rcases h with h | h | h | h <;> exact ⟨_, h⟩⟩

theorem laws :
    (∀ (W B T R : Type) (F : CausalityFrame W B T R)
      (ex : W → Reason B → ExistenceFact B → Prop) (w : W),
      BruteContingentBeingAt F (reasonModel F ex) w →
        ¬ ContingentHasDistinctEsseCause F w ∧
        ¬ NoBruteContingentExistenceAt (reasonModel F ex) w ∧
        ¬ (ContingentExistenceNotSelfExplained (reasonModel F ex) w ∧
            ExistenceReasonSourceCausesEsse F (reasonModel F ex) w ∧
            NoBruteContingentExistenceAt (reasonModel F ex) w) ∧
        ∀ (concrete : B → Prop) (grounds : W → B → B → Prop),
          ¬ (ContingentsConcrete F concrete w ∧
            EveryContingentGroundedAt (groundProfile F concrete grounds) w ∧
            ActualGroundIsDistinctEsseCause (groundProfile F concrete grounds) w F.CausesIn
              F.esse)) ∧
    (∀ (W B : Type) (m : Model W B) (w : W) (x : B),
      ContingentExistenceNotSelfExplained m w → m.explains w (.intrinsic x) (.fact x) →
        ¬ ContingentAt m.ontic w x) ∧
    (∀ (W B T R P : Type) (F : CausalityFrame W B T R) (essenceOf esseOf : B → P) (w : W),
      ContingentExistenceNotSelfExplained (natureModel F essenceOf esseOf) w ↔
        ContingentHasDistinctEsse F w essenceOf esseOf) ∧
    (∀ (W B T R : Type) (F : CausalityFrame W B T R)
      (ex : W → Reason B → ExistenceFact B → Prop) (w : W) (x : B),
      BruteAt (ofModel (reasonModel F ex)) w (.inl (.fact x)) ↔
        ContingentAt F.history.ontic w x ∧ ¬ ∃ r, ex w r (.fact x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro W B T R F ex w ⟨x, hx, hNoCause, hNoReason⟩
    have hB2 : ¬ ContingentHasDistinctEsseCause F w := fun h => hNoCause (h x hx)
    refine ⟨hB2, fun h => hNoReason (h x hx), ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      exact hB2 (esseCauseFromExistenceReasons F ex w h3 h1 h2)
    · rintro concrete grounds ⟨h1, h2, h3⟩
      exact hB2 (esseCauseFromGroundingClosure F concrete grounds w h1 h2 h3)
  · intro W B m w x hSelf hr hx
    exact hSelf x (.intrinsic x) hx hr rfl
  · intro W B T R P F essenceOf esseOf w
    constructor
    · intro h x hx heq
      exact h x (.intrinsic x) hx ⟨rfl, fun hne => hne heq⟩ rfl
    · intro h x r hx hr
      cases r with
      | intrinsic z => exact (hr.2 (h x hx)).elim
      | circumstance y => exact hr.elim
  · intro W B T R F ex w x
    constructor
    · rintro ⟨⟨hx, v, hv, hnx⟩, hne⟩
      exact ⟨⟨hx, v, hv, hnx⟩, fun ⟨r, hr⟩ => hne ⟨.inr r, hr⟩⟩
    · rintro ⟨⟨hx, v, hv, hnx⟩, hne⟩
      refine ⟨⟨hx, v, hv, hnx⟩, ?_⟩
      rintro ⟨r, hr⟩
      cases r with
      | inl f => cases f; exact hr.elim
      | inr r => exact hne ⟨r, hr⟩

theorem models :
    -- 1
    (ContingentExistenceNotSelfExplained (reasonModel bruteFirst noReasons) true ∧
      ExistenceReasonSourceCausesEsse bruteFirst (reasonModel bruteFirst noReasons) true ∧
      ¬ NoBruteContingentExistenceAt (reasonModel bruteFirst noReasons) true ∧
      ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
      BruteContingentBeingAt bruteFirst (reasonModel bruteFirst noReasons) true ∧
      ContingentAt bruteFirst.history.ontic true true ∧
      BruteAt (ofModel (reasonModel bruteFirst noReasons)) true (.inl (.fact true))) ∧
    -- 2
    (NoBruteContingentExistenceAt (reasonModel bruteFirst selfNature) true ∧
      ExistenceReasonSourceCausesEsse bruteFirst (reasonModel bruteFirst selfNature) true ∧
      ¬ ContingentExistenceNotSelfExplained (reasonModel bruteFirst selfNature) true ∧
      ¬ ContingentHasDistinctEsseCause bruteFirst true ∧
      ContingentAt bruteFirst.history.ontic true true ∧
      selfNature true (.intrinsic true) (.fact true)) ∧
    -- 3
    (NoBruteContingentExistenceAt (reasonModel bruteFirst occasion) true ∧
      ContingentExistenceNotSelfExplained (reasonModel bruteFirst occasion) true ∧
      ¬ ExistenceReasonSourceCausesEsse bruteFirst (reasonModel bruteFirst occasion) true ∧
      ¬ ContingentHasDistinctEsseCause bruteFirst true) ∧
    -- 4
    (NoBruteContingentExistenceAt (reasonModel conserved occasion) true ∧
      ContingentExistenceNotSelfExplained (reasonModel conserved occasion) true ∧
      ExistenceReasonSourceCausesEsse conserved (reasonModel conserved occasion) true ∧
      ContingentHasDistinctEsseCause conserved true ∧
      ContingentAt conserved.history.ontic true true) ∧
    -- 5
    (ContingentHasDistinctEsseCause conserved true ∧
      ¬ NoBruteContingentExistenceAt (reasonModel conserved noReasons) true) ∧
    -- 6
    (ContingentHasDistinctEsseCause conserved true ∧
      ¬ ContingentExistenceNotSelfExplained (reasonModel conserved selfAndOccasion) true) ∧
    -- 7
    (ContingentsConcrete bruteFirst allConcrete true ∧
      ActualGroundIsDistinctEsseCause (groundProfile bruteFirst allConcrete noGround) true
        bruteFirst.CausesIn bruteFirst.esse ∧
      ¬ EveryContingentGroundedAt (groundProfile bruteFirst allConcrete noGround) true) ∧
    -- 8
    (ContingentsConcrete bruteFirst allConcrete true ∧
      EveryContingentGroundedAt (groundProfile bruteFirst allConcrete xGroundsF) true ∧
      ¬ ActualGroundIsDistinctEsseCause (groundProfile bruteFirst allConcrete xGroundsF) true
        bruteFirst.CausesIn bruteFirst.esse) ∧
    -- 9
    (EveryContingentGroundedAt (groundProfile bruteFirst noneConcrete noGround) true ∧
      ActualGroundIsDistinctEsseCause (groundProfile bruteFirst noneConcrete noGround) true
        bruteFirst.CausesIn bruteFirst.esse ∧
      ¬ ContingentsConcrete bruteFirst noneConcrete true) ∧
    -- 10
    (ContingentsConcrete conserved allConcrete true ∧
      EveryContingentGroundedAt (groundProfile conserved allConcrete xGroundsF) true ∧
      ActualGroundIsDistinctEsseCause (groundProfile conserved allConcrete xGroundsF) true
        conserved.CausesIn conserved.esse) := by
  simp only [ContingentExistenceNotSelfExplained, ExistenceReasonSourceCausesEsse,
    NoBruteContingentExistenceAt, ContingentHasDistinctEsseCause, BruteContingentBeingAt,
    ContingentsConcrete, EveryContingentGroundedAt, ActualGroundIsDistinctEsseCause,
    ActualConcrete, ContingentAt, BruteAt, Contingent, Explained, Access, ofModel,
    reasonModel, groundProfile, bruteFirst, conserved, mk, fContingent, noCause,
    xCausesF, allConcrete, noneConcrete, noGround, xGroundsF, noReasons,
    selfNature, occasion, selfAndOccasion, source, reason_forall, reason_exists]
  simp [Bool.forall_bool]

theorem b2SupportControls : B2SupportControls := by
  obtain ⟨l1, l2, l3, l4⟩ := laws
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := models
  exact ⟨fun W B T R F ex w => esseCauseFromExistenceReasons F ex w,
    fun W B T R F concrete grounds w => esseCauseFromGroundingClosure F concrete grounds w,
    fun W B m w => noBruteContingentOfNoBrute m w,
    l1, l2, l3, l4, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩

/-! ## The parity map -/

theorem pfact_forall {p : PFact → Prop} :
    (∀ f, p f) ↔ p .god ∧ p .base ∧ p .found ∧ p .atom ∧ p .star :=
  ⟨fun h => ⟨h _, h _, h _, h _, h _⟩, fun ⟨a, b, c, d, e⟩ f => by
    cases f <;> assumption⟩

theorem pfact_exists {p : PFact → Prop} :
    (∃ f, p f) ↔ p .god ∨ p .base ∨ p .found ∨ p .atom ∨ p .star :=
  ⟨fun ⟨f, h⟩ => by cases f <;> simp_all, fun h => by
    rcases h with h | h | h | h | h <;> exact ⟨_, h⟩⟩

theorem fork : ∀ (W B F : Type) (S : WhyStance F) (A : Arena W B F) (w : W) (t o : F)
    (k : F → Prop),
    S.requiresWhy t → WhyHonors S A w → S.accepts o → BruteAt A w o →
      ¬ Uniform (whyView S) t o ∧
      ((k t ↔ k o) → Selective (whyView S) k t o) ∧
      (¬ (k t ↔ k o) → Restricted (whyView S) k t o) := by
  intro W B F S A w t o k ht hHonors ho hBrute
  have hno : ¬ S.requiresWhy o := fun h => hBrute.2 (hHonors o h ho)
  exact ⟨fun ⟨_, h⟩ => hno h, fun hk => ⟨ht, hno, hk⟩, fun hk => ⟨ht, hno, hk⟩⟩

theorem necessitating : ∀ (W B F : Type) (S : WhyStance F) (A : Arena W B F) (w : W) (f : F),
    WhyHonorsNecessitating S A w → S.requiresWhy f → S.accepts f → Contingent A w f →
    (∀ r, A.explains w r f → ∀ v, Access A w v → A.holds v r) → False := by
  intro W B F S A w f hHonors hReq hAcc ⟨_, v, hv, hnot⟩ hNec
  obtain ⟨r, hr, hsuff⟩ := hHonors f hReq hAcc
  exact hnot (hsuff v hv (hNec r hr v hv))

/-- A reason structure with a self-reason is not well-founded. -/
theorem not_wellFounded_of_self {α : Type} {R : α → α → Prop} (a : α) (h : R a a) :
    ¬ WellFounded R := fun hwf =>
  hwf.induction (C := fun x => ¬ R x x) a (fun x ih hx => ih x hx hx) h

/-- Both sides alike: with factive, well-founded reasons, a truth at `a` leaves
some truth at `a` without a reason (the #746 second core, reused). -/
theorem wellFoundedLeavesUnexplained : ∀ (W B F : Type) (A : Arena W B F) (a : W) (t : F),
    A.holds a t → TruthCore.Explanation.PSRStrength.Factive A →
      WellFounded (A.explains a) → ¬ TruthCore.Explanation.PSRStrength.FactPSR A a :=
  fun _ _ _ A a t ht hf hwf hp =>
    TruthCore.Results.Explanation.StoppingPoints.core_unrestricted A a t ht hp hf hwf

/-- A scene reason relation is well-founded when the termini (God, the base)
have no reasons, the initial state has only termini as reasons, and the two
existents have only the initial state as reasons. Stated by layers, without
arithmetic. -/
theorem wf_scene {R : PFact → PFact → Prop}
    (hg : ∀ y, ¬ R y .god) (hb : ∀ y, ¬ R y .base)
    (hf : ∀ y, R y .found → y = .god ∨ y = .base)
    (ha : ∀ y, R y .atom → y = .found) (hs : ∀ y, R y .star → y = .found) :
    WellFounded R := by
  have ag : Acc R .god := ⟨_, fun y hy => (hg y hy).elim⟩
  have ab : Acc R .base := ⟨_, fun y hy => (hb y hy).elim⟩
  have af : Acc R .found := ⟨_, fun y hy => by
    rcases hf y hy with h | h <;> subst h <;> assumption⟩
  refine ⟨fun f => ?_⟩
  cases f with
  | god => exact ag
  | base => exact ab
  | found => exact af
  | atom => exact ⟨_, fun y hy => by rw [ha y hy]; exact af⟩
  | star => exact ⟨_, fun y hy => by rw [hs y hy]; exact af⟩

/-- Unfold the scene and decide it by cases. -/
local macro "scene" : tactic => `(tactic| (
  simp only [ShareFeature, PositedWithoutReason, atheistReading, theistReading, naturalist,
    manyBrute, bruteBase, natureBase, bruteGod, theist, contingentGod, picture, contingentRow,
    pnone, basic, everywhere, ptbl, Explained, HoldsBruteRival, WhyHonors,
    WhyHonorsNecessitating, RequiresWhyFor, FeatureUniform, Selective, Restricted, whyView,
    idle, existence, godOnly, evidential, symmetric, uniformRejector, baseNaturalist,
    theistStance, contingentOnlyTheist, wstance, natAccepts, natCore, BruteAt, Contingent,
    Access, IrreflexiveContingent, ofModel, reasonModel, bruteFirst, mk, fContingent,
    noReasons, UnexplainedAre, UnnecessitatedAre, observation,
    TruthCore.Explanation.PSRStrength.Factive,
    TruthCore.Explanation.PSRSelfApplication.Supported,
    TruthCore.Explanation.PSRSelfApplication.Honors,
    TruthCore.Explanation.PSRSelfApplication.demandNorm,
    TruthCore.Logic.SelfApplication.Norm.Holds, pfact_forall, pfact_exists] <;>
  simp [Bool.forall_bool, reason_exists]))

theorem parityMap : ParityMap := by
  refine ⟨fork, necessitating, wellFoundedLeavesUnexplained,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wf_scene ?_ ?_ ?_ ?_ ?_,
      ?_, wf_scene ?_ ?_ ?_ ?_ ?_,
      ?_, wf_scene ?_ ?_ ?_ ?_ ?_,
      ?_, wf_scene ?_ ?_ ?_ ?_ ?_,
      ?_, not_wellFounded_of_self PFact.base ?_, ?_,
      ?_, not_wellFounded_of_self PFact.god ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> scene

end TruthCore.Results.Explanation.BruteContingencyParity
