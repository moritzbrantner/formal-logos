module

public import TruthCore.Modal.MirrorCollapse
public import TruthCore.Results.Modal.SimplicityCollapse.Solution
public import TruthCore.Results.Causality.RootPerfectionIntellect.Solution

/-! # The relation-of-reason account and the mirror-world rule: proofs (#2145, lane M)

See `TruthCore.Modal.MirrorCollapse` and `docs/notes/simplicity-collapse-555.md`,
section "The relation-of-reason account and the mirror-world rule". -/

@[expose] public section

namespace TruthCore.Results.Modal.MirrorCollapse

open TruthCore.Modal.MirrorCollapse
open TruthCore.Modal.MirrorCollapse.Control
open TruthCore.German.Kant.CosmologicalInference (Ontic ContingentAt)
open TruthCore.Modal.SelectedEffectBridge (OutputProfile SameActEverywhere)
open TruthCore.Modal.ModalGrounding (EssentialTruth)
open TruthCore.Modal.SimplicityCollapse (StrictEfficacy)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ContingentBeingNode (RouteCollapsedAt RouteNotCollapsedAt
  SomeActualContingentAt)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple
  UnlimitedDeterminationsArePure)
open TruthCore.Causality.RootPerfectionIntellect (ExclusionFreeAdmissible
  AdmissibleIsExclusionFree PureRequiresNoPureLack ExclusionFree)
open TruthCore.Explanation.BruteContingencyParity (NoBruteContingentExistenceAt)
open TruthCore.Causality.SourceIntellectControls.ProfileControls (Determination)

/-! ## B. The mirror argument -/

/-- Lean-only. Under actual collapse, a world violating no essential truth is
accessible (essence-grounded possibility) and therefore agrees with `w` on the
predicate "is `w`". -/
theorem collapseIdentifiesUnexcluded {W B : Type} (o : Ontic W B) (w : W)
    (E : B → (W → Prop) → Prop) (hMC : RouteCollapsedAt o w)
    (hEM : EssenceGroundedWorldPossibility o w E) (v : W)
    (hv : ∀ x φ, EssentialTruth E x φ → φ v) : v = w :=
  hMC (fun u => u = w) trivial rfl v (hEM v hv)

/-- Lean-only (full-collapse form). If every world violating no essential truth is possible,
the actual world satisfies every essential truth, the mirror image satisfies every
essential truth the actual world does, and the mirror reverses handedness, then
actual modal collapse fails: the mirror image is accessible and handedness differs
there. -/
theorem notCollapsedFromMirror {W B : Type} (o : Ontic W B) (w : W)
    (Essential : B → (W → Prop) → Prop) (σ : W → W) (H : W → Prop)
    (hEM : EssenceGroundedWorldPossibility o w Essential)
    (hFact : EssentialTruthsHoldAt Essential w)
    (hPres : EssentialTruthsPreservedByMirrorAt Essential σ w)
    (hRev : HandednessReversedAt σ H w) :
    RouteNotCollapsedAt o w := by
  intro hMC
  have hAcc : o.frame.access w (σ w) := hEM _ fun x φ h => hPres x φ h (hFact x φ h)
  have hSame : H (σ w) ↔ H w := hMC (fun u => H u ↔ H w) trivial Iff.rfl (σ w) hAcc
  have hContra : H w ↔ ¬ H w := hSame.symm.trans hRev
  exact (iff_not_self hContra)

/-- The chiral mirror argument. With the four premises of `notCollapsedFromMirror`
the mirror image is accessible and has the opposite handedness; an actual
concrete being that exists only at worlds sharing the actual handedness is absent
there, so it is contingent. -/
theorem contingentFromChiralMirror {W B : Type} (m : Profile W B) (w : W)
    (Essential : B → (W → Prop) → Prop) (σ : W → W) (H : W → Prop)
    (hEM : EssenceGroundedWorldPossibility m.ontic w Essential)
    (hFact : EssentialTruthsHoldAt Essential w)
    (hPres : EssentialTruthsPreservedByMirrorAt Essential σ w)
    (hRev : HandednessReversedAt σ H w)
    (hChiral : ChiralIndividualAt m w H) :
    SomeActualContingentAt m w := by
  obtain ⟨x, hx, hxw, hOnly⟩ := hChiral
  have hAcc : m.ontic.frame.access w (σ w) := hEM _ fun y φ h => hPres y φ h (hFact y φ h)
  refine ⟨x, hx, hxw, σ w, hAcc, fun hxσ => ?_⟩
  exact iff_not_self ((hOnly (σ w) hxσ).symm.trans hRev)

/-- Lean-only. Under invariance, an intrinsic fact has the same value at every
accessible world as at `w`. -/
theorem intrinsicConstant {W B D : Type} (o : Ontic W B) (Has : W → B → D → Prop) (w : W)
    (g : B) (hInv : IntrinsicProfileInvariant o Has w g) (e : W → Prop)
    (he : IntrinsicTo o Has w g e) (v : W) (hv : o.frame.access w v) : e v ↔ e w :=
  he v hv (hInv v hv)

/-- The mirror fork. -/
theorem mirrorFork : MirrorForkCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B o w E hMC hEM v hv
    exact collapseIdentifiesUnexcluded o w E hMC hEM v hv
  · intro W B o w E σ H hMC hEM hFact hRev
    by_contra hNo
    have hPres : EssentialTruthsPreservedByMirrorAt E σ w := by
      intro x φ h hw
      by_contra hn
      exact hNo ⟨x, φ, h, hw, hn⟩
    exact notCollapsedFromMirror o w E σ H hEM hFact hPres hRev hMC
  · intro W B o w E σ H hMC hFact hPres hRev
    refine ⟨fun hAcc => ?_, fun x φ h => hPres x φ h (hFact x φ h)⟩
    have hSame : H (σ w) ↔ H w := hMC (fun u => H u ↔ H w) trivial Iff.rfl (σ w) hAcc
    exact iff_not_self (hSame.symm.trans hRev)
  · intro W B o w E σ hMC hEM hFact hPres
    have hEq : σ w = w :=
      collapseIdentifiesUnexcluded o w E hMC hEM (σ w) fun x φ h => hPres x φ h (hFact x φ h)
    refine ⟨hEq, fun H hRev => ?_⟩
    unfold HandednessReversedAt at hRev
    rw [hEq] at hRev
    exact iff_not_self hRev
  · intro W B w E σ H ρ ⟨hρ, hOnly⟩ hUnex hRev
    refine ⟨hρ, fun hρσ => ?_⟩
    have hEq : σ w = w := hOnly (σ w) hUnex hρσ
    unfold HandednessReversedAt at hRev
    rw [hEq] at hRev
    exact iff_not_self hRev
  · intro W B D o Has w g σ hInv hAcc Ex e hEx hNot he ⟨hew, hdisc⟩
    exact hdisc (σ w) hAcc hNot ((intrinsicConstant o Has w g hInv e he (σ w) hAcc).2 hew)
  · intro W B D P m w Admissible RequiresLack Has Pure Composite Prior essence esse left right
      hRoots hPurity hSuff hPure hEx hPar r hr
    have hNone : ¬ (Pure left ∧ Pure right) := by
      rintro ⟨hl, hrt⟩
      have hAdm : Admissible {left, right} :=
        TruthCore.Results.Causality.RootPerfectionIntellect.allPureAdmissible Admissible
          RequiresLack Pure hSuff hPure _ fun d hd => by
            rcases hd with rfl | hd
            · exact hl
            · rw [Set.mem_singleton_iff.1 hd]; exact hrt
      exact hEx _ hAdm (by simp) (by simp)
    refine ⟨fun hl => ?_, fun hrt => ?_⟩
    · have hPl : Pure left := hPurity r (hRoots r hr) _ hl
      exact hNone ⟨hPl, hPar.1 hPl⟩
    · have hPr : Pure right := hPurity r (hRoots r hr) _ hrt
      exact hNone ⟨hPar.2 hPr, hPr⟩
  · intro W B m w E σ H hNec hFact hPres hRev hChiral hEM
    obtain ⟨x, hx, hxw, v, hv, hnv⟩ :=
      contingentFromChiralMirror m w E σ H hEM hFact hPres hRev hChiral
    exact hnv (hNec x hx hxw v hv)

/-! ## Mirror controls -/

theorem mirror_reversed : HandednessReversedAt not handed true := by
  simp [HandednessReversedAt, handed]

theorem id_notReversed : ¬ HandednessReversedAt id handed true := by
  simp [HandednessReversedAt, handed]

theorem emUniv {E : Unit → (Bool → Prop) → Prop} :
    EssenceGroundedWorldPossibility (cProfile univAccess).ontic true E :=
  fun _ _ => trivial

theorem emOriented :
    EssenceGroundedWorldPossibility (cProfile onlyActual).ontic true orientedEss :=
  fun v hv => hv () (fun v => v = true) rfl

theorem factOriented : EssentialTruthsHoldAt orientedEss true := by
  intro x φ h
  change φ = _ at h
  subst h
  rfl

theorem notPresOriented : ¬ EssentialTruthsPreservedByMirrorAt orientedEss not true := by
  intro h
  have := h () (fun v => v = true) rfl rfl
  cases this

theorem presNoEss {σ : Bool → Bool} : EssentialTruthsPreservedByMirrorAt noEss σ true :=
  fun _ _ h => h.elim

theorem factNoEss : EssentialTruthsHoldAt noEss true := fun _ _ h => h.elim

theorem emAbsurd : EssenceGroundedWorldPossibility (cProfile onlyActual).ontic true absurdEss := by
  intro v hv
  exact (hv () (fun _ => False) rfl).elim

theorem notFactAbsurd : ¬ EssentialTruthsHoldAt absurdEss true :=
  fun h => h () (fun _ => False) rfl

theorem presAbsurd : EssentialTruthsPreservedByMirrorAt absurdEss not true := by
  intro x φ h hw
  change φ = _ at h
  subst h
  exact hw.elim

theorem chiral {acc : Bool → Bool → Prop} : ChiralIndividualAt (cProfile acc) true handed :=
  ⟨(), trivial, rfl, fun v hv => by
    change v = true at hv
    subst hv
    exact Iff.rfl⟩

theorem univ_contingent : SomeActualContingentAt (cProfile univAccess) true :=
  ⟨(), trivial, rfl, false, trivial, by simp [cProfile]⟩

theorem onlyActual_notContingent : ¬ SomeActualContingentAt (cProfile onlyActual) true := by
  rintro ⟨_, -, -, v, hv, hnv⟩
  exact hnv hv

theorem mirror3_reversed : HandednessReversedAt (Option.map not) handed3 (some true) := by
  simp [HandednessReversedAt, handed3]

/-- The controls of the chiral mirror argument. -/
theorem mirrorControls : MirrorControls := by
  refine ⟨⟨emUniv, factNoEss, presNoEss, mirror_reversed, chiral, univ_contingent⟩,
    ⟨emOriented, factOriented, notPresOriented, mirror_reversed, chiral,
      onlyActual_notContingent⟩,
    ⟨fun h => ?_, factNoEss, presNoEss, mirror_reversed, chiral, onlyActual_notContingent⟩,
    ⟨emOriented, factOriented, fun x φ h hw => by simpa using hw, id_notReversed, chiral,
      onlyActual_notContingent⟩,
    ⟨emAbsurd, notFactAbsurd, presAbsurd, mirror_reversed, chiral, onlyActual_notContingent⟩,
    ⟨fun _ _ => trivial, factNoEss, presNoEss, mirror_reversed, ?_, ?_⟩,
    ⟨emUniv, factOriented, notPresOriented, mirror_reversed, chiral, univ_contingent⟩,
    ⟨fun h => ?_, fun _ _ h => h.elim, fun _ _ h => h.elim, mirror3_reversed, ?_, ?_⟩,
    ⟨emUniv, factNoEss, presNoEss, id_notReversed, chiral, univ_contingent⟩,
    ⟨emUniv, notFactAbsurd, presAbsurd, mirror_reversed, chiral, univ_contingent⟩,
    ⟨fun _ _ => trivial, fun _ _ h => h.elim, fun _ _ h => h.elim, mirror3_reversed, ?_, ?_⟩⟩
  · have := h false (fun _ _ hx => hx.elim)
    cases this
  · rintro ⟨_, -, -, hall⟩
    have := (hall false trivial).2 (rfl : handed true)
    cases this
  · rintro ⟨_, -, -, v, -, hnv⟩
    exact hnv trivial
  · exact absurd (h none (fun _ _ hx => hx.elim)) (by simp [threeProfile])
  · refine ⟨(), trivial, rfl, fun v hv => ?_⟩
    change v = some true at hv
    subst hv
    exact Iff.rfl
  · exact ⟨(), trivial, rfl, some false, by simp [threeProfile], by simp [threeProfile]⟩
  · rintro ⟨_, -, -, hall⟩
    have := (hall none (by simp [threeUnivProfile])).2 rfl
    simp [handed3] at this
  · exact ⟨(), trivial, by simp [threeUnivProfile], some false, trivial,
      by simp [threeUnivProfile]⟩

/-! ## A. The relation-of-reason account -/

/-- Lean-only. The cost of the relation-of-reason account. -/
theorem relationOfReasonCost {W B A D : Type} (p : OutputProfile W B A)
    (Has : W → B → D → Prop) (w : W) (a : A) (x : B) (h : RelationOfReasonAt p Has w a x) :
    SameActEverywhere p w a ∧ ¬ StrictEfficacy p w a x ∧
    (∀ e, IntrinsicTo p.ontic Has w p.source e →
      ¬ Discriminates p.ontic w (fun v => p.ontic.ExistsAt v x) e) ∧
    Discriminates p.ontic w (fun v => p.ontic.ExistsAt v x) (fun v => p.output v a x) ∧
    ¬ IntrinsicTo p.ontic Has w p.source (fun v => p.output v a x) := by
  obtain ⟨hInv, ⟨d, hd, hCarry⟩, hOut, hSound, hCont⟩ := h
  have hSame : SameActEverywhere p w a := fun v hv => hCarry v hv ((hInv v hv d).2 hd)
  obtain ⟨-, v, hv, hnx⟩ := hCont
  refine ⟨hSame, fun hS => ?_, fun e he ⟨hew, hdisc⟩ => ?_,
    ⟨hOut, fun u hu hnu ho => hnu (hSound u hu ho)⟩, fun hI => ?_⟩
  · exact hnx (hS v hv (hSame v hv))
  · exact hdisc v hv hnx ((he v hv (hInv v hv)).2 hew)
  · exact hnx (hSound v hv ((hI v hv (hInv v hv)).2 hOut))

theorem rr_actualRoot (r : Bool) : ActualRoot rrProfile true r ↔ r = true := by
  constructor
  · rintro ⟨-, hNo⟩
    cases r
    · exact absurd (hNo true) (by
        simp [TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround, rrProfile,
          rrOntic])
    · rfl
  · rintro rfl
    refine ⟨⟨trivial, Or.inl rfl⟩, ?_⟩
    rintro y ⟨-, -, hg⟩
    simp [rrProfile] at hg

theorem rr_contingent : ContingentAt rrOntic true false := by
  refine ⟨Or.inr rfl, false, trivial, ?_⟩
  simp [rrOntic]

/-- Lean-only. Under N for `g`, an exclusive real decree family leaves `g` at
every accessible world either its actual decree or none. -/
theorem decreesUnderN {W B D X : Type} (o : Ontic W B) (Has : W → B → D → Prop) (w : W) (g : B)
    (dec : X → D) (c : X) (hN : AbsencesNecessaryFor o Has w g)
    (hEx : DecreesExclusiveAt Has w g dec) (hc : Has w g (dec c)) (v : W)
    (hv : o.frame.access w v) (c' : X) (hc' : Has v g (dec c')) : c' = c :=
  hEx c' c (hN v hv _ hc') hc

/-- Lean-only. Under N, an exclusive real decree sufficing for a contingent effect
leaves some accessible world without the effect and without any decree. -/
theorem noDecreeWorldUnderN {W B D X : Type} (o : Ontic W B) (Has : W → B → D → Prop) (w : W)
    (g x : B) (dec : X → D) (c : X) (hN : AbsencesNecessaryFor o Has w g)
    (hEx : DecreesExclusiveAt Has w g dec) (hc : Has w g (dec c))
    (hSuff : DecreeSuffices o Has w g dec c x) (hCont : ContingentAt o w x) :
    ∃ v, o.frame.access w v ∧ ¬ o.ExistsAt v x ∧ ∀ c', ¬ Has v g (dec c') := by
  obtain ⟨-, v, hv, hnx⟩ := hCont
  refine ⟨v, hv, hnx, fun c' hc' => hnx (hSuff v hv ?_)⟩
  rw [← decreesUnderN o Has w g dec c hN hEx hc v hv c' hc']
  exact hc'

/-- The relation-of-reason certificate. -/
theorem relationOfReason : RelationOfReasonCertificate := by
  refine ⟨fun W B A D p Has w a x h => relationOfReasonCost p Has w a x h,
    fun W B D X o Has w g dec c hN hEx hc => decreesUnderN o Has w g dec c hN hEx hc,
    fun W B D X o Has w g x dec c hN hEx hc hSuff hCont =>
      noDecreeWorldUnderN o Has w g x dec c hN hEx hc hSuff hCont, ?_⟩
  refine ⟨⟨?_, ⟨Determination.esse, ?_, ?_⟩, ⟨rfl, rfl⟩, ?_, rr_contingent⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ⟨false, trivial, rr_contingent⟩, ?_, ?_, fun v _ d h => ?_, rr_actualRoot⟩
  · intro v _ d
    rfl
  · simp [rrOutput, rrHas, TruthCore.Causality.SourceIntellectControls.ProfileControls.pure]
  · intro v _ _
    trivial
  · rintro v - ⟨rfl, -⟩
    exact Or.inr rfl
  · intro x hx d hd
    cases x
    · exact absurd (Or.inl rfl) hx
    · exact hd
  · intro r hr
    have hrt := (rr_actualRoot r).1 hr
    subst hrt
    simp [TruthCore.Causality.RootMultiplication.HasLimitingPrinciple, rrComposite, rrPrior]
  · rintro d S hd - ⟨rfl, -⟩
    simp [rrPure, TruthCore.Causality.SourceIntellectControls.ProfileControls.pure] at hd
  · intro q hq
    exact hq
  · intro q hq
    exact hq
  · intro x hx
    obtain ⟨hxw, v, -, hxv⟩ := hx
    cases x
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact absurd (Or.inl rfl) hxv
  · intro h
    have := h (fun v => v = true) trivial rfl false trivial
    cases this
  · refine ⟨fun x r => ?_, fun r h => h, fun v r _ h => ?_⟩
    · simp [rrNoPotency]
    · cases v <;> exact h
  · cases v <;> exact h

end TruthCore.Results.Modal.MirrorCollapse
