module

public import TruthCore.Causality.SelectionScope

@[expose] public section

namespace TruthCore.Results.Causality.SelectionScope

open TruthCore.Modal.STIT
open TruthCore.Causality.Frame (CausalityFrame)
open TruthCore.Causality.SelectionScope
open TruthCore.Causality.SelectionScope.Model
open TruthCore.Modal.PrussPowerPremises (GivesTo FixedGiver ActualAbsenceByWithholding)
open TruthCore.Modal.PrussPowerPremises.Model (Bg V3 vanCleveG theistG allC gPower gFrame uni
  replEx givesCHere givesDThere vcEx)
open TruthCore.Modal.ModalGrounding (NoActualContingentConcreteIn NoContingentConcreteIn)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.WillVersusChance (GodsHoldActualAbsencePower)

/-! ## Part A -/

section RangeSelection

variable {M H A X : Type} {F : BranchingFrame M H A} {m : M}

theorem explains_iff_not_cellRange (a : A) (h : F.Through m) (out : F.Through m → X) (y : X) :
    ExplainsContrast a h out y ↔ y ∉ CellRange a h out :=
  ⟨fun hp ⟨k, hk, hy⟩ => hp k hk hy, fun hn k hk hy => hn ⟨k, hk, hy⟩⟩

theorem decomposition (a : A) (h : F.Through m) (out : F.Through m → X) (T0 : Set X)
    (hsub : RealizedRange out ⊆ T0) :
    T0 \ CellRange a h out =
        (T0 \ RealizedRange out) ∪ (RealizedRange out \ CellRange a h out) ∧
      Disjoint (T0 \ RealizedRange out) (RealizedRange out \ CellRange a h out) := by
  have hcr : CellRange a h out ⊆ RealizedRange out := fun _ ⟨k, _, hk⟩ => ⟨k, hk⟩
  refine ⟨?_, ?_⟩
  · ext y
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨h0, hn⟩
      by_cases hr : y ∈ RealizedRange out
      · exact Or.inr ⟨hr, hn⟩
      · exact Or.inl ⟨h0, hr⟩
    · rintro (⟨h0, hr⟩ | ⟨hr, hn⟩)
      · exact ⟨h0, fun hc => hr (hcr hc)⟩
      · exact ⟨hsub hr, hn⟩
  · rw [Set.disjoint_left]
    rintro y ⟨_, hr⟩ ⟨hr', _⟩
    exact hr hr'

theorem invariant_explains_iff (a : A) (h : F.Through m) (out : F.Through m → X) (y : X)
    (hinv : InvariantExplanans F m a) :
    ExplainsContrast a h out y ↔ y ∉ RealizedRange out :=
  ⟨fun hp ⟨k, hk⟩ => hp k (hinv h k) hk, fun hn k _ hk => hn ⟨k, hk⟩⟩

theorem invariant_selects_iff (a : A) (h : F.Through m) (out : F.Through m → X)
    (hinv : InvariantExplanans F m a) :
    SelectsActual a h out ↔ ¬ ContingentOutcome h out :=
  ⟨fun hs ⟨k, hk⟩ => hk (hs k (hinv h k)),
    fun hn k _ => Classical.byContradiction fun hne => hn ⟨k, hne⟩⟩

theorem selects_iff_all (a : A) (h : F.Through m) (out : F.Through m → X) :
    SelectsActual a h out ↔ ∀ y, y ≠ out h → ExplainsContrast a h out y :=
  ⟨fun hs _ hy k hk hky => hy (hky ▸ hs k hk),
    fun hall k hk => Classical.byContradiction fun hne => hall (out k) hne k hk rfl⟩

theorem relocation (a : A) (h : F.Through m) (out : F.Through m → X)
    (hs : SelectsActual a h out) (hc : ContingentOutcome h out) :
    Dstit a h (InCell a h) ∧ ∀ b, InvariantExplanans F m b → ¬ Cstit b h (InCell a h) := by
  obtain ⟨k, hk⟩ := hc
  exact ⟨⟨fun _ hj => hj, fun hnec => hk (hs k (hnec k))⟩,
    fun b hinv hcb => hk (hs k (hcb k (hinv h k)))⟩

theorem same_cell_same_profile (a b : A) (h : F.Through m) (out : F.Through m → X) (y : X)
    (hsame : ∀ k, (F.choice m a).r h k ↔ (F.choice m b).r h k) :
    ExplainsContrast a h out y ↔ ExplainsContrast b h out y :=
  ⟨fun hp k hk => hp k ((hsame k).2 hk), fun hp k hk => hp k ((hsame k).1 hk)⟩

end RangeSelection

theorem selectionRangeLaws : SelectionRangeLaws :=
  ⟨fun _ _ _ _ _ _ a h out y => explains_iff_not_cellRange a h out y,
    fun _ _ _ _ _ _ a h out T0 hsub => decomposition a h out T0 hsub,
    fun _ _ _ _ _ _ a h out y hinv => invariant_explains_iff a h out y hinv,
    fun _ _ _ _ _ _ a h out hinv => invariant_selects_iff a h out hinv,
    fun _ _ _ _ _ _ a h out => selects_iff_all a h out,
    fun _ _ _ _ _ _ a h out hs hc => relocation a h out hs hc,
    fun _ _ _ _ _ _ a b h out y hsame => same_cell_same_profile a b h out y hsame⟩

/-! ### The four-account table -/

theorem nature_invariant {E : Type} (scope : Outcome → Prop) (f : Outcome → E) :
    InvariantExplanans (accountFrame scope f) () nature :=
  fun _ _ => rfl

theorem nature_explains_iff {E : Type} (scope : Outcome → Prop) (f : Outcome → E)
    (h : (accountFrame scope f).Through ()) (y : Outcome) :
    ExplainsContrast nature h outcome y ↔ ¬ scope y := by
  rw [invariant_explains_iff nature h outcome y (nature_invariant scope f)]
  exact ⟨fun hn hs => hn ⟨⟨y, hs⟩, rfl⟩, fun hn ⟨k, hk⟩ => hn (hk ▸ k.property)⟩

theorem exercise_selects (scope : Outcome → Prop)
    (h : (accountFrame scope outcomeExercise).Through ()) :
    SelectsActual exercise h outcome :=
  fun _ hk => (Option.some.inj hk).symm

theorem fourAccountTable : FourAccountTable := by
  have cD : ContingentOutcome (F := exerciseSource) (actualIn fitScope outcomeExercise trivial)
      outcome := ⟨⟨.d, trivial⟩, by decide⟩
  have cN : ContingentOutcome (F := permissiveExercise)
      (actualIn permissiveScope outcomeExercise (Or.inr trivial)) outcome :=
    ⟨⟨.none, Or.inl rfl⟩, by decide⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, cD, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (nature_explains_iff onlyC noExercise _ _).2 (by unfold onlyC; decide)
  · exact (nature_explains_iff onlyC noExercise _ _).2 (by unfold onlyC; decide)
  · exact (nature_explains_iff onlyC noExercise _ _).2 (by unfold onlyC; decide)
  · refine (invariant_selects_iff nature _ outcome (nature_invariant onlyC noExercise)).2 ?_
    rintro ⟨⟨o, ho⟩, hne⟩
    exact hne ho
  · rintro ⟨⟨o, ho⟩, hne⟩
    exact hne ho
  · exact (nature_explains_iff fitScope noExercise _ _).2 (fun h => h)
  · exact (nature_explains_iff fitScope noExercise _ _).2 (fun h => h)
  · exact fun hp => (nature_explains_iff fitScope noExercise _ _).1 hp trivial
  · rw [invariant_selects_iff nature _ outcome (nature_invariant fitScope noExercise)]
    exact fun hn => hn ⟨⟨.d, trivial⟩, by decide⟩
  · exact ⟨⟨.d, trivial⟩, by decide⟩
  · exact fun hp => (nature_explains_iff permissiveScope noExercise _ _).1 hp (Or.inl rfl)
  · refine (nature_explains_iff permissiveScope noExercise _ _).2 ?_
    rintro (h | h)
    · cases h
    · exact h
  · exact exercise_selects fitScope _
  · exact (relocation exercise _ outcome (exercise_selects fitScope _) cD).1
  · exact (relocation exercise _ outcome (exercise_selects fitScope _) cD).2 nature
      (nature_invariant fitScope outcomeExercise)
  · exact fun hp => (nature_explains_iff fitScope outcomeExercise _ _).1 hp trivial
  · exact (selects_iff_all exercise _ outcome).1 (exercise_selects permissiveScope _) .none
      (by decide)
  · exact fun hp => (nature_explains_iff permissiveScope outcomeExercise _ _).1 hp (Or.inl rfl)
  · exact (relocation exercise _ outcome (exercise_selects permissiveScope _) cN).1

/-! ## Part B -/

section Omission

variable {W B T R : Type}

theorem withholdsAll_roster {F : CausalityFrame W B T R} {w : W} {g : B}
    (h : WithholdsAllAt F w g) : WithholdsActualRosterAt F w g := by
  obtain ⟨v, hv, hg, hall⟩ := h
  exact ⟨v, hv, hg, fun x _ => hall x⟩

theorem roster_each {F : CausalityFrame W B T R} {w : W} {g : B}
    (h : WithholdsActualRosterAt F w g) : WithholdsEachAt F w g := by
  obtain ⟨v, hv, hg, hr⟩ := h
  exact fun x hx => ⟨v, hv, hg, hr x hx⟩

theorem productive_not_all {F : CausalityFrame W B T R} {w : W} {g : B}
    (hnec : NecessarilyGivesSomeAt F w g) : ¬ WithholdsAllAt F w g := by
  rintro ⟨v, hv, hg, hall⟩
  obtain ⟨x, hx⟩ := hnec v hv hg
  exact hall x hx

theorem fixed_not_each {F : CausalityFrame W B T R} {w : W} {g x : B} (hfix : FixedGiver F g)
    (hw : F.history.ontic.ExistsAt w g) (hx : GivesTo F w g x) : ¬ WithholdsEachAt F w g := by
  intro hEach
  obtain ⟨v, _, hgv, hn⟩ := hEach x hx
  exact hn ((hfix w v hw hgv x).1 hx)

end Omission

theorem vc_gives (v : V3) (x : Bg) (hx : vcEx v x) (hne : x ≠ .g) : GivesTo vanCleveG v .g x :=
  ⟨(), rfl, hx, hne⟩

theorem repl_noActual :
    NoActualContingentConcreteIn replGivingG allC false true := by
  intro x _ hc hx
  obtain ⟨hx0, v, _, hxv⟩ := hc
  cases x with
  | g => exact hxv (Or.inl rfl)
  | c => simp [replGivingG, gFrame, replEx] at hx
  | d => simp [replGivingG, gFrame, replEx] at hx0

theorem repl_each (x : Bg) (hc : ContingentAt replGivingG.history.ontic false x) :
    GivesTo replGivingG false .g x ∧ ¬ GivesTo replGivingG true .g x := by
  obtain ⟨hx0, v, _, hxv⟩ := hc
  cases x with
  | g => exact (hxv (Or.inl rfl)).elim
  | c =>
    refine ⟨⟨(), Or.inl ⟨rfl, rfl, rfl⟩⟩, ?_⟩
    rintro ⟨_, h | h⟩
    · exact Bool.noConfusion h.2.2
    · exact Bg.noConfusion h.2.1
  | d => simp [replGivingG, gFrame, replEx] at hx0

theorem repl_productive : NecessarilyGivesSomeAt replGivingG false .g := by
  intro v _ _
  cases v
  · exact ⟨.c, (), Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨.d, (), Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem omissionScopeTable : OmissionScopeTable := by
  refine ⟨fun _ _ _ _ _ _ _ => ⟨withholdsAll_roster, roster_each⟩,
    fun _ _ _ _ _ _ _ => productive_not_all,
    fun _ _ _ _ _ _ _ _ hfix hw hx => fixed_not_each hfix hw hx, ⟨?_, ?_, ?_⟩, ⟨?_, ?_,
    repl_productive, ?_⟩, ?_, TruthCore.Models.STITControls.pointwiseNotJoint, ?_⟩
  · rintro x ⟨_, -, hx, hne⟩
    cases x with
    | g => exact (hne rfl).elim
    | c => exact ⟨.z, trivial, Or.inl rfl, fun ⟨_, _, h, _⟩ => by simp [vcEx] at h⟩
    | d => exact ⟨.b, trivial, Or.inl rfl, fun ⟨_, _, h, _⟩ => by simp [vcEx] at h⟩
  · rintro ⟨v, _, _, hr⟩
    have gc : GivesTo vanCleveG .a .g .c := vc_gives .a .c (by simp [vcEx]) (by decide)
    have gd : GivesTo vanCleveG .a .g .d := vc_gives .a .d (by simp [vcEx]) (by decide)
    cases v with
    | a => exact hr .c gc gc
    | b => exact hr .c gc (vc_gives .b .c (by simp [vcEx]) (by decide))
    | z => exact hr .d gd (vc_gives .z .d (by simp [vcEx]) (by decide))
  · intro v _ _
    cases v with
    | a => exact ⟨.c, vc_gives .a .c (by simp [vcEx]) (by decide)⟩
    | b => exact ⟨.c, vc_gives .b .c (by simp [vcEx]) (by decide)⟩
    | z => exact ⟨.d, vc_gives .z .d (by simp [vcEx]) (by decide)⟩
  · refine ⟨true, trivial, Or.inl rfl, fun x hx hx' => ?_⟩
    have h0 := (repl_each x ?_).2
    · exact h0 hx'
    · obtain ⟨_, h | h⟩ := hx
      · obtain ⟨_, rfl, _⟩ := h
        exact ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), true, trivial, by simp [replGivingG, gFrame, replEx]⟩
      · exact Bool.noConfusion h.2.2
  · rintro ⟨v, _, _, hall⟩
    cases v
    · exact hall .c ⟨(), Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact hall .d ⟨(), Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨.g, Or.inl rfl, rfl, true, trivial, repl_noActual, Or.inl rfl,
      fun x _ hc => repl_each x hc⟩
  · exact ⟨true, trivial, Or.inl rfl, fun _ ⟨_, h⟩ => Bool.noConfusion h.2.2⟩
  · have t := TruthCore.Models.STITControls.tiedNoEmptyChoice
    exact ⟨t.1, t.2.1, t.2.2.2⟩

/-! ### The complete-decision fork -/

theorem omission_undominated_iff {D : Type} [PartialOrder D] (C : Set D) (o : D) :
    Maximal (· ∈ insert o C) o ↔ ¬ ∃ c ∈ C, o < c := by
  rw [maximal_iff_forall_gt]
  constructor
  · rintro ⟨_, h⟩ ⟨c, hc, hlt⟩
    exact h hlt (Set.mem_insert_of_mem o hc)
  · intro hn
    refine ⟨Set.mem_insert o C, fun y hlt hy => ?_⟩
    rcases hy with rfl | hy
    · exact lt_irrefl _ hlt
    · exact hn ⟨y, hy, hlt⟩

theorem creation_undominated_iff {D : Type} [PartialOrder D] (C : Set D) (o c : D) (hc : c ∈ C) :
    Maximal (· ∈ insert o C) c ↔ Maximal (· ∈ C) c ∧ ¬ c < o := by
  simp only [maximal_iff_forall_gt]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨⟨hc, fun y hlt hy => h hlt (Set.mem_insert_of_mem o hy)⟩,
      fun hlt => h hlt (Set.mem_insert o C)⟩
  · rintro ⟨⟨_, hm⟩, hno⟩
    refine ⟨Set.mem_insert_of_mem o hc, fun y hlt hy => ?_⟩
    rcases hy with rfl | hy
    · exact hno hlt
    · exact hm hlt hy

theorem completeDecisionFork : CompleteDecisionFork := by
  refine ⟨fun _ _ C o => omission_undominated_iff C o,
    fun _ _ C o c hc => creation_undominated_iff C o c hc, ?_, ?_, ?_, ?_⟩
  · intro D _ C m hfin _ huniq c hc hne
    obtain ⟨b, hcb, hb⟩ := hfin.exists_le_maximal hc
    have hbm := huniq b hb
    subst hbm
    exact lt_of_le_of_ne hcb hne
  · rintro D _ C o himp ⟨c, hc, hlt⟩ ⟨d, hd⟩
    rcases hd.prop with rfl | hdC
    · exact (omission_undominated_iff C d).1 hd ⟨c, hc, hlt⟩
    · obtain ⟨c', hc', hlt'⟩ := himp d hdC
      exact (maximal_iff_forall_gt.1 hd).2 hlt' (Set.mem_insert_of_mem _ hc')
  · intro W D _ C o scope chosen hpol hex v hv heq
    have hm := hpol v hv
    rw [heq] at hm
    exact (omission_undominated_iff C o).1 hm hex
  · intro C chosen
    have key : ∀ b b' : Bool, ¬ ({b} : Set Bool) < {b'} := by
      intro b b' hlt
      have hb : b = b' := Set.mem_singleton_iff.mp (hlt.le (Set.mem_singleton b))
      subst hb
      exact lt_irrefl _ hlt
    have memC : ∀ b, ({b} : Set Bool) ∈ C := by
      intro b
      cases b
      · exact Or.inr rfl
      · exact Or.inl rfl
    refine ⟨fun b => ?_, ⟨{true}, Or.inl rfl, Set.empty_ssubset.2 (Set.singleton_nonempty true)⟩,
      fun b => Set.singleton_ne_empty b, ?_⟩
    · refine (creation_undominated_iff C ∅ {b} (memC b)).2 ⟨?_, ?_⟩
      · rw [maximal_iff_forall_gt]
        refine ⟨memC b, fun y hlt hy => ?_⟩
        rcases hy with rfl | rfl
        · exact key b true hlt
        · exact key b false hlt
      · intro hlt
        exact (hlt.le (Set.mem_singleton b)).elim
    · rintro c (rfl | rfl)
      · exact ⟨false, fun h => Bool.noConfusion (Set.singleton_eq_singleton_iff.mp h)⟩
      · exact ⟨true, fun h => Bool.noConfusion (Set.singleton_eq_singleton_iff.mp h)⟩

/-! ## Part C -/

section PowerScope

variable {W B T R : Type}

/-- With Euclidean access, total absence of contingent concreta at an accessible
world is absence there of every concretum contingent at `w`. -/
theorem actualAbsence_of_total (F : CausalityFrame W B T R) (concrete : B → Prop) (w v : W)
    (hE : TruthCore.Modal.Euclidean F.history.ontic.frame)
    (hv : F.history.ontic.frame.access w v) (htot : NoContingentConcreteIn F concrete v) :
    NoActualContingentConcreteIn F concrete w v := by
  intro x hx hcont hxv
  obtain ⟨_, u, hu, hxu⟩ := hcont
  exact htot x hx ⟨hxv, u, hE w v u hv hu, hxu⟩

/-- `0050b6ed` from its total-refraining sibling, Euclidean access and monotone
powers. -/
theorem actualAbsencePowerOfTotal {W B T R : Type} (F : CausalityFrame W B T R)
    (PowerFor : W → B → (W → Prop) → Prop) (concrete : B → Prop) (IsGod : B → Prop) (w : W)
    (hTotal : GodsHoldTotalAbsencePower F PowerFor concrete IsGod w)
    (hEuclid : TruthCore.Modal.Euclidean F.history.ontic.frame)
    (hMono : PowerForMonotoneAt F PowerFor w) :
    GodsHoldActualAbsencePower F PowerFor concrete IsGod w := by
  intro g hg
  obtain ⟨hex, hpow⟩ := hTotal g hg
  exact ⟨hex, hMono g _ _ (fun v hv htot => actualAbsence_of_total F concrete w v hEuclid hv htot)
    hpow⟩

theorem possibilityPower_monotone (F : CausalityFrame W B T R) (w : W) :
    PowerForMonotoneAt F (possibilityPower F) w := by
  rintro y p q himp ⟨v, hv, hp, hy⟩
  exact ⟨v, hv, himp v hv hp, hy⟩

end PowerScope

theorem three_noContingent_none : NoContingentConcreteIn threeG allC none := by
  rintro x _ ⟨hx, u, _, hxu⟩
  rcases hx with rfl | ⟨_, h⟩ | ⟨_, h⟩
  · exact hxu (Or.inl rfl)
  · cases h
  · cases h

theorem three_noActual_true : NoActualContingentConcreteIn threeG allC (some false) (some true) := by
  rintro x _ ⟨hx, u, _, hxu⟩ hxt
  rcases hx with rfl | ⟨rfl, _⟩ | ⟨_, h⟩
  · exact hxu (Or.inl rfl)
  · simp [threeG, gFrame, threeEx] at hxt
  · cases h

theorem three_total_only_none (v : Option Bool) (hv : NoContingentConcreteIn threeG allC v) :
    v = none := by
  rcases v with _ | b
  · rfl
  · cases b
    · exact (hv .c trivial ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), none, trivial,
        by simp [threeG, gFrame, threeEx]⟩).elim
    · exact (hv .d trivial ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), none, trivial,
        by simp [threeG, gFrame, threeEx]⟩).elim

theorem actualAbsencePowerScopeControls : ActualAbsencePowerScopeControls := by
  have euclidThree : TruthCore.Modal.Euclidean threeG.history.ontic.frame :=
    fun _ _ _ _ _ => trivial
  have euclidRepl : TruthCore.Modal.Euclidean replGivingG.history.ontic.frame :=
    fun _ _ _ _ _ => trivial
  have totalThree : GodsHoldTotalAbsencePower threeG (possibilityPower threeG) allC (· = .g)
      (some false) := by
    rintro _ rfl
    exact ⟨Or.inl rfl, none, trivial, three_noContingent_none, Or.inl rfl⟩
  have actualRepl : GodsHoldActualAbsencePower replGivingG (possibilityPower replGivingG) allC
      (· = .g) false := by
    rintro _ rfl
    exact ⟨Or.inl rfl, true, trivial, repl_noActual, Or.inl rfl⟩
  refine ⟨⟨totalThree, euclidThree, possibilityPower_monotone _ _,
      actualAbsencePowerOfTotal _ _ _ _ _ totalThree euclidThree (possibilityPower_monotone _ _)⟩,
    ⟨actualRepl, euclidRepl, possibilityPower_monotone _ _, ?_, repl_productive, ?_⟩,
    ⟨?_, possibilityPower_monotone _ _, ?_, ?_⟩, ⟨?_, euclidThree, ?_, ?_⟩⟩
  · intro h
    obtain ⟨_, v, _, hno, _⟩ := h .g rfl
    cases v
    · exact hno .c trivial ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), true, trivial,
        by simp [replGivingG, gFrame, replEx]⟩
    · exact hno .d trivial ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), false, trivial,
        by simp [replGivingG, gFrame, replEx]⟩
  · exact ⟨.g, Or.inl rfl, ⟨true, trivial, repl_noActual, Or.inl rfl⟩, true, trivial,
      repl_noActual, Or.inl rfl, fun x _ hc => repl_each x hc⟩
  · rintro _ rfl
    refine ⟨⟨by decide, by decide⟩, .b, Or.inl ⟨rfl, rfl⟩, ?_, ⟨by decide, by decide⟩⟩
    rintro x _ ⟨hxb, u, hu, hxu⟩
    rcases hu with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩
    · cases h
    · cases h
    · exact hxu hxb
  · intro hE
    have := hE .a .b .c (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    rcases this with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> cases h
  · intro h
    obtain ⟨_, v, hv, hno, hgv⟩ := h .g rfl
    have hvb : v = .b := by
      rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h, _⟩
      · rfl
      · exact (hgv.2 rfl).elim
      · cases h
    subst hvb
    exact hno .g trivial ⟨⟨by decide, by decide⟩, .c, Or.inr (Or.inl ⟨rfl, rfl⟩),
      fun h => h.2 rfl⟩ hgv
  · rintro _ rfl
    exact ⟨Or.inl rfl, rfl, fun v hv => three_total_only_none v hv⟩
  · intro hm
    have hp := hm .g _ _ (fun v hv htot =>
      actualAbsence_of_total threeG allC (some false) v euclidThree hv htot)
      ⟨rfl, fun v hv => three_total_only_none v hv⟩
    exact Option.some_ne_none true (hp.2 (some true) three_noActual_true)
  · intro h
    exact Option.some_ne_none true ((h .g rfl).2.2 (some true) three_noActual_true)

end TruthCore.Results.Causality.SelectionScope
