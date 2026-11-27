module

public import TruthCore.Causality.RootPerfectionExclusion
public import TruthCore.Results.Causality.FiniteEsseDependence.Solution
public import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution
public import TruthCore.Results.Causality.WholePowerPerfection.Solution
public import TruthCore.Modal.LimitationPossibility

@[expose] public section

namespace TruthCore.Results.Causality.RootPerfectionExclusion

open TruthCore.Causality.RootPerfectionExclusion
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple UnlimitedDeterminationsArePure)
open TruthCore.Causality.PureActRoot (ActualRootHasEveryPureDetermination)
open TruthCore.Causality.FiniteEsseDependence (LimitedEsseHasGroundingGiverAt)
open TruthCore.Causality.SourceIntellectControls
  (HasCompatibleExtension possessedIfCompatibleAndOmissionFixed)
open TruthCore.Logic (ExcludedMiddle)

/-- The structural L bridge is derived, not assumed: if a bearer without a
represented limiting principle had only pure determinations (the open RootPurity
bridge), joint compossibility would add the admissible pure `k` to its admissible
actual profile, so its positive profile could not exclude `k`. -/
theorem positiveExclusionLimits {B D P : Type}
    (Admissible : Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P)
    (hEM : ExcludedMiddle)
    (hPurity : UnlimitedDeterminationsArePure Composite Prior essence esse Has Pure)
    (hExtend : PureExtensionsAdmissible Admissible Pure) :
    PositiveProfileExclusionLimits Admissible Has Pure Composite Prior essence esse := by
  intro x k hAdm hk hkAdm hExcluded
  cases hEM (HasLimitingPrinciple Composite Prior essence esse x) with
  | inl hLimit => exact hLimit
  | inr hUnlimited =>
    exact (hExcluded ⟨insert k (ActualProfile Has x),
      hExtend _ k hAdm (fun d hd => hPurity x hUnlimited d hd) hk hkAdm,
      fun _ hd => Set.mem_insert_of_mem k hd, Set.mem_insert k _⟩).elim

/-- E∘L in the structural sense. At an actual root no unexplained absence (E),
the derived or assumed structural L bridge, admissibility of the root's actual
profile and of each pure determination, and the root's lack of every represented
limiting principle give every pure determination to every actual root. -/
theorem rootPerfectionFromNoUnexplainedAbsence {W B D P : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P)
    (hEM : ExcludedMiddle)
    (hRoots : ActualRootsWithoutLimitingPrinciple m w Composite Prior essence esse)
    (hLimits : PositiveProfileExclusionLimits Admissible Has Pure Composite Prior essence esse)
    (hRootAdm : RootProfilesAdmissible m w Admissible Has)
    (hPureAdm : PureDeterminationsAdmissible Admissible Pure)
    (hNoBrute : NoUnexplainedAbsenceAtRoots m w Admissible Has) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  intro r hr k hk
  cases hEM (Has r k) with
  | inl hHas => exact hHas
  | inr hLacks =>
    exact (hRoots r hr (hLimits r k (hRootAdm r hr) hk (hPureAdm k hk)
      (fun hCompatible => hNoBrute r hr k ⟨hLacks, hCompatible⟩))).elim

/-- The formal-limitation L bridge from the determination-to-esse bridge and
joint compossibility. -/
theorem positiveExclusionLimitsEsse {B D : Type}
    (Admissible : Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (Limited : B → Prop) (hEM : ExcludedMiddle)
    (hImpure : ImpureDeterminationLimitsEsse Has Pure Limited)
    (hExtend : PureExtensionsAdmissible Admissible Pure) :
    PositiveProfileExclusionLimitsEsse Admissible Has Pure Limited := by
  intro x k hAdm hk hkAdm hExcluded
  cases hEM (Limited x) with
  | inl hLimited => exact hLimited
  | inr hUnlimited =>
    have hAllPure : ∀ d ∈ ActualProfile Has x, Pure d := by
      intro d hd
      cases hEM (Pure d) with
      | inl hPure => exact hPure
      | inr hImp => exact (hUnlimited (hImpure x d hd hImp)).elim
    exact (hExcluded ⟨insert k (ActualProfile Has x),
      hExtend _ k hAdm hAllPure hk hkAdm,
      fun _ hd => Set.mem_insert_of_mem k hd, Set.mem_insert k _⟩).elim

/-- E∘L composed with `rootUnlimited` (#1914): the limited-esse giver premise
08178314 excludes `Limited` at every actual root, and the same E and
admissibility inputs then give every pure determination. The core step is
`possessedIfCompatibleAndOmissionFixed`, whose compatibility input is refuted. -/
theorem rootPerfectionFromNoUnexplainedAbsenceUnlimited {W B D R : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (Limited : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hEM : ExcludedMiddle)
    (hGiver : LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse)
    (hLimits : PositiveProfileExclusionLimitsEsse Admissible Has Pure Limited)
    (hRootAdm : RootProfilesAdmissible m w Admissible Has)
    (hPureAdm : PureDeterminationsAdmissible Admissible Pure)
    (hNoBrute : NoUnexplainedAbsenceAtRoots m w Admissible Has) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  intro r hr k hk
  cases hEM (Has r k) with
  | inl hHas => exact hHas
  | inr hLacks =>
    exact (TruthCore.Results.Causality.FiniteEsseDependence.rootUnlimited m w Limited
      CausesIn esse hGiver hr (hLimits r k (hRootAdm r hr) hk (hPureAdm k hk)
        (fun hCompatible => hNoBrute r hr k ⟨hLacks, hCompatible⟩))).elim

/-! ## Coverage and exclusivity of the three cases (Lean-only helpers) -/

/-- Coverage: with excluded middle, every absence is of exactly one of the
three kinds relative to the supplied family. This is classical bookkeeping;
the substantive content is the choice of family and of `Has`. -/
theorem absenceTrichotomy {B D : Type} (Admissible : Set D → Prop) (Has : B → D → Prop)
    (hEM : ExcludedMiddle) {x : B} {k : D} (hLacks : ¬ Has x k) :
    AbsenceFromAdmissibility Admissible Has x k ∨
      AbsenceFromPositiveProfile Admissible Has x k ∨
      UnexplainedAbsence Admissible Has x k := by
  cases hEM (HasCompatibleExtension Admissible (ActualProfile Has x) k) with
  | inl hCompatible => exact Or.inr (Or.inr ⟨hLacks, hCompatible⟩)
  | inr hExcluded =>
    cases hEM (∃ q, Admissible q ∧ k ∈ q) with
    | inl hSome => exact Or.inr (Or.inl ⟨hLacks, hSome, hExcluded⟩)
    | inr hNone => exact Or.inl ⟨hLacks, fun q hq hkq => hNone ⟨q, hq, hkq⟩⟩

/-- Exclusivity: no two cases hold together. -/
theorem absenceTrichotomyExclusive {B D : Type} (Admissible : Set D → Prop)
    (Has : B → D → Prop) (x : B) (k : D) :
    ¬ (AbsenceFromAdmissibility Admissible Has x k ∧
        AbsenceFromPositiveProfile Admissible Has x k) ∧
    ¬ (AbsenceFromAdmissibility Admissible Has x k ∧ UnexplainedAbsence Admissible Has x k) ∧
    ¬ (AbsenceFromPositiveProfile Admissible Has x k ∧
        UnexplainedAbsence Admissible Has x k) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨_, hNone⟩, _, ⟨q, hq, hkq⟩, _⟩
    exact hNone q hq hkq
  · rintro ⟨⟨_, hNone⟩, _, ⟨q, hq, _, hkq⟩⟩
    exact hNone q hq hkq
  · rintro ⟨⟨_, _, hExcluded⟩, _, hCompatible⟩
    exact hExcluded hCompatible

/-- A single excluding determination is one way case (ii) arises. -/
theorem singleExcluderGivesPositiveExclusion {B D : Type} (Admissible : Set D → Prop)
    (Has : B → D → Prop) {x : B} {d k : D} (hLacks : ¬ Has x k) (hd : Has x d)
    (hSome : ∃ q, Admissible q ∧ k ∈ q)
    (hExcludes : ∀ q, Admissible q → d ∈ q → k ∉ q) :
    AbsenceFromPositiveProfile Admissible Has x k :=
  ⟨hLacks, hSome, fun ⟨q, hq, hContains, hkq⟩ => hExcludes q hq (hContains hd) hkq⟩

/-- No unexplained absence at a root, with its actual profile admissible, is
exactly maximality of that profile in the admissible family (Mathlib `Maximal`). -/
theorem noUnexplainedAbsenceIffMaximal {B D : Type} (Admissible : Set D → Prop)
    (Has : B → D → Prop) (x : B) (hEM : ExcludedMiddle)
    (hAdm : Admissible (ActualProfile Has x)) :
    (∀ d, ¬ UnexplainedAbsence Admissible Has x d) ↔
      Maximal Admissible (ActualProfile Has x) := by
  rw [maximal_subset_iff']
  constructor
  · intro hNo
    refine ⟨hAdm, fun q hq hSub d hd => ?_⟩
    cases hEM (Has x d) with
    | inl hHas => exact hHas
    | inr hLacks => exact (hNo d ⟨hLacks, q, hq, hSub, hd⟩).elim
  · rintro ⟨_, hMax⟩ d ⟨hLacks, q, hq, hSub, hd⟩
    exact hLacks (hMax hq hSub hd)

/-- The core step is the existing conditional fullness theorem: compatibility
from joint compossibility and omission-fixing from no unexplained absence. -/
theorem rootHasCompatibleFromNoUnexplainedAbsence {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop) (Has : B → D → Prop)
    (Pure : D → Prop)
    (hExtend : PureExtensionsAdmissible Admissible Pure)
    (hRootAdm : RootProfilesAdmissible m w Admissible Has)
    (hPureAdm : PureDeterminationsAdmissible Admissible Pure)
    (hNoBrute : NoUnexplainedAbsenceAtRoots m w Admissible Has)
    {r : B} (hr : ActualRoot m w r) (hAllPure : ∀ d, Has r d → Pure d)
    {k : D} (hk : Pure k) : Has r k :=
  possessedIfCompatibleAndOmissionFixed Admissible (ActualProfile Has r) k
    ⟨insert k (ActualProfile Has r), hExtend _ k (hRootAdm r hr) hAllPure hk (hPureAdm k hk),
      fun _ hd => Set.mem_insert_of_mem k hd, Set.mem_insert k _⟩
    (fun hLacks q hq hSub hkq => hNoBrute r hr k ⟨fun h => hLacks h, q, hq, hSub, hkq⟩)

/-- The A8 classifier as an L adapter bypasses every explanation: if lacking
each pure determination is a classifier-limiting property (L1) and a bearer of
a classifier-limiting property has limited esse (L3), the absence alone is
limiting, so roots have every pure determination with no use of admissibility,
positive exclusion or unexplained absence. L1 ∘ L3 is contraposed fullness. -/
theorem classifierRouteIgnoresExplanation {W B D R : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop) (Pure : D → Prop)
    (L : TruthCore.Isabelle.AFP.GoedelGod.Property W B → W → Prop)
    (Limited : B → Prop) (CausesIn : B → B → R → Prop) (esse : R) (hEM : ExcludedMiddle)
    (hClassify : ∀ k, Pure k →
      TruthCore.Modal.LimitationPossibility.KnownLimitingAt L (fun x _ => ¬ Has x k) w)
    (hToEsse : ∀ Q x, TruthCore.Modal.LimitationPossibility.KnownLimitingAt L Q w →
      Q x w → Limited x)
    (hGiver : LimitedEsseHasGroundingGiverAt m w Limited CausesIn esse) :
    ActualRootHasEveryPureDetermination m w Has Pure := by
  intro r hr k hk
  cases hEM (Has r k) with
  | inl hHas => exact hHas
  | inr hLacks =>
    exact (TruthCore.Results.Causality.FiniteEsseDependence.rootUnlimited m w Limited
      CausesIn esse hGiver hr (hToEsse _ r (hClassify k hk) hLacks)).elim

/-! ## Simplicity reading and the four roles (question D) -/

open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
  (SelfCapacityExercisedOrPotent)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

/-- At an own-being source in pure act, under the exercise-or-potency reading
of an unexercised own capacity and the ab-esse-ad-posse premise, own capacity
and actual exercise coincide for self-directed contents. Productive power and
objective exemplarity are untouched: they are not capacities of the source's own
apprehension. -/
theorem aptitudeIffExerciseAtPureAct {B C R : Type}
    (OwnBeing : B → Prop) (About : C → B → Prop)
    (CanApprehend Apprehends : B → C → Prop) (InPotency : B → R → Prop) (understanding : R)
    (hBridge : SelfCapacityExercisedOrPotent OwnBeing About CanApprehend Apprehends
      InPotency understanding)
    (hPosse : ∀ g c, Apprehends g c → CanApprehend g c)
    {g : B} (hOwn : OwnBeing g) (hPure : PureAct InPotency g) {c : C} (hAbout : About c g) :
    CanApprehend g c ↔ Apprehends g c :=
  ⟨fun hCan => (hBridge g c hOwn hAbout hCan).resolve_right (hPure understanding),
    hPosse g c⟩

/-! ## Finite controls -/

section Controls

/-- The #1970 pure determinations (`esse`, `a`, `b`, `noesis`). -/
local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.RootPerfectionExclusion.Control
open TruthCore.Causality.SourceIntellectControls.ProfileControls hiding pure
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile frame)

theorem rootIff (r : Bool) : ActualRoot rootProfile true r ↔ r = true := by
  cases r <;> simp [ActualRoot, TruthCore.Causality.NecessaryRootFork.ActualConcrete,
    TruthCore.Causality.CogitoNecessaryConcrete.ActualConcreteGround, rootProfile, frame]

theorem limitingIff (c : Prop) (x : Bool) :
    HasLimitingPrinciple (composite c) prior rep rep x ↔ (x = true ∧ c) ∨ x = false := by
  cases x <;> simp [HasLimitingPrinciple, composite, prior, rep]

theorem rootsIff (c : Prop) : roots c ↔ ¬ c := by
  simp [roots, ActualRootsWithoutLimitingPrinciple, rootIff, limitingIff]

theorem memPure (d : Determination) : d ∈ pureSet ↔ d ≠ Determination.limiter := by
  cases d <;> simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.pure]

theorem limiterImpure : ¬ isPure Determination.limiter := by simp [isPure, memPure]

theorem effectPure : ∀ d ∈ effect, isPure d := by
  intro d hd
  simp only [effect, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl <;> simp [isPure, memPure]

theorem positivePure : ∀ d ∈ positive, isPure d := fun _ hd => profileComparisons.2.2.1.2.1 hd

theorem jointPositive : jointConflict positive := profileComparisons.2.2.2.2.1.1

theorem jointExcludes : ¬ HasCompatibleExtension jointConflict positive Determination.noesis :=
  profileComparisons.2.2.2.2.1.2.2.2

theorem pureOpen : openProfile pureSet := by simp [openProfile, memPure]

theorem purityOf (src : Set Determination) (c : Prop) (h : ¬ c → ∀ d ∈ src, isPure d) :
    purity src c := by
  intro x hx d hd
  cases x with
  | false => exact (hx ((limitingIff c false).2 (Or.inr rfl))).elim
  | true => exact h (fun hc => hx ((limitingIff c true).2 (Or.inl ⟨rfl, hc⟩))) d hd

theorem openCompatible (p : Set Determination) (k : Determination) (hp : openProfile p)
    (hk : isPure k) : HasCompatibleExtension openProfile p k := by
  refine ⟨insert k p, ⟨Set.mem_insert_of_mem k hp.1, fun hl => ?_⟩,
    Set.subset_insert k p, Set.mem_insert k p⟩
  rcases Set.mem_insert_iff.mp hl with h | h
  · exact limiterImpure (h ▸ hk)
  · exact hp.2 h

theorem extendOpen : extend openProfile :=
  fun q k hq _ hk _ => (openCompatible q k hq hk).elim fun _ h => by
    exact ⟨Set.mem_insert_of_mem k hq.1, fun hl => by
      rcases Set.mem_insert_iff.mp hl with e | e
      · exact limiterImpure (e ▸ hk)
      · exact hq.2 e⟩

theorem finiteCompatible (p : Set Determination) (k : Determination) (hp : finiteMode p)
    (hLim : Determination.limiter ∉ p) (hk : isPure k) : finiteMode (insert k p) := by
  refine ⟨Set.mem_insert_of_mem k hp.1, fun ⟨hl, _⟩ => ?_⟩
  rcases Set.mem_insert_iff.mp hl with h | h
  · exact limiterImpure (h ▸ hk)
  · exact hLim h

theorem extendFinite : extend finiteMode :=
  fun q k hq hPure hk _ => finiteCompatible q k hq (fun h => limiterImpure (hPure _ h)) hk

theorem extendExact : extend exactClosure := by
  intro q k hq _ _ hk
  obtain ⟨q', hq', hkq⟩ := hk
  unfold exactClosure at *
  subst hq hq'
  exact Set.insert_eq_of_mem hkq

theorem notExtendJoint : ¬ extend jointConflict := by
  intro h
  obtain ⟨p, hp, hn, _⟩ := jointConflictPairwise Determination.noesis (by simp [memPure])
    Determination.noesis (by simp [memPure])
  exact jointExcludes ⟨insert Determination.noesis positive,
    h positive _ jointPositive positivePure (by simp [isPure, memPure]) ⟨p, hp, hn⟩,
    Set.subset_insert _ _, Set.mem_insert _ _⟩

theorem limitsOpen (src : Set Determination) (c : Prop) : limits openProfile src c :=
  fun _ k hAdm hk _ hNo => (hNo (openCompatible _ k hAdm hk)).elim

theorem limitsExact : limits exactClosure positive False := by
  intro x k hAdm _ hkAdm hNo
  obtain ⟨q, hq, hkq⟩ := hkAdm
  refine (hNo ⟨ActualProfile (has positive) x, hAdm, subset_refl _, ?_⟩).elim
  unfold exactClosure at hAdm hq
  rw [hAdm]
  rw [hq] at hkq
  exact hkq

theorem notLimitsJoint : ¬ limits jointConflict positive False := by
  intro h
  obtain ⟨p, hp, hn, _⟩ := jointConflictPairwise Determination.noesis (by simp [memPure])
    Determination.noesis (by simp [memPure])
  have := h true Determination.noesis jointPositive (by simp [isPure, memPure])
    ⟨p, hp, hn⟩ jointExcludes
  simp [limitingIff] at this

theorem effectFinite : finiteMode effect := by simp [finiteMode, effect]

theorem notLimitsFinite : ¬ limits finiteMode limitedMode False := by
  intro h
  have := h true Determination.noesis profileComparisons.2.2.2.1.1 (by simp [isPure, memPure])
    ⟨effect, effectFinite, by simp [effect]⟩ profileComparisons.2.2.2.1.2.2.2
  simp [limitingIff] at this

theorem limitsComposite (adm : Set Determination → Prop) (src : Set Determination) :
    limits adm src True := by
  intro x _ _ _ _ _
  rw [limitingIff]
  cases x <;> simp

theorem rootAdmOf (adm : Set Determination → Prop) (src : Set Determination) (h : adm src) :
    rootAdm adm src := by
  intro r hr
  rw [rootIff] at hr
  subst hr
  exact h

theorem noBruteOf (adm : Set Determination → Prop) (src : Set Determination)
    (h : ∀ d, d ∉ src → ¬ HasCompatibleExtension adm src d) : noBrute adm src := by
  intro r hr d ⟨hLacks, hComp⟩
  rw [rootIff] at hr
  subst hr
  exact h d hLacks hComp

theorem fullIff (src : Set Determination) : full src ↔ ∀ d, isPure d → d ∈ src := by
  constructor
  · intro h d hd
    exact h true ((rootIff true).2 rfl) d hd
  · intro h r hr d hd
    rw [rootIff] at hr
    subst hr
    exact h d hd

theorem noesisNotPositive : Determination.noesis ∉ positive := by simp [positive]

theorem notFullPositive : ¬ full positive :=
  fun h => noesisNotPositive ((fullIff positive).1 h _ (by simp [isPure, memPure]))

theorem notFullLimited : ¬ full limitedMode := by
  intro h
  have := (fullIff limitedMode).1 h Determination.noesis (by simp [isPure, memPure])
  simp [limitedMode, positive] at this

theorem unexplainedPositive :
    UnexplainedAbsence openProfile (has positive) true Determination.noesis :=
  ⟨noesisNotPositive, openCompatible positive _ profileComparisons.2.2.1.1
    (by simp [isPure, memPure])⟩

theorem pureAdmOpen : pureAdm openProfile := fun _ hk => ⟨pureSet, pureOpen, hk⟩

theorem pureAdmFinite : pureAdm finiteMode :=
  fun k hk => ⟨pureSet, by simp [finiteMode, memPure], hk⟩

theorem pureAdmJoint : pureAdm jointConflict := fun k hk => by
  obtain ⟨p, hp, hkp, _⟩ := jointConflictPairwise k hk k hk
  exact ⟨p, hp, hkp⟩

theorem notPureAdmExact : ¬ pureAdm exactClosure := by
  intro h
  obtain ⟨q, hq, hn⟩ := h Determination.noesis (by simp [isPure, memPure])
  unfold exactClosure at hq
  subst hq
  exact noesisNotPositive hn

theorem structuralControls : StructuralControls := by
  have hR := (rootsIff False).2 not_false
  have hPos : purity positive False := purityOf _ _ fun _ => positivePure
  refine ⟨⟨hR, purityOf _ _ fun _ _ h => h, extendOpen, limitsOpen _ _,
      rootAdmOf _ _ pureOpen, pureAdmOpen, noBruteOf _ _ ?_, (fullIff _).2 fun _ h => h⟩,
    ⟨hR, hPos, extendOpen, limitsOpen _ _, rootAdmOf _ _ profileComparisons.2.2.1.1,
      pureAdmOpen, fun h => h true ((rootIff true).2 rfl) _ unexplainedPositive,
      unexplainedPositive, notFullPositive⟩,
    ⟨hR, hPos, notExtendJoint, notLimitsJoint, rootAdmOf _ _ jointPositive,
      pureAdmJoint, noBruteOf _ _ ?_, ⟨noesisNotPositive, ?_, jointExcludes⟩,
      notFullPositive⟩,
    ⟨hR, hPos, extendExact, limitsExact, rootAdmOf _ _ rfl, notPureAdmExact, noBruteOf _ _ ?_,
      ⟨noesisNotPositive, fun q hq hn => ?_⟩, notFullPositive⟩,
    ⟨hR, fun h => ?_, extendFinite, notLimitsFinite, rootAdmOf _ _ profileComparisons.2.2.2.1.1,
      pureAdmFinite, noBruteOf _ _ ?_, notFullLimited⟩,
    ⟨fun h => (rootsIff True).1 h trivial, purityOf _ _ fun h => (h trivial).elim, extendFinite,
      limitsComposite _ _, rootAdmOf _ _ profileComparisons.2.2.2.1.1, pureAdmFinite,
      noBruteOf _ _ ?_, notFullLimited⟩⟩
  · intro d hd ⟨_, _, _, hl⟩
    cases d <;> simp [memPure] at hd
    exact (by assumption : openProfile _).2 hl
  · intro d hd ⟨q, hq, hSub, hdq⟩
    cases d <;> simp [positive] at hd
    · exact jointExcludes ⟨q, hq, hSub, hdq⟩
    · exact hq.1.2 hdq
  · obtain ⟨p, hp, hn, _⟩ := jointConflictPairwise Determination.noesis (by simp [memPure])
      Determination.noesis (by simp [memPure])
    exact ⟨p, hp, hn⟩
  · intro d hd ⟨q, hq, _, hdq⟩
    unfold exactClosure at hq
    subst hq
    exact hd hdq
  · unfold exactClosure at hq
    subst hq
    exact noesisNotPositive hn
  · have := h true ((limitingIff False true).not.2 (by simp)) Determination.limiter
      (by simp [has, limitedMode])
    exact limiterImpure this
  · intro d hd ⟨q, hq, hSub, hdq⟩
    cases d <;> simp [limitedMode, positive] at hd
    exact profileComparisons.2.2.2.1.2.2.2 ⟨q, hq, hSub, hdq⟩
  · intro d hd ⟨q, hq, hSub, hdq⟩
    cases d <;> simp [limitedMode, positive] at hd
    exact profileComparisons.2.2.2.1.2.2.2 ⟨q, hq, hSub, hdq⟩

theorem anchorControl : AnchorControl := by
  have hInf : ¬ (ActualProfile hasFromOne true).Finite := Set.Ici_infinite 1
  refine ⟨(rootsIff False).2 not_false, fun _ _ _ _ => trivial,
    fun q k hq _ _ _ => hq.insert k, ?_, fun h => hInf (h true ((rootIff true).2 rfl)),
    fun k _ => ⟨{k}, Set.finite_singleton k, rfl⟩, ?_, ?_⟩
  · intro x k hAdm _ _ hNo
    cases x with
    | true => exact (hInf hAdm).elim
    | false => exact (hNo ⟨{k}, Set.finite_singleton k, fun _ hd => hd.elim, rfl⟩).elim
  · intro r hr d ⟨_, q, hq, hSub, _⟩
    rw [rootIff] at hr
    subst hr
    exact hInf (hq.subset hSub)
  · intro h
    exact Nat.not_succ_le_zero 0 (h true ((rootIff true).2 rfl) 0 trivial)

theorem impureLimitsOf (src : Set Determination) (L : Bool → Prop)
    (h : ∀ d ∈ src, isPure d) : impureLimits src L := by
  intro x d hd hImp
  cases x with
  | false => exact (hImp (effectPure d hd)).elim
  | true => exact (hImp (h d hd)).elim

theorem limitsEsseOpen (src : Set Determination) (L : Bool → Prop) :
    limitsEsse openProfile src L :=
  fun _ k hAdm hk _ hNo => (hNo (openCompatible _ k hAdm hk)).elim

theorem giverNoLimit : giver noLimit := fun _ _ h => h.elim

theorem esseControls : EsseControls := by
  refine ⟨⟨giverNoLimit, impureLimitsOf _ _ fun _ h => h, limitsEsseOpen _ _⟩,
    ⟨giverNoLimit, impureLimitsOf _ _ positivePure, limitsEsseOpen _ _⟩,
    ⟨giverNoLimit, impureLimitsOf _ _ positivePure, fun h => ?_⟩,
    ⟨giverNoLimit, fun h => ?_, fun h => ?_⟩,
    ⟨fun h => ?_, ?_, ?_⟩, ⟨giverNoLimit, ?_⟩, ?_⟩
  · obtain ⟨p, hp, hn, _⟩ := jointConflictPairwise Determination.noesis (by simp [memPure])
      Determination.noesis (by simp [memPure])
    exact h true Determination.noesis jointPositive (by simp [isPure, memPure]) ⟨p, hp, hn⟩
      jointExcludes
  · exact h true Determination.limiter (by simp [has, limitedMode]) limiterImpure
  · exact h true Determination.noesis profileComparisons.2.2.2.1.1 (by simp [isPure, memPure])
      ⟨effect, effectFinite, by simp [effect]⟩ profileComparisons.2.2.2.1.2.2.2
  · obtain ⟨g, _, hc, _⟩ := h true ((rootIff true).2 rfl).1 rfl
    exact hc
  · intro x d hd hImp
    cases x with
    | false => exact (hImp (effectPure d hd)).elim
    | true => rfl
  · intro x k hAdm hk _ hNo
    cases x with
    | true => rfl
    | false =>
      exact (hNo ⟨insert k effect, finiteCompatible _ k effectFinite (by simp [effect]) hk,
        Set.subset_insert _ _, Set.mem_insert _ _⟩).elim
  · intro x k hAdm _ hkAdm hNo
    obtain ⟨q, hq, hkq⟩ := hkAdm
    refine (hNo ⟨ActualProfile (has positive) x, hAdm, subset_refl _, ?_⟩).elim
    unfold exactClosure at hAdm hq
    rw [hAdm]
    rw [hq] at hkq
    exact hkq
  · intro x k hAdm _ _ hNo
    cases x with
    | true => exact (Set.Ici_infinite 1 hAdm).elim
    | false => exact (hNo ⟨{k}, Set.finite_singleton k, fun _ hd => hd.elim, rfl⟩).elim

theorem standingRival : StandingRival := by
  refine ⟨TruthCore.Results.Causality.IntentionalExemplarExtension.ObjectiveEminence.controls.1,
    fun _ _ _ _ h => Or.inl h, (fun _ h => by cases h), (fun _ h => by cases h.1), ?_,
    (rootsIff False).2 not_false, purityOf _ _ fun _ => positivePure, extendOpen,
    limitsOpen _ _, rootAdmOf _ _ profileComparisons.2.2.1.1, pureAdmOpen,
    unexplainedPositive, by simp [has, personal], ?_, fun h => ?_⟩
  · intro x
    cases x <;> simp [has, positive, effect,
      TruthCore.Causality.IntentionalExemplarExtension.Control.effectOnly]
  · exact ⟨by simp [has, personal], openCompatible personal _ (by simp [openProfile, personal])
      (by simp [isPure, memPure])⟩
  · exact h true ((rootIff true).2 rfl) Determination.a
      ⟨by simp [has, personal], openCompatible personal _ (by simp [openProfile, personal])
        (by simp [isPure, memPure])⟩

end Controls

end TruthCore.Results.Causality.RootPerfectionExclusion
