module

public import TruthCore.Causality.RootPerfectionIntellect
public import TruthCore.Results.Causality.WholePowerPerfection.Solution
public import TruthCore.Results.Causality.ActualAncestralSource.Solution
public import TruthCore.Results.Causality.RootPerfectionExclusion.Solution

@[expose] public section

namespace TruthCore.Results.Causality.RootPerfectionIntellect

open TruthCore.Causality.RootPerfectionIntellect
open TruthCore.Causality.RootPerfectionIntellect.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPurity (ActualRootsWithoutLimitingPrinciple)
open TruthCore.Causality.PureActRoot
  (ActualRootHasEveryPureDetermination ActualRootDeterminationsArePure)
open TruthCore.Causality.WholePowerPerfection (UnlimitedIsOwnBeing)
open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
  (WisdomSelfCapacity SelfCapacityExercisedOrPotent TrueSelfApprehensionGrounded
    IntrinsicSelfKnowledge)
open TruthCore.Causality.NecessaryFirstBeing (NecessaryActualFirstPureActAt)
open TruthCore.Causality.ActualAncestralSource (GodReachesActualConcreta)
open TruthCore.Causality.RootPerfectionExclusion
  (ActualProfile RootProfilesAdmissible PureExtensionsAdmissible PureDeterminationsAdmissible)
open TruthCore.Causality.RootPerfectionExclusion.Control (roots has isPure)
open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination PairwiseAdmitted effect)
open TruthCore.Case.Catholicism (GodHasIntellect)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

/-! ## A. From every pure perfection to intellect -/

/-- Step one. At an actual root without a represented limiting principle
(`a30c5963`), the open `UnlimitedIsOwnBeing` makes the root its own being.
Every pure perfection at actual roots (`fe67d766`) and the purity of `wisdom`
give the root `wisdom`. The three open WisdomSelfUnderstanding bridges and the
root's pure act then give intrinsic self-knowledge. The proof is the existing
`actualRootSelfKnowledgeFromWisdom`, unchanged. The whole-power premises of the
q.4 a.2 route (`d164b1ff`, `c4fb87a6`) are not used: `fe67d766` replaces
them, so any producer of `fe67d766` feeds this step. -/
theorem pureActRootsKnowThemselvesFromPurity {W B P D C R : Type}
    (m : Profile W B) (w : W) (Composite : B → Prop) (PriorSimply : B → B → Prop)
    (essenceOf esseOf : B → P) (OwnBeing : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) (wisdom : D) (About Correct : C → B → Prop)
    (CanApprehend Apprehends CognitivelyGrounded : B → C → Prop)
    (InPotency : B → R → Prop) (understanding : R)
    (hNoLimits : ActualRootsWithoutLimitingPrinciple m w Composite PriorSimply essenceOf esseOf)
    (hOwn : UnlimitedIsOwnBeing Composite PriorSimply essenceOf esseOf OwnBeing)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPureWisdom : WisdomIsPure Pure wisdom)
    (hSelfCapacity : WisdomSelfCapacity OwnBeing Has wisdom About Correct CanApprehend)
    (hExercise : SelfCapacityExercisedOrPotent OwnBeing About CanApprehend Apprehends
      InPotency understanding)
    (hGrounding : TrueSelfApprehensionGrounded OwnBeing About Correct Apprehends
      CognitivelyGrounded) :
    PureActRootsKnowThemselves m w About Correct Apprehends CognitivelyGrounded InPotency :=
  fun r hr hPure =>
    TruthCore.Results.Causality.WholePowerPerfection.actualRootSelfKnowledgeFromWisdom
      m w Composite PriorSimply essenceOf esseOf OwnBeing Has Pure wisdom About Correct
      CanApprehend Apprehends CognitivelyGrounded InPotency understanding hNoLimits hOwn
      hEvery hPureWisdom hSelfCapacity hExercise hGrounding r hr hPure

/-- Step two. Some actual first root at `w` is PURE_ACT_1 (`593d7307`). Finite
grounding reach (`75974d26`) makes every GOD_4 that same root
(`namedRootOfReach`). Step one gives it intrinsic self-knowledge, and the open
recognition bridge gives HAS_INTELLECT_1. -/
theorem godHasIntellectFromRootPerfection {W B C R : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (InPotency : B → R → Prop) (IsGod HasIntellect : B → Prop)
    (About Correct : C → B → Prop) (Apprehends CognitivelyGrounded : B → C → Prop)
    (hFirst : NecessaryActualFirstPureActAt m w PriorSimply InPotency)
    (hReach : GodReachesActualConcreta m w IsGod)
    (hKnow : PureActRootsKnowThemselves m w About Correct Apprehends CognitivelyGrounded
      InPotency)
    (hRecognition : GodIntrinsicSelfKnowledgeIsIntellect IsGod HasIntellect About Correct
      Apprehends CognitivelyGrounded) :
    GodHasIntellect IsGod HasIntellect := by
  intro g hg
  obtain ⟨n, hn, _, _, hPure⟩ := hFirst
  have hIdentity : g = n :=
    TruthCore.Results.Causality.ActualAncestralSource.namedRootOfReach m w IsGod hReach g n hg hn
  subst hIdentity
  exact hRecognition g hg (hKnow g hn hPure)

/-! ## B. Constitutive admissibility

The registered derivations use only the sufficiency direction
`ExclusionFreeAdmissible`. Under it and `PureRequiresNoPureLack` every profile of
pure determinations is admissible, so the conclusions hold with room to spare.
`premisesIffStructural` and `sufficiencyPremisesIffAllPure` show what the premise
pairs amount to once the requirement relation is free: they relocate joint
compossibility into requirement form; they add no structural content beyond
downward closure (member grounding) and the localization of incompatibility in a
member, which lives in the intended reading of `RequiresLack`. -/

/-- Exclusion-freedom is inherited by subsets. -/
theorem exclusionFreeMono {D : Type} (RequiresLack : D → Set D → Prop) {p q : Set D}
    (hpq : p ⊆ q) (hq : ExclusionFree RequiresLack q) : ExclusionFree RequiresLack p :=
  fun d hd S hS => hq d (hpq hd) S (hS.trans hpq)

/-- Member grounding (strong) gives its sufficiency direction (weak). -/
theorem exclusionFreeAdmissibleOfMemberGrounding {D : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hGround : MemberGroundedAdmissibility Admissible RequiresLack) :
    ExclusionFreeAdmissible Admissible RequiresLack := fun q => (hGround q).2

/-- Under the two premises every profile of pure determinations is admissible. -/
theorem allPureAdmissible {D : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure) (q : Set D) (hq : ∀ d ∈ q, Pure d) :
    Admissible q :=
  hSuff q fun d hd S hS => hPure d S (hq d hd) (fun e he => hq e (hS he))

/-- Joint compossibility `500d0e2d` from the sufficiency direction and the
purity premise. The insertion law's admissibility hypotheses are not used. -/
theorem jointCompossibilityOfExclusionFreeAdmissibility {D : Type}
    (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure) :
    PureExtensionsAdmissible Admissible Pure := by
  intro q k _ hAll hk _
  apply allPureAdmissible Admissible RequiresLack Pure hSuff hPure
  intro d hd
  rcases Set.mem_insert_iff.mp hd with rfl | h
  · exact hk
  · exact hAll d h

/-- Admissibility of each pure determination `ee287fd3`: its singleton is
exclusion-free. -/
theorem pureAdmissibleOfExclusionFreeAdmissibility {D : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure) :
    PureDeterminationsAdmissible Admissible Pure := fun k hk =>
  ⟨{k}, allPureAdmissible Admissible RequiresLack Pure hSuff hPure {k}
    (fun _ hd => (Set.mem_singleton_iff.mp hd) ▸ hk), Set.mem_singleton k⟩

/-- Admissibility of each actual root's profile `0a9d3a40`, given that every
determination of an actual root is pure (`3b39e0ba`). -/
theorem rootProfilesAdmissibleOfExclusionFreeAdmissibility {W B D : Type} (m : Profile W B)
    (w : W) (Admissible : Set D → Prop) (RequiresLack : D → Set D → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hSuff : ExclusionFreeAdmissible Admissible RequiresLack)
    (hPure : PureRequiresNoPureLack RequiresLack Pure)
    (hRootPure : ActualRootDeterminationsArePure m w Has Pure) :
    RootProfilesAdmissible m w Admissible Has := fun r hr =>
  allPureAdmissible Admissible RequiresLack Pure hSuff hPure _ (fun d hd => hRootPure r hr d hd)

/-- With the requirement relation free, member grounding and the purity
premise together say exactly: the family is downward closed, contains the empty
profile, and contains every all-pure profile. (Reviewer probe, registered as a
Lean-only lemma.) -/
theorem premisesIffStructural {D : Type} (Admissible : Set D → Prop) (Pure : D → Prop) :
    (∃ RL : D → Set D → Prop, MemberGroundedAdmissibility Admissible RL ∧
        PureRequiresNoPureLack RL Pure) ↔
      ((∀ p q, p ⊆ q → Admissible q → Admissible p) ∧ Admissible ∅ ∧
        ∀ q, (∀ d ∈ q, Pure d) → Admissible q) := by
  constructor
  · rintro ⟨RL, hG, hP⟩
    refine ⟨fun p q hpq hq => (hG p).2 (exclusionFreeMono RL hpq ((hG q).1 hq)),
      (hG ∅).2 (fun d hd => absurd hd (Set.notMem_empty d)),
      fun q hq => allPureAdmissible Admissible RL Pure
        (exclusionFreeAdmissibleOfMemberGrounding Admissible RL hG) hP q hq⟩
  · rintro ⟨hDown, hEmpty, hAll⟩
    refine ⟨fun d S => ¬ Admissible (insert d S), fun q => ⟨?_, ?_⟩, ?_⟩
    · intro hq d hd S hS hR
      exact hR (hDown _ q (Set.insert_subset hd hS) hq)
    · intro hEF
      by_cases hne : q.Nonempty
      · obtain ⟨d, hd⟩ := hne
        have h1 : ¬¬Admissible (insert d q) := hEF d hd q (subset_refl q)
        rw [Set.insert_eq_of_mem hd] at h1
        exact Classical.byContradiction h1
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact hEmpty
    · intro d S hd hS hR
      apply hR
      apply hAll
      intro e he
      rcases Set.mem_insert_iff.mp he with rfl | h
      · exact hd
      · exact hS e h

/-- With the requirement relation free, the sufficiency direction and the purity
premise together say exactly: every all-pure profile is admissible. -/
theorem sufficiencyPremisesIffAllPure {D : Type} (Admissible : Set D → Prop)
    (Pure : D → Prop) :
    (∃ RL : D → Set D → Prop, ExclusionFreeAdmissible Admissible RL ∧
        PureRequiresNoPureLack RL Pure) ↔
      ∀ q, (∀ d ∈ q, Pure d) → Admissible q := by
  constructor
  · rintro ⟨RL, hS, hP⟩
    exact allPureAdmissible Admissible RL Pure hS hP
  · intro hAll
    refine ⟨fun d S => ¬ Admissible (insert d S), ?_, ?_⟩
    · intro q hEF
      by_cases hne : q.Nonempty
      · obtain ⟨d, hd⟩ := hne
        have h1 : ¬¬Admissible (insert d q) := hEF d hd q (subset_refl q)
        rw [Set.insert_eq_of_mem hd] at h1
        exact Classical.byContradiction h1
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        exact hAll ∅ (fun d hd => absurd hd (Set.notMem_empty d))
    · intro d S hd hS hR
      apply hR
      apply hAll
      intro e he
      rcases Set.mem_insert_iff.mp he with rfl | h
      · exact hd
      · exact hS e h

/-- Finite converse: under member grounding and admissibility of each pure
determination, joint compossibility gives the purity premise for every FINITE
set of pure determinations. (Reviewer probe, registered as a Lean-only lemma.) -/
theorem finiteConverse {D : Type} (Admissible : Set D → Prop)
    (RL : D → Set D → Prop) (Pure : D → Prop)
    (hG : MemberGroundedAdmissibility Admissible RL)
    (hPDA : PureDeterminationsAdmissible Admissible Pure)
    (hJ : PureExtensionsAdmissible Admissible Pure)
    (d : D) (S : Set D) (hS : S.Finite) (hd : Pure d) (hSP : ∀ e ∈ S, Pure e) :
    ¬ RL d S := by
  have hSingle : Admissible {d} := by
    obtain ⟨q, hq, hdq⟩ := hPDA d hd
    exact (hG _).2 (exclusionFreeMono RL (Set.singleton_subset_iff.mpr hdq) ((hG q).1 hq))
  have key : ∀ T : Set D, T.Finite → T ⊆ S → Admissible (insert d T) := by
    intro T hT
    refine Set.Finite.induction_on _ hT ?_ ?_
    · intro _; simpa using hSingle
    · intro a T _ _ ih hsub
      have hT' : T ⊆ S := fun x hx => hsub (Set.mem_insert_of_mem a hx)
      have hA := ih hT'
      have : insert a (insert d T) = insert d (insert a T) := Set.insert_comm a d T
      rw [← this]
      refine hJ _ a hA ?_ (hSP a (hsub (Set.mem_insert a T)))
        (hPDA a (hSP a (hsub (Set.mem_insert a T))))
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | h
      · exact hd
      · exact hSP x (hT' h)
  have hA := key S hS (subset_refl S)
  exact (hG _).1 hA d (Set.mem_insert d S) S (Set.subset_insert d S)

/-! ## Finite controls -/

section Controls

open TruthCore.Causality.RootPerfectionExclusion.Control (composite prior rep)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff limitingIff rootsIff)

theorem ownUnlimitedIff (c o : Prop) : ownUnlimited c o ↔ (¬ c → o) := by
  constructor
  · intro h hc
    exact (h true (fun hl => hc (((limitingIff c true).1 hl).elim (fun h => h.2)
      (fun h => Bool.noConfusion h)))).2
  · intro h x hx
    cases x with
    | false => exact (hx ((limitingIff c false).2 (Or.inr rfl))).elim
    | true => exact ⟨rfl, h (fun hc => hx ((limitingIff c true).2 (Or.inl ⟨rfl, hc⟩)))⟩

theorem everyIff (h p : Prop) : every h p ↔ (p → h) := by
  constructor
  · intro hE hp
    exact (hE true ((rootIff true).2 rfl) () hp).2
  · intro hE r hr _ hp
    exact ⟨(rootIff r).1 hr, hE hp⟩

theorem capacityIff (o h ca : Prop) : capacity o h ca ↔ (o → h → ca) := by
  constructor
  · intro hC ho hh
    obtain ⟨c, hc, _, hcan⟩ := hC true ⟨rfl, ho⟩ ⟨rfl, hh⟩
    exact hcan.2.2
  · intro hC g hg hw
    obtain ⟨rfl, ho⟩ := hg
    exact ⟨true, rfl, rfl, rfl, rfl, hC ho hw.2⟩

theorem exerciseIff (o ca ap : Prop) : exercise o ca ap ↔ (o → ca → ap) := by
  constructor
  · intro hE ho hca
    rcases hE true true ⟨rfl, ho⟩ rfl ⟨rfl, rfl, hca⟩ with h | h
    · exact h.2.2
    · exact h.2.elim
  · intro hE g c hg _ hcan
    exact Or.inl ⟨hcan.1, hcan.2.1, hE hg.2 hcan.2.2⟩

theorem groundingIff (o ap cg : Prop) : grounding o ap cg ↔ (o → ap → cg) := by
  constructor
  · intro hG ho hap
    exact (hG true true ⟨rfl, ho⟩ rfl rfl ⟨rfl, rfl, hap⟩).2.2
  · intro hG g c hg _ _ hApp
    exact ⟨hApp.1, hApp.2.1, hG hg.2 hApp.2.2⟩

theorem selfKnowledgeIff (ap cg : Prop) (x : Bool) :
    IntrinsicSelfKnowledge about correct (selfIf ap) (selfIf cg) x ↔ (x = true ∧ ap ∧ cg) := by
  constructor
  · rintro ⟨c, _, _, ⟨hx, _, hap⟩, ⟨_, _, hcg⟩⟩
    exact ⟨hx, hap, hcg⟩
  · rintro ⟨rfl, hap, hcg⟩
    exact ⟨true, rfl, rfl, ⟨rfl, rfl, hap⟩, ⟨rfl, rfl, hcg⟩⟩

theorem pureActIff (q : Prop) (x : Bool) : PureAct (potencyIf q) x ↔ (x = true → ¬ q) := by
  constructor
  · intro h hx hq
    exact h () ⟨hx, hq⟩
  · intro h _ hp
    exact h hp.1 hp.2

theorem knowsIff (q ap cg : Prop) : knows q ap cg ↔ (¬ q → ap ∧ cg) := by
  constructor
  · intro h hq
    exact ((selfKnowledgeIff ap cg true).1 (h true ((rootIff true).2 rfl)
      ((pureActIff q true).2 (fun _ => hq)))).2
  · intro h r hr hPure
    obtain rfl := (rootIff r).1 hr
    exact (selfKnowledgeIff ap cg true).2 ⟨rfl, h ((pureActIff q true).1 hPure rfl)⟩

/-- Step one: a positive witness and, for each of its seven premises, an
assignment on the same carrier where that premise fails, the six others hold
and the conclusion fails. The rows vary only which relations are populated.
In the exercise row the source can apprehend its own content, does not, and is
in potency in no respect: this is a model only because `InPotency` is the
independently supplied POTENCY_2. -/
theorem stepOneControls :
    -- positive witness
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      capacity True True True ∧ exercise True True True ∧ grounding True True True ∧
      knows False True True) ∧
    -- `a30c5963` fails: the source is composite and not its own being
    (¬ roots True ∧ ownUnlimited True False ∧ every True True ∧ wisdomPure True ∧
      capacity False True False ∧ exercise False False False ∧ grounding False False False ∧
      ¬ knows False False False) ∧
    -- `26e8e6ed` fails: an unlimited source that is not its own being
    (roots False ∧ ¬ ownUnlimited False False ∧ every True True ∧ wisdomPure True ∧
      capacity False True False ∧ exercise False False False ∧ grounding False False False ∧
      ¬ knows False False False) ∧
    -- `fe67d766` fails: wisdom is pure and the root lacks it
    (roots False ∧ ownUnlimited False True ∧ ¬ every False True ∧ wisdomPure True ∧
      capacity True False False ∧ exercise True False False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- purity fails: wisdom is not pure and the root lacks it
    (roots False ∧ ownUnlimited False True ∧ every False False ∧ ¬ wisdomPure False ∧
      capacity True False False ∧ exercise True False False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- `WisdomSelfCapacity` fails: wisdom without a self-directed capacity
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      ¬ capacity True True False ∧ exercise True False False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- `SelfCapacityExercisedOrPotent` fails: a dormant self-directed capacity
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      capacity True True True ∧ ¬ exercise True True False ∧ grounding True False False ∧
      ¬ knows False False False) ∧
    -- `TrueSelfApprehensionGrounded` fails: correct apprehension without grounding
    (roots False ∧ ownUnlimited False True ∧ every True True ∧ wisdomPure True ∧
      capacity True True True ∧ exercise True True True ∧ ¬ grounding True True False ∧
      ¬ knows False True False) := by
  simp only [rootsIff, ownUnlimitedIff, everyIff, capacityIff, exerciseIff, groundingIff,
    knowsIff, wisdomPure, WisdomIsPure, pureIf]
  simp

theorem reachIff (n : Bool) : reach n ↔ n = true := by
  constructor
  · intro h
    have hPath := h n rfl true ⟨trivial, Or.inl rfl⟩
    rcases Relation.ReflTransGen.cases_tail hPath with h | ⟨c, _, hEdge⟩
    · exact h.symm
    · exact (Bool.noConfusion hEdge.2.2.2.2 : False).elim
  · rintro rfl g hg x _
    subst hg
    cases x with
    | true => exact Relation.ReflTransGen.refl
    | false => exact Relation.ReflTransGen.single ⟨trivial, Or.inl rfl, rfl, rfl, rfl⟩

theorem firstIff (q : Prop) : first q ↔ ¬ q := by
  constructor
  · rintro ⟨n, hn, _, _, hPure⟩
    obtain rfl := (rootIff n).1 hn
    exact (pureActIff q true).1 hPure rfl
  · intro hq
    refine ⟨true, (rootIff true).2 rfl, fun _ _ => Or.inl rfl, ?_,
      (pureActIff q true).2 (fun _ => hq)⟩
    intro y hPrior
    exact (Bool.noConfusion hPrior.2 : False).elim

theorem recognitionIff (n : Bool) (i ap cg : Prop) :
    recognition n i ap cg ↔ (n = true → ap → cg → i) := by
  constructor
  · rintro h rfl hap hcg
    exact (h true rfl ((selfKnowledgeIff ap cg true).2 ⟨rfl, hap, hcg⟩)).2
  · intro h g hg hK
    obtain ⟨hx, hap, hcg⟩ := (selfKnowledgeIff ap cg g).1 hK
    subst hx
    exact ⟨rfl, h hg.symm hap hcg⟩

theorem godIntellectIff (n : Bool) (i : Prop) : godIntellect n i ↔ (n = true ∧ i) := by
  constructor
  · intro h
    exact h n rfl
  · rintro ⟨rfl, hi⟩ g hg
    exact ⟨hg, hi⟩

/-- Step two: a positive witness and, for each of its four premises, an
assignment on the same carrier where that premise fails, the three others hold
and GOD_4 HAS_INTELLECT_1 fails. In the reach row GOD_4 names the effect, which
is not an ancestor of the root. In the first-root row the root is in potency,
so step one holds vacuously. -/
theorem stepTwoControls :
    (first False ∧ reach true ∧ knows False True True ∧ recognition true True True True ∧
      godIntellect true True) ∧
    (¬ first True ∧ reach true ∧ knows True False False ∧ recognition true False False False ∧
      ¬ godIntellect true False) ∧
    (first False ∧ ¬ reach false ∧ knows False True True ∧ recognition false True True True ∧
      ¬ godIntellect false True) ∧
    (first False ∧ reach true ∧ ¬ knows False False False ∧
      recognition true False False False ∧ ¬ godIntellect true False) ∧
    (first False ∧ reach true ∧ knows False True True ∧ ¬ recognition true False True True ∧
      ¬ godIntellect true False) := by
  simp only [firstIff, reachIff, knowsIff, recognitionIff, godIntellectIff]
  simp

theorem exclusionFreeLimiter (q : Set Determination) :
    ExclusionFree limiterExcludesNoesis q ↔
      ¬ (Determination.limiter ∈ q ∧ Determination.noesis ∈ q) := by
  constructor
  · rintro h ⟨hl, hn⟩
    exact h _ hl {Determination.noesis} (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl⟩
  · rintro h d hd S hS ⟨rfl, rfl⟩
    exact h ⟨hd, hS rfl⟩

theorem exclusionFreePair (q : Set Determination) :
    ExclusionFree noesisExcludesPair q ↔ bruteTriple q := by
  constructor
  · rintro h ⟨ha, hb, hn⟩
    refine h _ hn {Determination.a, Determination.b} ?_ ⟨rfl, rfl⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · rintro h d hd S hS ⟨rfl, rfl⟩
    exact h ⟨hS (by simp), hS (by simp), hd⟩

theorem exclusionFreeSelf (q : Set Determination) :
    ExclusionFree noesisSelfExcluding q ↔ noNoesis q := by
  constructor
  · intro h hn
    exact h _ hn {Determination.noesis} (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl⟩
  · rintro h d hd S _ ⟨rfl, rfl⟩
    exact h hd

theorem exclusionFreeNone (q : Set Determination) : ExclusionFree noRequirement q :=
  fun _ _ _ _ h => h

theorem memPure (d : Determination) : isPure d ↔ d ≠ Determination.limiter :=
  TruthCore.Results.Causality.RootPerfectionExclusion.memPure d

theorem purityLimiter : PureRequiresNoPureLack limiterExcludesNoesis isPure := by
  rintro d S hd _ ⟨rfl, rfl⟩
  exact (memPure _).1 hd rfl

theorem purityNone : PureRequiresNoPureLack noRequirement isPure := fun _ _ _ _ h => h

theorem notPurityPair : ¬ PureRequiresNoPureLack noesisExcludesPair isPure := by
  intro h
  refine h Determination.noesis {Determination.a, Determination.b}
    ((memPure _).2 (by decide)) ?_ ⟨rfl, rfl⟩
  intro e he
  rcases he with rfl | rfl <;> exact (memPure _).2 (by decide)

theorem notPuritySelf : ¬ PureRequiresNoPureLack noesisSelfExcluding isPure := by
  intro h
  refine h Determination.noesis {Determination.noesis} ((memPure _).2 (by decide)) ?_ ⟨rfl, rfl⟩
  intro e he
  rw [Set.mem_singleton_iff.mp he]
  exact (memPure _).2 (by decide)

/-- The triple family admits every pure pair (the #1970 pairwise test), so it
is the downward-closed counterpart of the #2153 `jointConflict` family, which
additionally requires `esse` in every profile. -/
theorem bruteTriplePairwise : PairwiseAdmitted bruteTriple := by
  intro x _ y _
  refine ⟨{x, y}, ?_, by simp, by simp⟩
  cases x <;> cases y <;> simp [bruteTriple]

theorem bruteTripleNotJoint : ¬ PureExtensionsAdmissible bruteTriple isPure := by
  intro h
  have hPair : bruteTriple {Determination.a, Determination.b} := by
    rintro ⟨_, _, hn⟩
    simp at hn
  have hTriple := h {Determination.a, Determination.b} Determination.noesis hPair
    (by
      intro d hd
      rcases hd with rfl | rfl <;> exact (memPure _).2 (by decide))
    ((memPure _).2 (by decide)) ⟨{Determination.noesis}, by simp [bruteTriple], rfl⟩
  exact hTriple ⟨by simp, by simp, by simp⟩

theorem noNoesisNotPure : ¬ PureDeterminationsAdmissible noNoesis isPure := by
  intro h
  obtain ⟨q, hq, hn⟩ := h Determination.noesis ((memPure _).2 (by decide))
  exact hq hn

theorem notSuffTriple : ¬ ExclusionFreeAdmissible bruteTriple noRequirement := by
  intro h
  have := h {Determination.a, Determination.b, Determination.noesis} (exclusionFreeNone _)
  exact this ⟨by simp, by simp, by simp⟩

theorem notSuffNoNoesis : ¬ ExclusionFreeAdmissible noNoesis noRequirement := by
  intro h
  exact (h {Determination.noesis} (exclusionFreeNone _)) rfl

/-- A requirement of presence: `noesis` needs the impure `limiter` alongside it.
It is member-grounded for no relation, fails sufficiency with purity for every
relation (the singleton of noesis is all pure and inadmissible), admits each
pure determination somewhere and fails joint compossibility. The failure is
grounded in a member's requirement of presence, not of lack. (Reviewer probe.) -/
theorem presenceRequirement :
    (∀ RL, ¬ MemberGroundedAdmissibility needsLimiter RL) ∧
    ¬ (∃ RL, ExclusionFreeAdmissible needsLimiter RL ∧ PureRequiresNoPureLack RL isPure) ∧
    PureDeterminationsAdmissible needsLimiter isPure ∧
    ¬ PureExtensionsAdmissible needsLimiter isPure := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro RL h
    have hEF := (h {Determination.noesis, Determination.limiter}).1 (fun _ => by simp)
    have := (h {Determination.noesis}).2 (exclusionFreeMono RL (by simp) hEF) rfl
    simp at this
  · intro hEx
    have := (sufficiencyPremisesIffAllPure needsLimiter isPure).1 hEx {Determination.noesis}
      (fun d hd => by
        rw [Set.mem_singleton_iff.mp hd]
        exact (memPure _).2 (by decide)) rfl
    simp at this
  · intro k _
    exact ⟨{k, Determination.limiter}, fun _ => by simp, by simp⟩
  · intro h
    have := h {Determination.esse} Determination.noesis (fun h => by simp at h)
      (fun d hd => by
        rw [Set.mem_singleton_iff.mp hd]
        exact (memPure _).2 (by decide))
      ((memPure _).2 (by decide))
      ⟨{Determination.noesis, Determination.limiter}, fun _ => by simp, by simp⟩
    have hl := this (by simp)
    simp at hl

/-- The #2153 anchoring family (finite profiles of natural numbers) IS
member-grounded, with every determination requiring the lack of every infinite
set; but no requirement relation gives it the sufficiency direction together
with the purity premise when every determination is pure, since the infinite
all-pure profile is inadmissible. (First conjunct: reviewer probe.) -/
theorem anchorFamilyGrounding :
    MemberGroundedAdmissibility TruthCore.Causality.RootPerfectionExclusion.Control.finiteAdmissible
      infiniteLack ∧
    ¬ (∃ RL, ExclusionFreeAdmissible
        TruthCore.Causality.RootPerfectionExclusion.Control.finiteAdmissible RL ∧
      PureRequiresNoPureLack RL TruthCore.Causality.RootPerfectionExclusion.Control.allPure) := by
  refine ⟨?_, ?_⟩
  · intro q
    constructor
    · intro hq d _ S hS hInf
      exact hInf (Set.Finite.subset hq hS)
    · intro hEF
      by_contra hInf
      rcases Set.eq_empty_or_nonempty q with h | ⟨d, hd⟩
      · exact hInf (h ▸ Set.finite_empty)
      · exact hEF d hd q (subset_refl q) hInf
  · intro hEx
    exact Set.infinite_univ ((sufficiencyPremisesIffAllPure _ _).1 hEx Set.univ (fun _ _ => trivial))

theorem rootPureIff (src : Set Determination) : rootPure src ↔ ∀ d ∈ src, isPure d := by
  constructor
  · intro h d hd
    exact h true ((rootIff true).2 rfl) d hd
  · intro h r hr d hd
    obtain rfl := (rootIff r).1 hr
    exact h d hd

theorem rootAdmIff (adm : Set Determination → Prop) (src : Set Determination) :
    rootAdm adm src ↔ adm src := by
  constructor
  · intro h
    exact h true ((rootIff true).2 rfl)
  · intro h r hr
    obtain rfl := (rootIff r).1 hr
    exact h

/-- Constitutive-admissibility controls on the #1970 determinations, stated
for the sufficiency direction `ExclusionFreeAdmissible` that the registered
derivations use. Each row names the requirement relation, the family and which
premise fails:

1. positive witness: only the nonpure `limiter` requires a lack (of `noesis`);
   member grounding (hence sufficiency), the purity premise and joint
   compossibility hold, and the root with every pure determination has an
   admissible profile;
2. the triple family with no requirement: sufficiency fails (an irreducibly
   holistic prohibition), the purity premise holds, joint compossibility fails;
3. the SAME triple family with `noesis` requiring the joint lack of `a` and
   `b`: member grounding and sufficiency hold, the purity premise fails, joint
   compossibility fails;
4. and 5. the family without `noesis`, with no requirement (sufficiency fails)
   or with `noesis` requiring its own lack (purity fails): pure admissibility
   fails;
6. the root's profile with the nonpure `limiter` and `noesis`: member grounding
   and purity hold, root purity and root-profile admissibility fail;
7. the all-pure root profile in the triple family: root purity holds and
   root-profile admissibility fails;
8. strictness: with every profile admissible and `noesis` requiring its own
   lack, sufficiency holds and member grounding fails. -/
theorem constitutiveControls :
    (MemberGroundedAdmissibility (ExclusionFree limiterExcludesNoesis) limiterExcludesNoesis ∧
      ExclusionFreeAdmissible (ExclusionFree limiterExcludesNoesis) limiterExcludesNoesis ∧
      PureRequiresNoPureLack limiterExcludesNoesis isPure ∧
      PureExtensionsAdmissible (ExclusionFree limiterExcludesNoesis) isPure ∧
      rootPure TruthCore.Causality.SourceIntellectControls.ProfileControls.pure ∧
      rootAdm (ExclusionFree limiterExcludesNoesis)
        TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) ∧
    (¬ ExclusionFreeAdmissible bruteTriple noRequirement ∧
      PureRequiresNoPureLack noRequirement isPure ∧
      ¬ PureExtensionsAdmissible bruteTriple isPure) ∧
    (MemberGroundedAdmissibility bruteTriple noesisExcludesPair ∧
      ExclusionFreeAdmissible bruteTriple noesisExcludesPair ∧
      ¬ PureRequiresNoPureLack noesisExcludesPair isPure ∧
      PairwiseAdmitted bruteTriple ∧
      ¬ PureExtensionsAdmissible bruteTriple isPure) ∧
    (¬ ExclusionFreeAdmissible noNoesis noRequirement ∧
      ¬ PureDeterminationsAdmissible noNoesis isPure) ∧
    (ExclusionFreeAdmissible noNoesis noesisSelfExcluding ∧
      ¬ PureRequiresNoPureLack noesisSelfExcluding isPure ∧
      ¬ PureDeterminationsAdmissible noNoesis isPure) ∧
    (ExclusionFreeAdmissible (ExclusionFree limiterExcludesNoesis) limiterExcludesNoesis ∧
      PureRequiresNoPureLack limiterExcludesNoesis isPure ∧
      ¬ rootPure (insert Determination.limiter effect) ∧
      ¬ rootAdm (ExclusionFree limiterExcludesNoesis) (insert Determination.limiter effect)) ∧
    (rootPure TruthCore.Causality.SourceIntellectControls.ProfileControls.pure ∧
      ¬ rootAdm bruteTriple TruthCore.Causality.SourceIntellectControls.ProfileControls.pure) ∧
    (ExclusionFreeAdmissible anyProfile noesisSelfExcluding ∧
      ¬ MemberGroundedAdmissibility anyProfile noesisSelfExcluding) := by
  have hPureAll : ∀ d ∈ TruthCore.Causality.SourceIntellectControls.ProfileControls.pure,
      isPure d := fun d hd => hd
  have hPairMG : MemberGroundedAdmissibility bruteTriple noesisExcludesPair :=
    fun q => (exclusionFreePair q).symm
  have hSelfMG : MemberGroundedAdmissibility noNoesis noesisSelfExcluding :=
    fun q => (exclusionFreeSelf q).symm
  refine ⟨⟨fun _ => Iff.rfl, fun _ h => h, purityLimiter,
      jointCompossibilityOfExclusionFreeAdmissibility _ _ _ (fun _ h => h) purityLimiter,
      (rootPureIff _).2 hPureAll, ?_⟩,
    ⟨notSuffTriple, purityNone, bruteTripleNotJoint⟩,
    ⟨hPairMG, exclusionFreeAdmissibleOfMemberGrounding _ _ hPairMG, notPurityPair,
      bruteTriplePairwise, bruteTripleNotJoint⟩,
    ⟨notSuffNoNoesis, noNoesisNotPure⟩,
    ⟨exclusionFreeAdmissibleOfMemberGrounding _ _ hSelfMG, notPuritySelf, noNoesisNotPure⟩,
    ⟨fun _ h => h, purityLimiter, ?_, ?_⟩,
    ⟨(rootPureIff _).2 hPureAll, ?_⟩,
    ⟨fun _ _ => trivial, ?_⟩⟩
  · rw [rootAdmIff]
    exact allPureAdmissible _ _ isPure (fun _ h => h) purityLimiter _ hPureAll
  · rw [rootPureIff]
    intro h
    exact (memPure _).1 (h Determination.limiter (by simp)) rfl
  · rw [rootAdmIff, exclusionFreeLimiter]
    exact fun h => h ⟨by simp, by simp [effect]⟩
  · rw [rootAdmIff]
    exact fun h => h ⟨by simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.pure],
      by simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.pure],
      by simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.pure]⟩
  · intro h
    exact (h {Determination.noesis}).1 trivial _ rfl {Determination.noesis}
      (subset_refl _) ⟨rfl, rfl⟩

end Controls

end TruthCore.Results.Causality.RootPerfectionIntellect
