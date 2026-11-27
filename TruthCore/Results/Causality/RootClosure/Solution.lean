module

public import TruthCore.Causality.RootClosure
public import TruthCore.Results.Causality.RootPerfectionExclusion.Solution

@[expose] public section

namespace TruthCore.Results.Causality.RootClosure

open TruthCore.Causality.RootClosure
open TruthCore.Causality.RootClosure.Control
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion
  (ActualProfile UnexplainedAbsence NoUnexplainedAbsenceAtRoots)
open TruthCore.Causality.RootPerfectionIntellect (AdmissibleIsExclusionFree PureRequiresNoPureLack)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.SourceIntellectControls (HasCompatibleExtension)

/-! ## A. E from essence-grounded modality with positive essences -/

/-- E from N, EM and EP. Fix an actual root `r` at `w` and a determination `d`
that `r` lacks while some admissible `q` contains all of `r`'s determinations
and `d` (case iii). EP makes every essential condition on `r`'s profile hold of
`q`, so EM gives an accessible world at which `r` has every member of `q`, in
particular `d`. N then gives `r` the determination `d` at `w`, a contradiction.
No case analysis and no axioms. -/
theorem noUnexplainedAbsenceFromPositiveEssence {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (hN : RootAbsencesNecessary m w HasAt)
    (hEM : EssenceGroundedRootProfileModality m w Ess HasAt)
    (hEP : RootEssentialConditionsPositive m w Admissible Ess HasAt) :
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) := by
  intro r hr d ⟨hLack, q, hq, hsub, hd⟩
  obtain ⟨v, hv, hqv⟩ := hEM r hr q (fun y C hC => hEP r hr y C hC q hq hsub)
  exact hLack (hN r hr v hv d (hqv hd))

/-- EP from LE and the necessity direction of member grounding (`89c988d9`).
For an admissible extension `q` of an actual root's profile, the necessity
direction makes `q` exclusion-free: no member of `q`, and so no determination of
the root, requires the lack of a subset of `q`. LE then gives every essential
condition at `q`. No axioms. -/
theorem positiveEssenceFromCarriage {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    RootEssentialConditionsPositive m w Admissible Ess HasAt :=
  fun r hr y C hC q hq hsub =>
    hLE r hr y C hC q hq hsub (fun t ht S hS => hMG q hq t (hsub ht) S hS)

/-- EP gives LE: the strength order of the two (EP drops LE's hypothesis). -/
theorem carriedOfPositive {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hEP : RootEssentialConditionsPositive m w Admissible Ess HasAt) :
    RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack :=
  fun r hr y C hC q hq hsub _ => hEP r hr y C hC q hq hsub

/-! ## Lean-only diagnostics -/

/-- Under EM and EP an unexplained absence is a contingent one: the root has
the missing determination at some accessible world. So case (iii) together
with N is excluded by EM and EP, and case (iii) without N lies inside the scope
of a contingent-fact PSR. -/
theorem unexplainedAbsenceIsContingent {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (hEM : EssenceGroundedRootProfileModality m w Ess HasAt)
    (hEP : RootEssentialConditionsPositive m w Admissible Ess HasAt) :
    ∀ r, ActualRoot m w r → ∀ d, UnexplainedAbsence Admissible (HasAt w) r d →
      ∃ v, m.ontic.frame.access w v ∧ HasAt v r d := by
  intro r hr d ⟨_, q, hq, hsub, hd⟩
  obtain ⟨v, hv, hqv⟩ := hEM r hr q (fun y C hC => hEP r hr y C hC q hq hsub)
  exact ⟨v, hv, hqv hd⟩

/-- The relocation converse: E and factivity of essential conditions give EP.
E makes every admissible profile that contains an actual root's profile equal
to that profile (a further member would be an unexplained absence), and
factivity gives each essential condition there. Admissibility of the root's
profile is not needed. So under N, EM and factivity, EP and E are equivalent. -/
theorem positivityOfNoUnexplainedAbsence {W B D : Type}
    (m : Profile W B) (w : W) (Admissible : Set D → Prop)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (hE : NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w))
    (hFact : RootEssentialConditionsFactive m w Ess HasAt) :
    RootEssentialConditionsPositive m w Admissible Ess HasAt := by
  intro r hr y C hC q hq hsub
  have hEq : q = ActualProfile (HasAt w) r := by
    apply Set.Subset.antisymm _ hsub
    intro d hd
    by_contra hn
    exact hE r hr d ⟨hn, q, hq, hsub, hd⟩
  exact hEq ▸ hFact r hr y C hC

/-- A carried closure at an actual root contradicts strict purity of root
determinations (`3b39e0ba`) and the purity of requirements (`0c8631bd`): no
determination of an actual root requires the lack of pure determinations. -/
theorem closureCarrierExcludedAtRoots {W B D : Type}
    (m : Profile W B) (w : W) (Has : B → D → Prop) (Pure : D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hRootPure : ActualRootDeterminationsArePure m w Has Pure)
    (hReq : PureRequiresNoPureLack RequiresLack Pure) :
    ∀ r, ActualRoot m w r → ∀ t, Has r t → ∀ S, (∀ e ∈ S, Pure e) → ¬ RequiresLack t S :=
  fun r hr t ht S hS => hReq t S (hRootPure r hr t ht) hS

/-- Under the necessity direction of member grounding, a determination of the
bearer that requires the lack of a subset of its profile with `k` added makes
the absence of `k` not unexplained: every profile containing the bearer's
determinations and `k` is inadmissible (case i or ii). -/
theorem carriedClosureNotUnexplained {B D : Type} (Admissible : Set D → Prop)
    (RequiresLack : D → Set D → Prop) (Has : B → D → Prop) (x : B) (k t : D)
    (S : Set D) (hMG : AdmissibleIsExclusionFree Admissible RequiresLack)
    (ht : Has x t) (hS : S ⊆ insert k (ActualProfile Has x)) (hReq : RequiresLack t S) :
    ¬ UnexplainedAbsence Admissible Has x k := by
  rintro ⟨_, q, hq, hsub, hk⟩
  have hS' : S ⊆ q := fun e he => by
    rcases Set.mem_insert_iff.mp (hS he) with h | h
    · exact h ▸ hk
    · exact hsub h
  exact hMG q hq t (hsub ht) S hS' hReq

section Truthmakers

open TruthCore.Explanation.PSRStrength (Arena Access)
open TruthCore.Explanation.TruthmakerTheories (Making Sound MakerNecessitation NeedsMakerAt)

/-- Truthmaker necessitation does not discriminate makers of a necessary fact.
If `f` holds at every world accessible from `w` and `b` exists at `w`, the
making relation "`b` makes `f` true at `w`" is sound, gives `f` its needed
maker at `w`, and necessitates `f`. Any existent, the root itself included,
is such a maker; choosing the root's determinations as the relevant maker needs
a relevance constraint, which is LE in truthmaker form. -/
theorem necessaryFactAnyMaker {W B F : Type} (A : Arena W B F) (w : W) (b : B) (f : F)
    (hb : A.ontic.ExistsAt w b) (hf : ∀ v, Access A w v → A.holds v f) (hw : A.holds w f) :
    let M : Making W B F := fun u c g => u = w ∧ c = b ∧ g = f
    Sound A M ∧ NeedsMakerAt A M w f ∧ MakerNecessitation A M := by
  intro M
  refine ⟨⟨?_, ?_⟩, fun _ => ⟨b, rfl, rfl, rfl⟩, ?_⟩
  · rintro u c g ⟨rfl, rfl, rfl⟩; exact hw
  · rintro u c g ⟨rfl, rfl, rfl⟩; exact hb
  · rintro u c g ⟨rfl, rfl, rfl⟩ v hv _; exact hf v hv

end Truthmakers


/-! ## Finite controls -/

section Controls

local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.SourceIntellectControls.ProfileControls hiding pure
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff memPure)

theorem openSubPure (q : Set Determination) (hq : openProfile q) : q ⊆ pureSet := by
  intro d hd
  rw [memPure]
  rintro rfl
  exact hq.2 hd

theorem openNoNoesisSubPositive (q : Set Determination) (hq : openProfile q)
    (hn : Determination.noesis ∉ q) : q ⊆ positive := by
  intro d hd
  cases d <;> simp_all [positive, openProfile]

theorem pureOpen' : openProfile pureSet := by simp [openProfile, memPure]

theorem positiveOpen : openProfile positive := by simp [openProfile, positive]

theorem positiveSubPure : positive ⊆ pureSet := by
  intro d hd; simp [positive] at hd; rcases hd with rfl | rfl | rfl <;> simp [memPure]

theorem noesisPure : Determination.noesis ∈ pureSet := by simp [memPure]
theorem noesisNotPositive' : Determination.noesis ∉ positive := by simp [positive]

theorem nOf (s t : Set Determination) (h : t ⊆ s) : cN s t := by
  intro r hr v _ d hd
  rw [rootIff] at hr; subst hr
  cases v
  · exact h hd
  · exact hd

theorem notN : ¬ cN positive pureSet := by
  intro h
  have := h true ((rootIff true).2 rfl) false trivial Determination.noesis noesisPure
  exact noesisNotPositive' this

theorem emOpen (s t : Set Determination) (ht : pureSet ⊆ t) : cEM essOpen s t := by
  intro r hr q hq
  rw [rootIff] at hr; subst hr
  have hqo : openProfile q := (hq true openProfile ⟨rfl, rfl, rfl⟩ :)
  exact ⟨false, trivial, fun d hd => ht (openSubPure q hqo hd)⟩

theorem notEMOpen : ¬ cEM essOpen positive positive := by
  intro h
  obtain ⟨v, _, hv⟩ := h true ((rootIff true).2 rfl) pureSet (by
    rintro y C ⟨-, -, rfl⟩; exact pureOpen')
  have := hv noesisPure
  cases v <;> exact noesisNotPositive' this

theorem emNeg : cEM essNeg positive positive := by
  intro r hr q hq
  rw [rootIff] at hr; subst hr
  have hqo : openProfile q := hq true openProfile ⟨rfl, rfl, Or.inl rfl⟩
  have hqn : noNoesis q := hq true noNoesis ⟨rfl, rfl, Or.inr rfl⟩
  exact ⟨true, trivial, openNoNoesisSubPositive q hqo hqn⟩

theorem epOpen (s t : Set Determination) : cEP essOpen s t := by
  rintro r - y C ⟨-, -, rfl⟩ q hq -
  exact hq

theorem notEPNeg (s t : Set Determination) (hs : s ⊆ pureSet) : ¬ cEP essNeg s t := by
  intro h
  exact h true ((rootIff true).2 rfl) true noNoesis ⟨rfl, rfl, Or.inr rfl⟩ pureSet pureOpen'
    hs noesisPure

theorem eOf (s t : Set Determination) (h : pureSet ⊆ s) : cE s t := by
  rintro r hr d ⟨hLack, q, hq, hsub, hd⟩
  rw [rootIff] at hr; subst hr
  exact hLack (h (openSubPure q hq hd))

theorem notEPositive (t : Set Determination) : ¬ cE positive t := by
  intro h
  exact h true ((rootIff true).2 rfl) Determination.noesis
    ⟨noesisNotPositive', pureSet, pureOpen', positiveSubPure, noesisPure⟩

/-- Comparator companion of `noUnexplainedAbsenceFromPositiveEssence`. On one
carrier (open family, the source the only actual root), each row lists N, EM,
EP and E:
1. positive witness: the source has every pure determination at both worlds,
   its nature imposes only admissibility; all four hold;
2. N fails: the source lacks `noesis` actually and has it at the other world
   (a contingent lack); EM and EP hold, E fails;
3. EM fails: the source lacks `noesis` at both worlds and its nature imposes
   only admissibility (a necessary lack that no nature grounds: modal
   primitivism or brutalism); N and EP hold, E fails;
4. EP fails: the same profile, and its nature also contains the negative clause
   "lacks `noesis`" (the rival's negative essence); N and EM hold, E fails. -/
theorem essenceControls :
    (cN pureSet pureSet ∧ cEM essOpen pureSet pureSet ∧ cEP essOpen pureSet pureSet ∧
      cE pureSet pureSet) ∧
    (¬ cN positive pureSet ∧ cEM essOpen positive pureSet ∧ cEP essOpen positive pureSet ∧
      ¬ cE positive pureSet) ∧
    (cN positive positive ∧ ¬ cEM essOpen positive positive ∧
      cEP essOpen positive positive ∧ ¬ cE positive positive) ∧
    (cN positive positive ∧ cEM essNeg positive positive ∧
      ¬ cEP essNeg positive positive ∧ ¬ cE positive positive) :=
  ⟨⟨nOf _ _ subset_rfl, emOpen _ _ subset_rfl, epOpen _ _, eOf _ _ subset_rfl⟩,
    ⟨notN, emOpen _ _ subset_rfl, epOpen _ _, notEPositive _⟩,
    ⟨nOf _ _ subset_rfl, notEMOpen, epOpen _ _, notEPositive _⟩,
    ⟨nOf _ _ subset_rfl, emNeg, notEPNeg _ _ positiveSubPure, notEPositive _⟩⟩

theorem leOpen (s t : Set Determination) (req : Determination → Set Determination → Prop) :
    cLE essOpen s t req := by
  rintro r - y C ⟨-, -, rfl⟩ q hq - -
  exact hq

theorem notLENeg : ¬ cLE essNeg positive positive noReq := by
  intro h
  exact h true ((rootIff true).2 rfl) true noNoesis ⟨rfl, rfl, Or.inr rfl⟩ pureSet pureOpen'
    positiveSubPure (fun _ _ _ _ h => h) noesisPure

theorem leCarried : cLE essNeg positive positive aExcludesNoesis := by
  rintro r hr y C ⟨-, -, hC | hC⟩ q hq hsub hfree
  · subst hC; exact hq
  · subst hC
    rw [rootIff] at hr; subst hr
    intro hn
    exact hfree Determination.a (by simp [hasAt, positive]) {Determination.noesis}
      (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl⟩

theorem mgNoReq : AdmissibleIsExclusionFree openProfile noReq :=
  fun _ _ _ _ _ _ h => h

theorem notMGCarried : ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis := by
  intro h
  exact h pureSet pureOpen' Determination.a (by simp [memPure]) {Determination.noesis}
    (Set.singleton_subset_iff.mpr noesisPure) ⟨rfl, rfl⟩

theorem notPureReqCarried :
    ¬ PureRequiresNoPureLack aExcludesNoesis
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure := by
  intro h
  refine h Determination.a {Determination.noesis} (by
    simp [TruthCore.Causality.RootPerfectionExclusion.Control.isPure, memPure]) ?_ ⟨rfl, rfl⟩
  intro e he
  rw [Set.mem_singleton_iff.mp he]
  simp [TruthCore.Causality.RootPerfectionExclusion.Control.isPure, memPure]

/-- Comparator companion of `positiveEssenceFromCarriage` and
`carriedOfPositive`. Same carrier, the source lacking `noesis` at both worlds
except in row 1. Each row lists LE, the necessity direction of member
grounding, and EP:
1. positive witness: only admissibility is essential and nothing requires a
   lack; all three hold (source with every pure determination);
2. LE fails: the negative clause "lacks `noesis`" is carried by no determination
   (nothing requires a lack); the necessity direction holds, EP fails. This is
   the rival's non-determinative closure;
3. the necessity direction fails: the clause is carried by the pure `a`, which
   requires the lack of `noesis`, but the family still admits `pure`; LE holds
   and EP fails (so EP is strictly stronger than LE). Here `a`, a pure
   determination, requires the lack of the pure `noesis`, so the purity of
   requirements (`0c8631bd`) fails too: a carried closure of a pure
   determination is what that premise excludes. N and EM hold in this row and
   E fails, so carriage with N and EM, without the necessity direction, does
   not give E. -/
theorem carriageControls :
    (cLE essOpen pureSet pureSet noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      cEP essOpen pureSet pureSet) ∧
    (¬ cLE essNeg positive positive noReq ∧ AdmissibleIsExclusionFree openProfile noReq ∧
      ¬ cEP essNeg positive positive) ∧
    (cLE essNeg positive positive aExcludesNoesis ∧
      ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧
      ¬ cEP essNeg positive positive ∧
      ¬ PureRequiresNoPureLack aExcludesNoesis
        TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
      cN positive positive ∧ cEM essNeg positive positive ∧ ¬ cE positive positive) :=
  ⟨⟨leOpen _ _ _, mgNoReq, epOpen _ _⟩,
    ⟨notLENeg, mgNoReq, notEPNeg _ _ positiveSubPure⟩,
    ⟨leCarried, notMGCarried, notEPNeg _ _ positiveSubPure, notPureReqCarried,
      nOf _ _ subset_rfl, emNeg, notEPositive _⟩⟩

end Controls

end TruthCore.Results.Causality.RootClosure
