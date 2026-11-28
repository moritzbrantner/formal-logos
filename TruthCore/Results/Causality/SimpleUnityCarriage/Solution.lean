module

public import TruthCore.Causality.SimpleUnityCarriage
public import TruthCore.Results.Causality.RootClosure.Solution
public import TruthCore.Results.Explanation.InquiryClosure.Solution

@[expose] public section

namespace TruthCore.Results.Causality.SimpleUnityCarriage

open TruthCore.Causality.SimpleUnityCarriage
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootPerfectionExclusion (ActualProfile NoUnexplainedAbsenceAtRoots)
open TruthCore.Causality.RootPerfectionIntellect (AdmissibleIsExclusionFree PureRequiresNoPureLack)
open TruthCore.Causality.RootClosure (RootEssentialConditionsCarried)
open TruthCore.Explanation.InquiryClosure (RootLacksEssentiallyExcluded)
open TruthCore.Causality.PossibiliaContent (RootsConstitutivelySimple)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)

/-! ## Registered derivations -/

/-- Own-nature carriage from the unity of a simple root (REQUIRES_LACK_1). Fix
an actual root `r`, a condition `C` of its own nature, and an admissible `q`
containing its determinations in which no determination of `r` requires, as
such, the lack of members of `q`. SEAT puts `C` in a real constituent `k`. ESSE
gives `r` a determination `t₀`, and REAL gives it a real constituent `k₀` that
realizes `t₀`. Simplicity identifies `k₀` with `k`, so the seat realizes a
determination of `r`. TRANSFER_1 then gives `C q`. -/
theorem ownCarriageFromUnity {W B D K : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RealConstituent : B → K → Prop)
    (Seat : B → (Set D → Prop) → K → Prop) (Realizes : B → K → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hS : RootsConstitutivelySimple m w RealConstituent)
    (hSeat : RootOwnConditionsSeated m w Ess RealConstituent Seat)
    (hReal : RootDeterminationsRealized m w HasAt RealConstituent Realizes)
    (hEsse : RootsHaveSomeDetermination m w HasAt)
    (hT : RootSeatedExclusionsRequiredAsSuch m w Admissible Ess HasAt RealConstituent Seat
      Realizes RequiresLack) :
    RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack := by
  intro r hr C hC q hq hsub hfree
  obtain ⟨k, hk, hseat⟩ := hSeat r hr C hC
  obtain ⟨t₀, ht₀⟩ := hEsse r hr
  obtain ⟨k₀, hk₀, hreal₀⟩ := hReal r hr t₀ ht₀
  have hkk : k₀ = k := hS r hr k₀ k hk₀ hk
  subst hkk
  exact hT r hr C k₀ hk hseat ⟨t₀, ht₀, hreal₀⟩ q hq hsub (fun t ht _ S hS => hfree t ht S hS)

/-- The relocation converse: at a simple root, own-nature carriage gives
TRANSFER_1 back, given only REAL. A determination of `r` is realized by some
real constituent, which simplicity identifies with the seat; so "no
determination realized by the seat requires a lack within `q`" already says
"no determination of `r` does". With `ownCarriageFromUnity`, under simplicity,
SEAT, REAL and ESSE, TRANSFER_1 and own-nature carriage are equivalent. -/
theorem unityTransferOfOwnCarriage {W B D K : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RealConstituent : B → K → Prop)
    (Seat : B → (Set D → Prop) → K → Prop) (Realizes : B → K → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hS : RootsConstitutivelySimple m w RealConstituent)
    (hReal : RootDeterminationsRealized m w HasAt RealConstituent Realizes)
    (hLE : RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack) :
    RootSeatedExclusionsRequiredAsSuch m w Admissible Ess HasAt RealConstituent Seat Realizes
      RequiresLack := by
  intro r hr C k hk hseat _ q hq hsub hfree
  refine hLE r hr C hseat.1 q hq hsub (fun t ht S hSq => ?_)
  obtain ⟨k', hk', hreal⟩ := hReal r hr t ht
  have hkk : k' = k := hS r hr k' k hk' hk
  subst hkk
  exact hfree t ht hreal S hSq

/-- Own-nature carriage in REQUIRES_LACK_2 from the unity of a simple root:
the same derivation as `ownCarriageFromUnity`, with TRANSFER_2. -/
theorem ownCarriageInFromUnity {W B D K : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RealConstituent : B → K → Prop)
    (Seat : B → (Set D → Prop) → K → Prop) (Realizes : B → K → D → Prop)
    (ReqIn : B → D → Set D → Prop)
    (hS : RootsConstitutivelySimple m w RealConstituent)
    (hSeat : RootOwnConditionsSeated m w Ess RealConstituent Seat)
    (hReal : RootDeterminationsRealized m w HasAt RealConstituent Realizes)
    (hEsse : RootsHaveSomeDetermination m w HasAt)
    (hT : RootSeatedExclusionsRequiredIn m w Admissible Ess HasAt RealConstituent Seat
      Realizes ReqIn) :
    RootOwnEssentialConditionsCarriedIn m w Admissible Ess HasAt ReqIn := by
  intro r hr C hC q hq hsub hfree
  obtain ⟨k, hk, hseat⟩ := hSeat r hr C hC
  obtain ⟨t₀, ht₀⟩ := hEsse r hr
  obtain ⟨k₀, hk₀, hreal₀⟩ := hReal r hr t₀ ht₀
  have hkk : k₀ = k := hS r hr k₀ k hk₀ hk
  subst hkk
  exact hT r hr C k₀ hk hseat ⟨t₀, ht₀, hreal₀⟩ q hq hsub (fun t ht _ S hS => hfree t ht S hS)

/-- Own-nature carriage as such from carriage in the root and the sense bridge
from REQUIRES_LACK_2 to REQUIRES_LACK_1 at actual roots. If no determination of
`r` requires a lack within `q` as such, then by the bridge none requires one in
`r`, and carriage in the root gives the condition. -/
theorem ownCarriageFromCarriageIn {W B D : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RequiresLack : D → Set D → Prop)
    (ReqIn : B → D → Set D → Prop)
    (hIn : RootOwnEssentialConditionsCarriedIn m w Admissible Ess HasAt ReqIn)
    (hB : RootRequirementsInHoldAsSuch m w HasAt RequiresLack ReqIn) :
    RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack := by
  intro r hr C hC q hq hsub hfree
  exact hIn r hr C hC q hq hsub (fun t ht S hS hReq => hfree t ht S hS (hB r hr t S ht hReq))

/-- E from own-nature exclusion, own-nature carriage and the necessity direction
of member grounding. Fix an actual root `r` and a determination `d` it lacks
while an admissible `q` contains its determinations and `d`. A condition of
`r`'s own nature fails at every profile containing its determinations and `d`,
so at `q`. The necessity direction makes `q` exclusion-free, so no
determination of `r` requires a lack within `q`, and own-nature carriage gives
the condition at `q`: a contradiction. -/
theorem noUnexplainedAbsenceFromOwnExclusion {W B D : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RequiresLack : D → Set D → Prop)
    (hX : RootLacksExcludedByOwnNature m w Ess HasAt)
    (hLE : RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack)
    (hMG : AdmissibleIsExclusionFree Admissible RequiresLack) :
    NoUnexplainedAbsenceAtRoots m w Admissible (HasAt w) := by
  rintro r hr d ⟨hLack, q, hq, hsub, hd⟩
  obtain ⟨C, hC, hEx⟩ := hX r hr d hLack
  exact hEx q hsub hd (hLE r hr C hC q hq hsub (fun t ht S hS => hMG q hq t (hsub ht) S hS))

/-- Every pure perfection at the actual roots from carriage in the root and the
purity of requirements in the root, without carriage as such, the requirement
sense bridge or member grounding. Fix an actual root `r` and a pure `k`. By
excluded middle `r` has `k` or lacks it. If it lacks `k`, a condition of `r`'s
own nature fails at every profile containing `r`'s determinations and `k`. The
root's profile is admissible and pure (strict purity), and `k` occurs in some
admissible profile, so joint compossibility makes the profile with `k` added
admissible. Its members are pure, so by the purity of requirements in the root
no determination of `r` requires in `r` the lack of some of them, and carriage
in the root gives the condition there: a contradiction. -/
theorem everyPureFromCarriageIn {W B D : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (Pure : D → Prop) (ReqIn : B → D → Set D → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hX : RootLacksExcludedByOwnNature m w Ess HasAt)
    (hIn : RootOwnEssentialConditionsCarriedIn m w Admissible Ess HasAt ReqIn)
    (hPin : RootPureRequiresNoPureLackIn m w HasAt Pure ReqIn)
    (hPure : ActualRootDeterminationsArePure m w (HasAt w) Pure)
    (hAdm : TruthCore.Causality.RootPerfectionExclusion.RootProfilesAdmissible m w Admissible
      (HasAt w))
    (hOcc : TruthCore.Causality.RootPerfectionExclusion.PureDeterminationsAdmissible Admissible
      Pure)
    (hJC : TruthCore.Causality.RootPerfectionExclusion.PureExtensionsAdmissible Admissible Pure) :
    TruthCore.Causality.PureActRoot.ActualRootHasEveryPureDetermination m w (HasAt w) Pure := by
  intro r hr k hk
  rcases hEM (HasAt w r k) with h | hLack
  · exact h
  · exfalso
    obtain ⟨C, hC, hEx⟩ := hX r hr k hLack
    have hq : Admissible (insert k (ActualProfile (HasAt w) r)) :=
      hJC _ k (hAdm r hr) (fun d hd => hPure r hr d hd) hk (hOcc k hk)
    have hsub : ActualProfile (HasAt w) r ⊆ insert k (ActualProfile (HasAt w) r) :=
      fun _ h => Or.inr h
    refine hEx _ hsub (Or.inl rfl) (hIn r hr C hC _ hq hsub (fun t ht S hS => ?_))
    refine hPin r hr t S ht (hPure r hr t ht) (fun e he => ?_)
    rcases hS he with rfl | he'
    · exact hk
    · exact hPure r hr e he'

/-- The purity of requirements in the root follows from the purity of
requirements as such (`0c8631bd`) and the bridge from REQUIRES_LACK_2 to
REQUIRES_LACK_1: a requirement in the root of a pure lack by a pure
determination would be one as such, which `0c8631bd` excludes. -/
theorem pureRequiresNoPureLackInOfAsSuch {W B D : Type} (m : Profile W B) (w : W)
    (HasAt : W → B → D → Prop) (Pure : D → Prop) (RequiresLack : D → Set D → Prop)
    (ReqIn : B → D → Set D → Prop)
    (hP : PureRequiresNoPureLack RequiresLack Pure)
    (hB : RootRequirementsInHoldAsSuch m w HasAt RequiresLack ReqIn) :
    RootPureRequiresNoPureLackIn m w HasAt Pure ReqIn :=
  fun r hr t S ht hpt hS hReq => hP t S hpt hS (hB r hr t S ht hReq)

/-- LE gives its own-nature restriction: take the being whose nature it is to be
the root itself. -/
theorem ownCarriageOfCarriage {W B D : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RequiresLack : D → Set D → Prop)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack) :
    RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack :=
  fun r hr C hC => hLE r hr r C hC

/-- Own-nature exclusion of root absences gives XN: an excluding condition of
the root's own nature is an excluding condition in some being's nature. -/
theorem essentialExclusionOfOwn {W B D : Type} (m : Profile W B) (w : W)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (hX : RootLacksExcludedByOwnNature m w Ess HasAt) :
    RootLacksEssentiallyExcluded m w Ess HasAt := by
  intro r hr d hd
  obtain ⟨C, hC, h⟩ := hX r hr d hd
  exact ⟨r, C, hC, h⟩

/-! ## Finite controls -/

section Controls

local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.SimpleUnityCarriage.Control
open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination openProfile positive)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootClosure.Control (hasAt noNoesis essOpen essNeg noReq aExcludesNoesis)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff memPure)
open TruthCore.Results.Causality.RootClosure (eOf notEPositive notLENeg notMGCarried
  positiveSubPure pureOpen' noesisPure openSubPure mgNoReq)

theorem noesisNotPositive : Determination.noesis ∉ positive := by simp [positive]

theorem rootTrue : ActualRoot rootProfile true true := (rootIff true).2 rfl

theorem noNoesisNeOpen : noNoesis ≠ openProfile := by
  intro h
  have h1 : openProfile pureSet := pureOpen'
  rw [← h] at h1
  exact h1 noesisPure

theorem simpleS : RootsConstitutivelySimple rootProfile true simpleRC := by
  rintro r - a b ⟨-, rfl⟩ ⟨-, rfl⟩; rfl

theorem notCompositeS : ¬ RootsConstitutivelySimple rootProfile true compositeRC := by
  intro h
  exact absurd (h true rootTrue true false rfl rfl) (by decide)

theorem seatAllOk (ess : Bool → Bool → (Set Determination → Prop) → Prop)
    (hess : ∀ y x C, ess y x C → x = true) :
    RootOwnConditionsSeated rootProfile true ess simpleRC seatAll := by
  intro r hr C hC
  have hx := hess r r C hC
  subst hx
  exact ⟨true, ⟨rfl, rfl⟩, hC, rfl, rfl⟩

theorem essOpenTrue : ∀ y x C, essOpen y x C → x = true := fun _ _ _ h => h.2.1
theorem essNegTrue : ∀ y x C, essNeg y x C → x = true := fun _ _ _ h => h.2.1

theorem realOk (src : Set Determination) :
    RootDeterminationsRealized rootProfile true (hasAt src src) simpleRC (realizesSrc src) := by
  intro r hr t ht
  rw [rootIff] at hr; subst hr
  exact ⟨true, ⟨rfl, rfl⟩, rfl, rfl, ht⟩

theorem esseOk (src : Set Determination) (h : Determination.esse ∈ src) :
    RootsHaveSomeDetermination rootProfile true (hasAt src src) := by
  intro r hr
  rw [rootIff] at hr; subst hr
  exact ⟨Determination.esse, h⟩

theorem pureEsse : Determination.esse ∈ pureSet := by simp [memPure]
theorem positiveEsse : Determination.esse ∈ positive := by simp [positive]
theorem positiveA : Determination.a ∈ positive := by simp [positive]

/-- An ESSENCE_6 condition of `essOpen` holds at every admissible profile. -/
theorem openCond {C : Set Determination → Prop} {y x : Bool} (h : essOpen y x C)
    {q : Set Determination} (hq : openProfile q) : C q := by
  obtain ⟨-, -, rfl⟩ := h; exact hq

/-- Classical row. -/
theorem classicalRow :
    cUnity essOpen pureSet simpleRC seatAll (realizesSrc pureSet) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essOpen
      (hasAt pureSet pureSet) simpleRC seatAll (realizesSrc pureSet) noReq ∧
    RootSeatedExclusionsRequiredIn rootProfile true openProfile essOpen
      (hasAt pureSet pureSet) simpleRC seatAll (realizesSrc pureSet) noReqIn ∧
    RootOwnEssentialConditionsCarried rootProfile true openProfile essOpen
      (hasAt pureSet pureSet) noReq ∧
    RootOwnEssentialConditionsCarriedIn rootProfile true openProfile essOpen
      (hasAt pureSet pureSet) noReqIn ∧
    RootEssentialConditionsCarried rootProfile true openProfile essOpen
      (hasAt pureSet pureSet) noReq ∧
    AdmissibleIsExclusionFree openProfile noReq ∧
    RootLacksExcludedByOwnNature rootProfile true essOpen (hasAt pureSet pureSet) ∧
    NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt pureSet pureSet true) := by
  refine ⟨⟨simpleS, seatAllOk _ essOpenTrue, realOk _, esseOk _ pureEsse⟩, ?_, ?_, ?_, ?_, ?_,
    mgNoReq, ?_, eOf _ _ subset_rfl⟩
  · intro r _ C k _ hseat _ q hq _ _; exact openCond hseat.1 hq
  · intro r _ C k _ hseat _ q hq _ _; exact openCond hseat.1 hq
  · intro r _ C hC q hq _ _; exact openCond hC hq
  · intro r _ C hC q hq _ _; exact openCond hC hq
  · intro r _ y C hC q hq _ _; exact openCond hC hq
  · intro r hr d hd
    rw [rootIff] at hr; subst hr
    refine ⟨openProfile, ⟨rfl, rfl, rfl⟩, fun q _ hdq hq => ?_⟩
    have hlim : d = Determination.limiter := by
      by_contra hne; exact hd ((memPure d).2 hne)
    subst hlim
    exact hq.2 hdq

/-- In the rival row, the source's absences are `noesis` and `limiter`. -/
theorem rivalLacks (d : Determination) (hd : ¬ hasAt positive positive true true d) :
    d = Determination.noesis ∨ d = Determination.limiter := by
  cases d <;> simp_all [hasAt, positive]

theorem rivalXN : RootLacksExcludedByOwnNature rootProfile true essNeg (hasAt positive positive) := by
  intro r hr d hd
  rw [rootIff] at hr; subst hr
  rcases rivalLacks d hd with rfl | rfl
  · exact ⟨noNoesis, ⟨rfl, rfl, Or.inr rfl⟩, fun q _ hdq hq => hq hdq⟩
  · exact ⟨openProfile, ⟨rfl, rfl, Or.inl rfl⟩, fun q _ hdq hq => hq.2 hdq⟩

/-- The rival's clause, with nothing requiring a lack as such, fails own-nature
carriage at the admissible `pure`. -/
theorem rivalNotLEown : ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
    (hasAt positive positive) noReq := by
  intro h
  exact h true rootTrue noNoesis ⟨rfl, rfl, Or.inr rfl⟩ pureSet pureOpen' positiveSubPure
    (fun _ _ _ _ h => h) noesisPure

/-- Rival row: the unity premises hold and carry the clause in the root; the
passage to requirement as such fails. -/
theorem rivalRow :
    cUnity essNeg positive simpleRC seatAll (realizesSrc positive) ∧
    RootSeatedExclusionsRequiredIn rootProfile true openProfile essNeg (hasAt positive positive)
      simpleRC seatAll (realizesSrc positive) esseExcludesNoesisIn ∧
    RootOwnEssentialConditionsCarriedIn rootProfile true openProfile essNeg
      (hasAt positive positive) esseExcludesNoesisIn ∧
    RootLacksExcludedByOwnNature rootProfile true essNeg (hasAt positive positive) ∧
    AdmissibleIsExclusionFree openProfile noReq ∧
    PureRequiresNoPureLack noReq TruthCore.Causality.RootPerfectionExclusion.Control.isPure ∧
    ¬ RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatAll (realizesSrc positive) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq ∧
    ¬ RootEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq ∧
    ¬ RootRequirementsInHoldAsSuch rootProfile true (hasAt positive positive) noReq
      esseExcludesNoesisIn ∧
    ¬ NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt positive positive true) ∧
    ¬ RootPureRequiresNoPureLackIn rootProfile true (hasAt positive positive)
      TruthCore.Causality.RootPerfectionExclusion.Control.isPure esseExcludesNoesisIn := by
  refine ⟨⟨simpleS, seatAllOk _ essNegTrue, realOk _, esseOk _ positiveEsse⟩, ?_, ?_, rivalXN,
    mgNoReq, fun _ _ _ _ h => h, ?_, rivalNotLEown, notLENeg, ?_, notEPositive _, ?_⟩
  · intro r hr C k _ hseat _ q hq hsub hfree
    rw [rootIff] at hr; subst hr
    obtain ⟨⟨-, -, hC | hC⟩, -, rfl⟩ := hseat
    · subst hC; exact hq
    · subst hC
      intro hn
      exact hfree Determination.esse positiveEsse ⟨rfl, rfl, positiveEsse⟩ {Determination.noesis}
        (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl, rfl⟩
  · intro r hr C hC q hq hsub hfree
    rw [rootIff] at hr; subst hr
    obtain ⟨-, -, hC | hC⟩ := hC
    · subst hC; exact hq
    · subst hC
      intro hn
      exact hfree Determination.esse positiveEsse {Determination.noesis}
        (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl, rfl⟩
  · intro h
    exact h true rootTrue noNoesis true ⟨rfl, rfl⟩ ⟨⟨rfl, rfl, Or.inr rfl⟩, rfl, rfl⟩
      ⟨Determination.esse, positiveEsse, rfl, rfl, positiveEsse⟩ pureSet pureOpen'
      positiveSubPure (fun _ _ _ _ _ h => h) noesisPure
  · intro h
    exact h true rootTrue Determination.esse {Determination.noesis} positiveEsse ⟨rfl, rfl, rfl⟩
  · intro h
    exact h true rootTrue Determination.esse {Determination.noesis} positiveEsse
      (by simp [TruthCore.Causality.RootPerfectionExclusion.Control.isPure, memPure])
      (fun e he => by
        rw [Set.mem_singleton_iff.mp he]
        simp [TruthCore.Causality.RootPerfectionExclusion.Control.isPure, memPure])
      ⟨rfl, rfl, rfl⟩

/-- Joint compossibility row: on the open family, with the necessity direction,
no requirement relation gives the rival's clause own-nature carriage as such
(`pure` is admissible and contains the rival's profile and `noesis`), and
`esse`, which the thinking effect shares, does not require the lack of `noesis`
as such (the effect's profile is admissible). -/
theorem rivalNoCarrierUnderMG (req : Determination → Set Determination → Prop)
    (hMG : AdmissibleIsExclusionFree openProfile req) :
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) req ∧
    ¬ RequiresLackAsSuch req Determination.esse {Determination.noesis} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact h true rootTrue noNoesis ⟨rfl, rfl, Or.inr rfl⟩ pureSet pureOpen' positiveSubPure
      (fun t ht S hS => hMG pureSet pureOpen' t (positiveSubPure ht) S hS) noesisPure
  · have hEff : openProfile TruthCore.Causality.SourceIntellectControls.ProfileControls.effect := by
      simp [openProfile, TruthCore.Causality.SourceIntellectControls.ProfileControls.effect]
    exact hMG _ hEff Determination.esse (by
        simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.effect])
      {Determination.noesis} (by
        simp [TruthCore.Causality.SourceIntellectControls.ProfileControls.effect]) h

/-- Simplicity omitted. -/
theorem compositeRow :
    ¬ RootsConstitutivelySimple rootProfile true compositeRC ∧
    RootOwnConditionsSeated rootProfile true essNeg compositeRC seatSplit ∧
    RootDeterminationsRealized rootProfile true (hasAt positive positive) compositeRC
      (realizesSrc positive) ∧
    RootsHaveSomeDetermination rootProfile true (hasAt positive positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) compositeRC seatSplit (realizesSrc positive) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq := by
  refine ⟨notCompositeS, ?_, ?_, esseOk _ positiveEsse, ?_, rivalNotLEown⟩
  · intro r hr C hC
    rw [rootIff] at hr; subst hr
    rcases hC.2.2 with hC' | hC'
    · exact ⟨true, rfl, hC, rfl, Or.inl ⟨hC', rfl⟩⟩
    · exact ⟨false, rfl, hC, rfl, Or.inr ⟨hC', rfl⟩⟩
  · intro r hr t ht
    rw [rootIff] at hr; subst hr
    exact ⟨true, rfl, rfl, rfl, ht⟩
  · intro r _ C k _ hseat hex q hq _ _
    obtain ⟨-, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hseat
    · exact hq
    · obtain ⟨t, -, -, h, -⟩ := hex
      exact absurd h (by decide)

/-- SEAT omitted. -/
theorem unseatedRow :
    RootsConstitutivelySimple rootProfile true simpleRC ∧
    ¬ RootOwnConditionsSeated rootProfile true essNeg simpleRC seatOpenOnly ∧
    RootDeterminationsRealized rootProfile true (hasAt positive positive) simpleRC
      (realizesSrc positive) ∧
    RootsHaveSomeDetermination rootProfile true (hasAt positive positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatOpenOnly (realizesSrc positive) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq := by
  refine ⟨simpleS, ?_, realOk _, esseOk _ positiveEsse, ?_, rivalNotLEown⟩
  · intro h
    obtain ⟨k, -, -, -, h', -⟩ := h true rootTrue noNoesis ⟨rfl, rfl, Or.inr rfl⟩
    exact noNoesisNeOpen h'
  · intro r _ C k _ hseat _ q hq _ _
    obtain ⟨-, -, rfl, -⟩ := hseat
    exact hq

/-- REAL omitted. -/
theorem unrealizedRow :
    RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true essNeg simpleRC seatAll ∧
    ¬ RootDeterminationsRealized rootProfile true (hasAt positive positive) simpleRC
      realizesNone ∧
    RootsHaveSomeDetermination rootProfile true (hasAt positive positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatAll realizesNone noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) noReq := by
  refine ⟨simpleS, seatAllOk _ essNegTrue, ?_, esseOk _ positiveEsse, ?_, rivalNotLEown⟩
  · intro h
    obtain ⟨_, -, h'⟩ := h true rootTrue Determination.esse positiveEsse
    exact h'
  · intro r _ C k _ _ hex
    obtain ⟨_, -, h⟩ := hex
    exact absurd h id

/-- ESSE omitted: the source has no determination. -/
theorem emptyRow :
    RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true essNeg simpleRC seatAll ∧
    RootDeterminationsRealized rootProfile true (hasAt ∅ ∅) simpleRC (realizesSrc ∅) ∧
    ¬ RootsHaveSomeDetermination rootProfile true (hasAt ∅ ∅) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt ∅ ∅) simpleRC seatAll (realizesSrc ∅) noReq ∧
    ¬ RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt ∅ ∅) noReq := by
  refine ⟨simpleS, seatAllOk _ essNegTrue, realOk _, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨_, ht⟩ := h true rootTrue
    exact ht
  · intro r hr C k _ _ hex
    rw [rootIff] at hr; subst hr
    obtain ⟨_, ht, -⟩ := hex
    exact absurd ht id
  · intro h
    exact h true rootTrue noNoesis ⟨rfl, rfl, Or.inr rfl⟩ pureSet pureOpen'
      (fun _ h => absurd h id) (fun _ _ _ _ h => h) noesisPure

/-- The necessity direction is independent of the unity package. -/
theorem mgIndependentRow :
    cUnity essNeg positive simpleRC seatAll (realizesSrc positive) ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true openProfile essNeg
      (hasAt positive positive) simpleRC seatAll (realizesSrc positive) aExcludesNoesis ∧
    RootOwnEssentialConditionsCarried rootProfile true openProfile essNeg
      (hasAt positive positive) aExcludesNoesis ∧
    ¬ AdmissibleIsExclusionFree openProfile aExcludesNoesis ∧
    ¬ NoUnexplainedAbsenceAtRoots rootProfile true openProfile (hasAt positive positive true) := by
  refine ⟨⟨simpleS, seatAllOk _ essNegTrue, realOk _, esseOk _ positiveEsse⟩, ?_, ?_,
    notMGCarried, notEPositive _⟩
  · intro r hr C k _ hseat _ q hq _ hfree
    rw [rootIff] at hr; subst hr
    obtain ⟨⟨-, -, hC | hC⟩, -, rfl⟩ := hseat
    · subst hC; exact hq
    · subst hC
      intro hn
      exact hfree Determination.a positiveA ⟨rfl, rfl, positiveA⟩ {Determination.noesis}
        (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl⟩
  · intro r hr C hC q hq _ hfree
    rw [rootIff] at hr; subst hr
    obtain ⟨-, -, hC | hC⟩ := hC
    · subst hC; exact hq
    · subst hC
      intro hn
      exact hfree Determination.a positiveA {Determination.noesis}
        (Set.singleton_subset_iff.mpr hn) ⟨rfl, rfl⟩

theorem natHasIff (d : NatDet) :
    natHas true true d ↔ d = .inl .esse ∨ d = .inl .a ∨ d = .inl .b ∨ d = .inr () := Iff.rfl

theorem natLacks (d : NatDet) (hd : ¬ natHas true true d) :
    d = .inl .noesis ∨ d = .inl .limiter := by
  rcases d with d | u
  · cases d <;> simp_all [natHas]
  · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hd

theorem natNoesisOut {q : Set NatDet} (hq : natAdmissible q) (hn : Sum.inr () ∈ q) :
    Sum.inl Determination.noesis ∉ q := fun h => hq.2.2 ⟨hn, h⟩

/-- Fine-grained rival row. -/
theorem fineGrainedRow :
    RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true natEss simpleRC natSeat ∧
    RootDeterminationsRealized rootProfile true natHas simpleRC natRealizes ∧
    RootsHaveSomeDetermination rootProfile true natHas ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true natAdmissible natEss natHas simpleRC
      natSeat natRealizes natReq ∧
    RootOwnEssentialConditionsCarried rootProfile true natAdmissible natEss natHas natReq ∧
    RootRequirementsInHoldAsSuch rootProfile true natHas natReq natReqIn ∧
    AdmissibleIsExclusionFree natAdmissible natReq ∧
    RootLacksExcludedByOwnNature rootProfile true natEss natHas ∧
    NoUnexplainedAbsenceAtRoots rootProfile true natAdmissible (natHas true) ∧
    (¬ PureRequiresNoPureLack natReq natPurePlotinian ∧
      ActualRootDeterminationsArePure rootProfile true (natHas true) natPurePlotinian) ∧
    (PureRequiresNoPureLack natReq natPureStrict ∧
      ¬ ActualRootDeterminationsArePure rootProfile true (natHas true) natPureStrict) := by
  have hnat : Sum.inr () ∈ ActualProfile (natHas true) true := Or.inr (Or.inr (Or.inr rfl))
  have carried : ∀ C, natEss true true C → ∀ q, natAdmissible q →
      ActualProfile (natHas true) true ⊆ q → C q := by
    rintro C ⟨-, -, rfl | rfl⟩ q hq hsub
    · exact hq
    · exact natNoesisOut hq (hsub hnat)
  refine ⟨simpleS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro r hr C hC
    rw [rootIff] at hr; subst hr
    exact ⟨true, ⟨rfl, rfl⟩, hC, rfl, rfl⟩
  · intro r hr t ht
    rw [rootIff] at hr; subst hr
    exact ⟨true, ⟨rfl, rfl⟩, rfl, rfl, ht⟩
  · intro r hr
    rw [rootIff] at hr; subst hr
    exact ⟨.inl .esse, Or.inl rfl⟩
  · intro r hr C k _ hseat _ q hq hsub _
    rw [rootIff] at hr; subst hr
    exact carried C hseat.1 q hq hsub
  · intro r hr C hC q hq hsub _
    rw [rootIff] at hr; subst hr
    exact carried C hC q hq hsub
  · rintro r - t S - ⟨-, h⟩; exact h
  · rintro q hq d hd S hS ⟨rfl, rfl⟩
    exact hq.2.2 ⟨hd, hS rfl⟩
  · intro r hr d hd
    rw [rootIff] at hr; subst hr
    rcases natLacks d hd with rfl | rfl
    · exact ⟨natNoNoesis, ⟨rfl, rfl, Or.inr rfl⟩, fun q _ hdq hq => hq hdq⟩
    · exact ⟨natAdmissible, ⟨rfl, rfl, Or.inl rfl⟩, fun q _ hdq hq => hq.2.1 hdq⟩
  · rintro r hr d ⟨hLack, q, hq, hsub, hd⟩
    rw [rootIff] at hr; subst hr
    rcases natLacks d hLack with rfl | rfl
    · exact natNoesisOut hq (hsub hnat) hd
    · exact hq.2.1 hd
  · intro h
    exact h (.inr ()) {Sum.inl Determination.noesis} (by simp [natPurePlotinian])
      (by simp [natPurePlotinian]) ⟨rfl, rfl⟩
  · intro r hr d hd
    rw [rootIff] at hr; subst hr
    rcases hd with rfl | rfl | rfl | rfl <;> simp [natPurePlotinian]
  · rintro d S hd - ⟨rfl, -⟩
    exact hd.2 rfl
  · intro h
    exact (h true rootTrue (.inr ()) (Or.inr (Or.inr (Or.inr rfl)))).2 rfl

open TruthCore.Explanation.InquiryClosure.Control (selAdmissible selReq essSel) in
open TruthCore.Causality.RootClosure.Control (hasSel SelDet) in
/-- Classical selection row. -/
theorem selectionRow :
    RootsConstitutivelySimple rootProfile true simpleRC ∧
    RootOwnConditionsSeated rootProfile true essSel simpleRC selSeat ∧
    RootDeterminationsRealized rootProfile true hasSel simpleRC selRealizes ∧
    RootsHaveSomeDetermination rootProfile true hasSel ∧
    RootSeatedExclusionsRequiredAsSuch rootProfile true selAdmissible essSel hasSel simpleRC
      selSeat selRealizes selReq ∧
    RootOwnEssentialConditionsCarried rootProfile true selAdmissible essSel hasSel selReq ∧
    AdmissibleIsExclusionFree selAdmissible selReq ∧
    RootLacksExcludedByOwnNature rootProfile true essSel hasSel ∧
    NoUnexplainedAbsenceAtRoots rootProfile true selAdmissible (hasSel true) ∧
    ¬ TruthCore.Causality.RootClosure.RootAbsencesNecessary rootProfile true hasSel := by
  have hLE : RootOwnEssentialConditionsCarried rootProfile true selAdmissible essSel hasSel
      selReq := by
    rintro r - C ⟨-, -, rfl⟩ q hq - -
    exact hq
  have hXN : RootLacksExcludedByOwnNature rootProfile true essSel hasSel := by
    intro r hr d hd
    rw [rootIff] at hr; subst hr
    obtain ⟨y, C, hC, h⟩ := TruthCore.Results.Explanation.InquiryClosure.xnSel true rootTrue d hd
    obtain ⟨rfl, -, rfl⟩ := hC
    exact ⟨selAdmissible, ⟨rfl, rfl, rfl⟩, h⟩
  refine ⟨simpleS, ?_, ?_, ?_, ?_, hLE, TruthCore.Results.Explanation.InquiryClosure.mgSel, hXN,
    noUnexplainedAbsenceFromOwnExclusion _ _ _ _ _ _ hXN hLE
      TruthCore.Results.Explanation.InquiryClosure.mgSel,
    TruthCore.Results.Causality.RootClosure.classicalSelectionControl.2⟩
  · intro r hr C hC
    rw [rootIff] at hr; subst hr
    exact ⟨true, ⟨rfl, rfl⟩, hC, rfl, rfl⟩
  · intro r hr t ht
    rw [rootIff] at hr; subst hr
    exact ⟨true, ⟨rfl, rfl⟩, rfl, rfl, ht⟩
  · intro r hr
    rw [rootIff] at hr; subst hr
    exact ⟨.inl Determination.esse, by simp [hasSel, memPure]⟩
  · rintro r - C k - ⟨⟨-, -, rfl⟩, -⟩ - q hq - -
    exact hq

open TruthCore.Causality.RootPerfectionExclusion.Control (isPure) in
/-- Clause 12: the in-root route on the #2153 carrier. -/
theorem inRootRow :
    RootPureRequiresNoPureLackIn rootProfile true (hasAt pureSet pureSet) isPure noReqIn ∧
    TruthCore.Causality.PureActRoot.ActualRootHasEveryPureDetermination rootProfile true
      (hasAt pureSet pureSet true) isPure ∧
    ActualRootDeterminationsArePure rootProfile true (hasAt positive positive true) isPure ∧
    TruthCore.Causality.RootPerfectionExclusion.RootProfilesAdmissible rootProfile true
      openProfile (hasAt positive positive true) ∧
    TruthCore.Causality.RootPerfectionExclusion.PureDeterminationsAdmissible openProfile isPure ∧
    TruthCore.Causality.RootPerfectionExclusion.PureExtensionsAdmissible openProfile isPure ∧
    ¬ TruthCore.Causality.PureActRoot.ActualRootHasEveryPureDetermination rootProfile true
      (hasAt positive positive true) isPure := by
  refine ⟨fun _ _ _ _ _ _ _ h => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr d hd
    rw [rootIff] at hr; subst hr
    exact hd
  · intro r hr d hd
    rw [rootIff] at hr; subst hr
    exact positiveSubPure hd
  · intro r hr
    rw [rootIff] at hr; subst hr
    exact TruthCore.Results.Causality.RootClosure.positiveOpen
  · intro k hk
    exact ⟨pureSet, pureOpen', hk⟩
  · intro q k hq _ hk _
    refine ⟨Or.inr hq.1, ?_⟩
    rintro (h | h)
    · subst h; exact absurd hk (by simp [isPure, memPure])
    · exact hq.2 h
  · intro h
    exact noesisNotPositive (h true rootTrue Determination.noesis noesisPure)

/-- Clause 1: on the constituents-realize reading simplicity is idle. -/
theorem simplicityIdle {W B D K : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RealConstituent : B → K → Prop)
    (Seat : B → (Set D → Prop) → K → Prop) (Realizes : B → K → D → Prop)
    (RequiresLack : D → Set D → Prop)
    (hSeat : RootOwnConditionsSeated m w Ess RealConstituent Seat)
    (hCR : RootConstituentsRealize m w HasAt RealConstituent Realizes)
    (hT : RootSeatedExclusionsRequiredAsSuch m w Admissible Ess HasAt RealConstituent Seat
      Realizes RequiresLack) :
    RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack := by
  intro r hr C hC q hq hsub hfree
  obtain ⟨k, hk, hseat⟩ := hSeat r hr C hC
  exact hT r hr C k hk hseat (hCR r hr k hk) q hq hsub (fun t ht _ S hS => hfree t ht S hS)

/-- Comparator companion and certificate of lane U (#2145): see
`SimpleUnityCarriageMap` for the twelve clauses. Structural assignments only, not
models of essence, constituency, realization or requirement. -/
theorem simpleUnityCarriageMap : SimpleUnityCarriageMap :=
  ⟨fun m w Adm Ess HasAt RC Seat Rl Req => simplicityIdle m w Adm Ess HasAt RC Seat Rl Req,
    classicalRow, rivalRow, rivalNoCarrierUnderMG, compositeRow, unseatedRow, unrealizedRow,
    emptyRow, mgIndependentRow, fineGrainedRow, selectionRow, inRootRow⟩

end Controls

end TruthCore.Results.Causality.SimpleUnityCarriage
