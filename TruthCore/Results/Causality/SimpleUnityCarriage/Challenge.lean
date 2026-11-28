import TruthCore.Causality.SimpleUnityCarriage
import TruthCore.Results.Causality.RootClosure.Solution
import TruthCore.Results.Explanation.InquiryClosure.Solution

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The purity of requirements in the root follows from the purity of
requirements as such (`0c8631bd`) and the bridge from REQUIRES_LACK_2 to
REQUIRES_LACK_1: a requirement in the root of a pure lack by a pure
determination would be one as such, which `0c8631bd` excludes. -/
theorem pureRequiresNoPureLackInOfAsSuch {W B D : Type} (m : Profile W B) (w : W)
    (HasAt : W → B → D → Prop) (Pure : D → Prop) (RequiresLack : D → Set D → Prop)
    (ReqIn : B → D → Set D → Prop)
    (hP : PureRequiresNoPureLack RequiresLack Pure)
    (hB : RootRequirementsInHoldAsSuch m w HasAt RequiresLack ReqIn) :
    RootPureRequiresNoPureLackIn m w HasAt Pure ReqIn := by
  sorry

/-- LE gives its own-nature restriction: take the being whose nature it is to be
the root itself. -/
theorem ownCarriageOfCarriage {W B D : Type} (m : Profile W B) (w : W)
    (Admissible : Set D → Prop) (Ess : B → B → (Set D → Prop) → Prop)
    (HasAt : W → B → D → Prop) (RequiresLack : D → Set D → Prop)
    (hLE : RootEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack) :
    RootOwnEssentialConditionsCarried m w Admissible Ess HasAt RequiresLack := by
  sorry

/-- Own-nature exclusion of root absences gives XN: an excluding condition of
the root's own nature is an excluding condition in some being's nature. -/
theorem essentialExclusionOfOwn {W B D : Type} (m : Profile W B) (w : W)
    (Ess : B → B → (Set D → Prop) → Prop) (HasAt : W → B → D → Prop)
    (hX : RootLacksExcludedByOwnNature m w Ess HasAt) :
    RootLacksEssentiallyExcluded m w Ess HasAt := by
  sorry

/-! ## Finite controls -/

local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.SimpleUnityCarriage.Control
open TruthCore.Causality.SourceIntellectControls.ProfileControls
  (Determination openProfile positive)
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile)
open TruthCore.Causality.RootClosure.Control (hasAt noNoesis essOpen essNeg noReq aExcludesNoesis)
open TruthCore.Results.Causality.RootPerfectionExclusion (rootIff memPure)
open TruthCore.Results.Causality.RootClosure (eOf notEPositive notLENeg notMGCarried
  positiveSubPure pureOpen' noesisPure openSubPure mgNoReq)

open TruthCore.Explanation.InquiryClosure.Control (selAdmissible selReq essSel) in
open TruthCore.Causality.RootClosure.Control (hasSel SelDet) in

open TruthCore.Causality.RootPerfectionExclusion.Control (isPure) in

/-- Comparator companion and certificate of lane U (#2145): see
`SimpleUnityCarriageMap` for the thirteen clauses. Structural assignments only, not
models of essence, constituency, realization or requirement. -/
theorem simpleUnityCarriageMap : SimpleUnityCarriageMap := by
  sorry

end TruthCore.Results.Causality.SimpleUnityCarriage
