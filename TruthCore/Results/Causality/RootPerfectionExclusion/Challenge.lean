import TruthCore.Causality.RootPerfectionExclusion
import TruthCore.Results.Causality.FiniteEsseDependence.Solution
import TruthCore.Results.Causality.IntentionalExemplarExtension.Solution
import TruthCore.Results.Causality.WholePowerPerfection.Solution
import TruthCore.Modal.LimitationPossibility

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
  sorry

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
  sorry

/-- The formal-limitation L bridge from the determination-to-esse bridge and
joint compossibility. -/
theorem positiveExclusionLimitsEsse {B D : Type}
    (Admissible : Set D → Prop) (Has : B → D → Prop) (Pure : D → Prop)
    (Limited : B → Prop) (hEM : ExcludedMiddle)
    (hImpure : ImpureDeterminationLimitsEsse Has Pure Limited)
    (hExtend : PureExtensionsAdmissible Admissible Pure) :
    PositiveProfileExclusionLimitsEsse Admissible Has Pure Limited := by
  sorry

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
  sorry

/-! ## Coverage and exclusivity of the three cases (Lean-only helpers) -/

/-! ## Simplicity reading and the four roles (question D) -/

open TruthCore.Causality.WholePowerPerfection.WisdomSelfUnderstanding
  (SelfCapacityExercisedOrPotent)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

/-! ## Finite controls -/

/-- The #1970 pure determinations (`esse`, `a`, `b`, `noesis`). -/
local notation "pureSet" => TruthCore.Causality.SourceIntellectControls.ProfileControls.pure
open TruthCore.Causality.RootPerfectionExclusion.Control
open TruthCore.Causality.SourceIntellectControls.ProfileControls hiding pure
open TruthCore.Causality.IntentionalExemplarExtension.Control (rootProfile frame)

theorem structuralControls : StructuralControls := by
  sorry

theorem anchorControl : AnchorControl := by
  sorry

theorem esseControls : EsseControls := by
  sorry

theorem standingRival : StandingRival := by
  sorry

end TruthCore.Results.Causality.RootPerfectionExclusion
