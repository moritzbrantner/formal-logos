import TruthCore.Modal.MirrorCollapse
import TruthCore.Results.Modal.SimplicityCollapse.Solution
import TruthCore.Results.Causality.RootPerfectionIntellect.Solution

/-! # The relation-of-reason account and the mirror-world rule: proofs (#2145, lane M)

See `TruthCore.Modal.MirrorCollapse` and `docs/notes/simplicity-collapse-555.md`,
section "The relation-of-reason account and the mirror-world rule". -/

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

/-- The chiral mirror argument, mirror in sense MIRROR_2 (CPT conjugation). With
essence-grounded possibility, factivity, preservation by the CPT map and reversed
handedness at the CPT image, the CPT image is accessible and has the opposite
handedness; an actual concrete being that exists at the CPT image only if that
image keeps the actual handedness is absent there, so it is contingent. -/
theorem contingentFromChiralMirror {W B : Type} (m : Profile W B) (w : W)
    (Essential : B → (W → Prop) → Prop) (τ : CPTConjugation W) (H : W → Prop)
    (hEM : EssenceGroundedWorldPossibility m.ontic w Essential)
    (hFact : EssentialTruthsHoldAt Essential w)
    (hPres : EssentialTruthsPreservedByCPTAt Essential τ w)
    (hRev : HandednessReversedByCPTAt τ H w)
    (hChiral : ChiralAtCPTImageAt m τ w H) :
    SomeActualContingentAt m w := by
  sorry

/-- The mirror fork. -/
theorem mirrorFork : MirrorForkCertificate := by
  sorry

/-! ## Mirror controls -/

/-- The controls of the chiral mirror argument. -/
theorem mirrorControls : MirrorControls := by
  sorry

/-! ## A. The relation-of-reason account -/

/-- The relation-of-reason certificate. -/
theorem relationOfReason : RelationOfReasonCertificate := by
  sorry

end TruthCore.Results.Modal.MirrorCollapse
