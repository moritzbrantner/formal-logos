import TruthCore.Causality.BegunOrHomogeneousGiving
import TruthCore.Results.Causality.TimeSymmetricGiving.Solution

namespace TruthCore.Results.Causality.BegunOrHomogeneousGiving

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation (BeingGiving)
open TruthCore.Causality.ConcurrentActualization (ConcurrentlyActualized)
open TruthCore.Causality.SustainingDependence (ConcurrentlyActualizedOnceBegun)
open TruthCore.Causality.TimeSymmetricGiving
  (HomogeneousIn PreservesHistory ConcurrentlyActualizedIfHomogeneous)
open TruthCore.Causality.BegunOrHomogeneousGiving

/-- The begun restriction, the homogeneous restriction and coverage by the two
cases give weak concurrent actualization `40a97664`: a present received-esse
thing either has a first moment of presence, and the begun restriction applies,
or is homogeneous, and the homogeneous restriction applies. -/
theorem concurrentOfBegunOrHomogeneous {W B T P : Type} [Preorder T] (h : History W B T)
    (G : BeingGiving W B T) (Facts : W → B → T → Prop) (EsseReceivedIn : B → P → Prop)
    (hBegun : ConcurrentlyActualizedOnceBegun h G EsseReceivedIn)
    (hHom : ConcurrentlyActualizedIfHomogeneous h G Facts EsseReceivedIn)
    (hCover : BegunOrHomogeneous h Facts EsseReceivedIn) :
    ConcurrentlyActualized h G EsseReceivedIn := by
  sorry

open TruthCore.Causality.TimeSymmetricGiving.Control (eternal begun noGivingZ givesAtZero
  givesAlways noFacts)
open TruthCore.Causality.ConcurrentActualization.Control (falseReceived)
open TruthCore.Causality.BegunOrHomogeneousGiving.Control

/-- Omission and strictness controls (`Control.Certificate`). -/
theorem controls : Certificate := by
  sorry

/-- Populated nonvacuity witness (`Control.Nonvacuity`). -/
theorem nonvacuity : Nonvacuity := by
  sorry

end TruthCore.Results.Causality.BegunOrHomogeneousGiving
