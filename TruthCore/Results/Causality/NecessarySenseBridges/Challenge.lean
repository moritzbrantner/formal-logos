import TruthCore.Causality.ModalSenseSupport
import TruthCore.Results.Modal.StandardCorrespondenceCertificate.Solution

/-! Frame-to-schema correspondences for the route's NECESSARY_2 box (#1784,
#461). The sense fork's frame premises (`OnticFrameKT`, `OnticFrameKTB`,
`OnticFrameS5` of `TruthCore.Causality.NecessarySenseFork`) are frame
conditions on the route frame `m.ontic.frame`; the schema premises
(`OnticTSchemaValid`, `OnticBSchemaValid`, `Ontic5SchemaValid` of
`TruthCore.Causality.ModalSenseSupport`) are modal principles about the same
box. The forward direction applies the soundness theorems of the modal library
(`TruthCore.Modal.axiomT_valid`, `axiomB_valid`, `axiom5_valid` of
`TruthCore.Modal.Kripke`); the converse T direction applies the verified T
correspondence `TruthCore.Results.Modal.StandardCorrespondenceCertificate.certificate`
(premise-free, MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE). Nothing is restated, and
no frame condition or schema is asserted of the route. -/

namespace TruthCore.Results.Causality.NecessarySenseBridges

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)

/-- A KT route frame validates the T schema of the route's box
(`axiomT_valid`: T is valid on reflexive frames). -/
theorem frameKTToTSchema {W B : Type} (m : Profile W B) (h : OnticFrameKT m) :
    OnticTSchemaValid m.ontic := by
  sorry

/-- The T schema on the route frame makes the route frame KT (the verified T
correspondence of the modal library: T-schema validity implies reflexivity). -/
theorem tSchemaToFrameKT {W B : Type} (m : Profile W B)
    (h : OnticTSchemaValid m.ontic) : OnticFrameKT m := by
  sorry

/-- A KTB route frame validates the B schema of the route's box
(`axiomB_valid`: B is valid on symmetric frames; the frame's symmetry is the
second conjunct of KTB). -/
theorem frameKTBToBSchema {W B : Type} (m : Profile W B) (h : OnticFrameKTB m) :
    OnticBSchemaValid m.ontic := by
  sorry

/-- An S5 route frame validates the 5 schema of the route's box
(`axiom5_valid`: 5 is valid on Euclidean frames; Euclideanness is the second
conjunct of S5). -/
theorem frameS5To5Schema {W B : Type} (m : Profile W B) (h : OnticFrameS5 m) :
    Ontic5SchemaValid m.ontic := by
  sorry

/-- Strictness of the KTB-to-B and S5-to-5 orders, on the one-world frame with
no edge. -/
theorem schemaStrictness : TruthCore.Causality.ModalSenseSupport.Control.SchemaStrictness := by
  sorry

end TruthCore.Results.Causality.NecessarySenseBridges
