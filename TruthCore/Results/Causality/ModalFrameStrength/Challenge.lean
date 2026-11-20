import TruthCore.Causality.ModalSenseSupport

/-! Frame-class strength orders among the route's open frame premises
(`OnticFrameKT`, `OnticFrameS4`, `OnticFrameKTB`, `OnticFrameS5` of
`TruthCore.Causality.NecessarySenseFork`), found by a `truth discover` run over
the modal sense-fork nodes. The proofs reuse the frame-class theorems of the
modal library (`TruthCore.Modal.s5_implies_s4` and `s5_implies_ktb` of
`TruthCore.Modal.Cube`); nothing is restated.
Each frame premise is about the same route frame `m.ontic.frame`; none is
asserted to hold. -/

namespace TruthCore.Results.Causality.ModalFrameStrength

open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.BruteFoundationBoundary (Profile)

/-- An S5 route frame is an S4 route frame (`s5_implies_s4`: a reflexive
Euclidean relation is transitive). -/
theorem frameS5ToS4 {W B : Type} (m : Profile W B) (h : OnticFrameS5 m) :
    OnticFrameS4 m := by
  sorry

/-- An S5 route frame is a KTB route frame (`s5_implies_ktb`: a reflexive
Euclidean relation is symmetric). -/
theorem frameS5ToKTB {W B : Type} (m : Profile W B) (h : OnticFrameS5 m) :
    OnticFrameKTB m := by
  sorry

/-- An S4 route frame is a KT route frame (its reflexivity conjunct). -/
theorem frameS4ToKT {W B : Type} (m : Profile W B) (h : OnticFrameS4 m) :
    OnticFrameKT m := by
  sorry

/-- A KTB route frame is a KT route frame (its reflexivity conjunct). -/
theorem frameKTBToKT {W B : Type} (m : Profile W B) (h : OnticFrameKTB m) :
    OnticFrameKT m := by
  sorry

/-- Strictness of the four orders, on explicit frames. -/
theorem frameStrictness : TruthCore.Causality.ModalSenseSupport.Control.FrameStrictness := by
  sorry

end TruthCore.Results.Causality.ModalFrameStrength
