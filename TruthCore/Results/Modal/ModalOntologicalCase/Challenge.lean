import TruthCore.Modal.ModalOntologicalCase

namespace TruthCore.Results.Modal.ModalOntologicalCase
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal.ModalOntologicalCase

/-- The modal ontological argument on the case profile, concluding the shared
`NecessaryConcreteAt`. Possibility gives an accessible world `v` with a
concrete GOD_4; the boxed conditional at `w` makes `G` necessary at `v`;
Euclidean access at `w` carries that box back to every world accessible from
`w` (a de dicto box); reflexivity at `w` gives a concrete GOD_4 `x` at `w`, and
the persistence bridge makes `x` exist at every accessible world. The witness
of the conclusion is that same `x`; its GOD_4-hood is not part of the
conclusion. -/
theorem necessaryConcreteOfModal {W : Type} (σ : Signature) (m : Profile W σ.Being)
    (w : W)
    (hEuclidean : EuclideanAt m.ontic.frame w)
    (hReflexive : ActualReflexive m.ontic w)
    (hIf : GodNecessaryIfExistentAt σ m w)
    (hPossible : GodPossiblyExistsAt σ m w)
    (hPersists : GodPresencePersistsAt σ m w) :
    NecessaryConcreteAt m w := by
  sorry

/-- Rigidity of concrete GOD_4 presence entails the persistence bridge (the
strength order backing result; `fixedPlusVisitor` in `controls` is strict). -/
theorem persistsOfRigid {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (hRigid : GodPresenceRigidAt σ m w) : GodPresencePersistsAt σ m w := by
  sorry

/-- The omission, nonvacuity and strictness controls. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Modal.ModalOntologicalCase
