module

public import TruthCore.Modal.ModalOntologicalCase

@[expose] public section

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
  obtain ⟨v, hwv, hGv⟩ := hPossible
  have hBoxV := hIf v hwv hGv
  obtain ⟨x, _, hConcrete, hExists, hNecessary⟩ :=
    necessaryGod_of_box_persists σ m w hReflexive hPersists
      (fun u hwu => hBoxV u (hEuclidean v u hwv hwu))
  exact ⟨x, hConcrete, hExists, hNecessary⟩

/-- Rigidity of concrete GOD_4 presence entails the persistence bridge (the
strength order backing result; `fixedPlusVisitor` in `controls` is strict). -/
theorem persistsOfRigid {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (hRigid : GodPresenceRigidAt σ m w) : GodPresencePersistsAt σ m w :=
  persists_of_rigid σ m w hRigid

/-- Certified difference (#1598): rigidity is exactly persistence together with
uniqueness of concrete GOD_4 at accessible worlds whenever one exists at `w`. -/
theorem rigidOverPersistsExact : RigidOverPersistsExact := by
  intro W σ m w
  constructor
  · intro hRigid
    refine ⟨persists_of_rigid σ m w hRigid, fun ⟨x, hx⟩ v hv y z hy hz => ?_⟩
    rw [hRigid v x y hv hx hy, hRigid v x z hv hx hz]
  · rintro ⟨hPersists, hUnique⟩ v x y hv hx hy
    have hxv : GodConcretePresent σ m x v :=
      ⟨hx.1, hx.2.1, hPersists x hx v hv ⟨y, hy⟩⟩
    exact hUnique ⟨x, hx⟩ v hv y x hy hxv

/-- The omission, nonvacuity and strictness controls. -/
theorem controls : Controls := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩ <;>
  simp [EuclideanAt, ActualReflexive, GodPossiblyExistsAt, GodNecessaryIfExistentAt,
    GodPresenceRigidAt, GodPresencePersistsAt, NecessaryGodConcreteAt, NecessaryConcreteAt,
    GodConcreteExists, GodConcretePresent, TruthCore.Modal.NecessaryIfExistent.NecessaryIf,
    TruthCore.Modal.NecessaryIfExistent.PossibleExistence,
    TruthCore.Isabelle.AFP.GoedelGod.Box, TruthCore.Isabelle.AFP.GoedelGod.Dia,
    TruthCore.German.Kant.CosmologicalInference.NecessaryAt,
    onlyHere, nobody, swapped, fixedOne, fixedPlusVisitor, fixedPlusLocal, boolProfile,
    boolSignature]

end TruthCore.Results.Modal.ModalOntologicalCase
