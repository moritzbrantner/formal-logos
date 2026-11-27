module

public import TruthCore.Modal.NecessaryIfExistent
public import TruthCore.Causality.ActualEuclidean
public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Case.Catholicism.Root
public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers
public import TruthCore.Logic.StrengthComparison

/-!
Case instance of the stipulated proposition `G` of `NecessaryIfExistent`
(#437) for the modal ontological route (#2103, lane F). Analyst formulation,
attribution deferred: nothing here is read from Anselm, Hartshorne, Malcolm or
Plantinga.

`G v` says that some being which is GOD_4 under the case signature's primitive
`IsGod` (DEF-GOD-OF-CLASSICAL-THEISM) is concrete under the case profile and
exists at `v` under the profile's `Ontic`. Concreteness is part of `G`'s
content, so it is supplied by the possibility premise, never derived from
necessity: de re necessity alone does not give concreteness (#2106).

`Box G` is de dicto: different GOD_4 concreta may witness `G` at different
worlds (`DeDicto` of #435 with this presence). The passage to the de re
`NecessaryAt` of one individual is the explicit open premise
`GodPresencePersistsAt`; the stronger sibling `GodPresenceRigidAt` adds a
cross-world uniqueness commitment the route does not use. Neither Scott's nor the Gödel 1970 essence-based
`NecessaryExistence` occurs, and Gödel's `GodLike` is not used, so no
identification of GOD_4 with a Gödel–Scott God concept is made here.
-/

@[expose] public section

namespace TruthCore.Modal.ModalOntologicalCase

open TruthCore.Case.Catholicism (Signature)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modal.NecessaryIfExistent (NecessaryIf PossibleExistence)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (DeDicto DeRe)

variable {W : Type}

/-- `x` is GOD_4 under the case signature, concrete under the case profile,
and exists at `v`. `IsGod` is world-independent; only existence varies. -/
def GodConcretePresent (σ : Signature) (m : Profile W σ.Being)
    (x : σ.Being) (v : W) : Prop :=
  σ.IsGod x ∧ m.concrete x ∧ m.ontic.ExistsAt v x

/-- The case instance of the stipulated `G`: some concrete GOD_4 exists at
`v`. A world proposition; it fixes no individual across worlds. -/
def GodConcreteExists (σ : Signature) (m : Profile W σ.Being) : MProp W :=
  fun v => ∃ x, GodConcretePresent σ m x v

/-- The boxed conditional `□(G → □G)` for the case instance, at the standpoint
`w` of the profile's own frame. -/
def GodNecessaryIfExistentAt (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  NecessaryIf m.ontic.frame (GodConcreteExists σ m) w

/-- Possibly some concrete GOD_4 exists: an accessible world from `w` has one. -/
def GodPossiblyExistsAt (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  PossibleExistence m.ontic.frame (GodConcreteExists σ m) w

/-- Rigidity of concrete GOD_4 presence, anchored at the standpoint: any
concrete GOD_4 existing at a world accessible from `w` is the same individual
as any concrete GOD_4 existing at `w`. It asserts no existence. Given
reflexivity at `w` it entails that at most one concrete GOD_4 exists at `w`
(`atMostOne_of_rigid`), and, if one does, that every concrete GOD_4 at an
accessible world is that one: a cross-world uniqueness commitment. Given
reflexivity at `w` it is weaker than pairwise identity across all worlds
accessible from `w`; without reflexivity the two are incomparable. The route
uses the weaker `GodPresencePersistsAt` (`persists_of_rigid`). -/
def GodPresenceRigidAt (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  ∀ v x y, m.ontic.frame.access w v → GodConcretePresent σ m x w →
    GodConcretePresent σ m y v → y = x

/-- The de dicto to de re bridge used by the route: every concrete GOD_4 at
`w` exists at every world accessible from `w` at which some concrete GOD_4
exists. It asserts no existence and no uniqueness: other concrete GOD_4 may
exist at `w` or at accessible worlds. -/
def GodPresencePersistsAt (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  ∀ x, GodConcretePresent σ m x w → ∀ v, m.ontic.frame.access w v →
    (∃ y, GodConcretePresent σ m y v) → m.ontic.ExistsAt v x

/-- Rigidity entails persistence. -/
theorem persists_of_rigid (σ : Signature) (m : Profile W σ.Being) (w : W)
    (hRigid : GodPresenceRigidAt σ m w) : GodPresencePersistsAt σ m w := by
  intro x hx v hv ⟨y, hy⟩
  have hyx : y = x := hRigid v x y hv hx hy
  exact hyx ▸ hy.2.2

/-- The uniqueness consequence of rigidity: with reflexivity at `w`, at most
one concrete GOD_4 exists at `w`. -/
theorem atMostOne_of_rigid (σ : Signature) (m : Profile W σ.Being) (w : W)
    (hReflexive : m.ontic.frame.access w w) (hRigid : GodPresenceRigidAt σ m w)
    (x y : σ.Being) (hx : GodConcretePresent σ m x w) (hy : GodConcretePresent σ m y w) :
    y = x :=
  hRigid w x y hReflexive hx hy

/-- The difference of rigidity over persistence: whenever a concrete GOD_4
exists at `w`, every world accessible from `w` has at most one concrete GOD_4.
It asserts no existence. -/
def GodPresenceUniqueWhenPresentAt (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  (∃ x, GodConcretePresent σ m x w) → ∀ v, m.ontic.frame.access w v →
    ∀ y z, GodConcretePresent σ m y v → GodConcretePresent σ m z v → y = z

/-- The certified-difference comparison (#1598): rigidity over persistence,
with no background. -/
def rigidOverPersists (σ : Signature) (m : Profile W σ.Being) (w : W) :
    TruthCore.Logic.StrengthComparison.ComparisonSpec where
  stronger := GodPresenceRigidAt σ m w
  weaker := GodPresencePersistsAt σ m w
  delta := GodPresenceUniqueWhenPresentAt σ m w

/-- Premise-free equivalence: rigidity holds exactly when persistence and the
difference hold. -/
def RigidOverPersistsExact : Prop :=
  ∀ {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W),
    GodPresenceRigidAt σ m w ↔
      GodPresencePersistsAt σ m w ∧ GodPresenceUniqueWhenPresentAt σ m w

/-- One and the same concrete GOD_4 exists at `w` and at every world accessible
from `w` (de re, accessibility-relative). No all-world existence, uniqueness
or classical attribute follows. -/
def NecessaryGodConcreteAt (σ : Signature) (m : Profile W σ.Being) (w : W) : Prop :=
  ∃ x, σ.IsGod x ∧ m.concrete x ∧ m.ontic.ExistsAt w x ∧ NecessaryAt m.ontic w x

/-- `□G` for the case instance is exactly `DeDicto` of concrete GOD_4 presence. -/
theorem box_iff_deDicto (σ : Signature) (m : Profile W σ.Being) (w : W) :
    Box m.ontic.frame (GodConcreteExists σ m) w ↔
      DeDicto m.ontic.frame (fun x v => GodConcretePresent σ m x v) w :=
  Iff.rfl

/-- With reflexivity at `w`, the persistence bridge turns the de dicto box into
an actual de re necessary concrete GOD_4. -/
theorem necessaryGod_of_box_persists (σ : Signature) (m : Profile W σ.Being) (w : W)
    (hReflexive : m.ontic.frame.access w w)
    (hPersists : GodPresencePersistsAt σ m w)
    (hBox : Box m.ontic.frame (GodConcreteExists σ m) w) :
    NecessaryGodConcreteAt σ m w := by
  obtain ⟨x, hx⟩ := hBox w hReflexive
  exact ⟨x, hx.1, hx.2.1, hx.2.2, fun v hv => hPersists x hx v hv (hBox v hv)⟩

/-! ## Finite controls -/

open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)

/-- Two candidates, both GOD_4 under this signature; the historical and creedal
fields are unused placeholders. A model of the formal premises only: it says
nothing about which candidates are God. -/
def boolSignature : Signature where
  Being := Bool
  IsGod := fun _ => True
  HasClassicalAttributes := fun _ => True
  RevealsRecognizably := fun _ => False
  jesus := false
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- Two worlds, each accessing both (reflexive and Euclidean at every world),
with the supplied existence assignment. -/
def boolProfile (ex : Bool → Bool → Prop) : Profile Bool boolSignature.Being where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := ex, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the models test the modal and identity structure, not the concrete/abstract line; a concrete conclusion here is no evidence that anything is concrete)
  grounds := fun _ _ _ => False

/-- Candidate `false` exists only at world `false`. -/
def onlyHere : Profile Bool boolSignature.Being := boolProfile fun v x => v = false ∧ x = false
/-- Nothing exists anywhere. -/
def nobody : Profile Bool boolSignature.Being := boolProfile fun _ _ => False
/-- Each world has its own candidate: `x` exists exactly at world `x`. -/
def swapped : Profile Bool boolSignature.Being := boolProfile fun v x => x = v
/-- Candidate `false` exists at both worlds; `true` exists nowhere. -/
def fixedOne : Profile Bool boolSignature.Being := boolProfile fun _ x => x = false
/-- Candidate `false` exists at both worlds; `true` exists only at world `true`. -/
def fixedPlusVisitor : Profile Bool boolSignature.Being :=
  boolProfile fun v x => x = false ∨ (x = true ∧ v = true)
/-- Candidate `false` exists at both worlds; `true` exists only at world `false`. -/
def fixedPlusLocal : Profile Bool boolSignature.Being :=
  boolProfile fun v x => x = false ∨ (x = true ∧ v = false)

/-- Omission and nonvacuity controls at standpoint `false`.
(1) `onlyHere`: every premise but `GodNecessaryIfExistentAt` holds; both conclusions fail.
(2) `nobody`: every premise but `GodPossiblyExistsAt` holds; both conclusions fail.
(3) `swapped`: every premise but `GodPresencePersistsAt` holds; both conclusions fail.
(4) `fixedOne`: all five premises and both conclusions hold (population: two
candidates, one existing at both worlds).
(5) `fixedPlusVisitor`: the GOD_4 conclusion and the persistence bridge hold
while rigidity fails: the conclusion does not entail rigidity, and persistence
is strictly weaker than rigidity.
(6) `fixedPlusLocal`: the GOD_4 conclusion and `NecessaryConcreteAt` hold while
persistence fails, so the conclusion does not entail persistence either. -/
def Controls : Prop :=
  (EuclideanAt onlyHere.ontic.frame false ∧ ActualReflexive onlyHere.ontic false ∧
    GodPossiblyExistsAt boolSignature onlyHere false ∧
    GodPresencePersistsAt boolSignature onlyHere false ∧
    ¬ GodNecessaryIfExistentAt boolSignature onlyHere false ∧
    ¬ NecessaryGodConcreteAt boolSignature onlyHere false ∧
    ¬ NecessaryConcreteAt onlyHere false) ∧
  (EuclideanAt nobody.ontic.frame false ∧ ActualReflexive nobody.ontic false ∧
    GodNecessaryIfExistentAt boolSignature nobody false ∧
    GodPresencePersistsAt boolSignature nobody false ∧
    ¬ GodPossiblyExistsAt boolSignature nobody false ∧
    ¬ NecessaryGodConcreteAt boolSignature nobody false ∧
    ¬ NecessaryConcreteAt nobody false) ∧
  (EuclideanAt swapped.ontic.frame false ∧ ActualReflexive swapped.ontic false ∧
    GodNecessaryIfExistentAt boolSignature swapped false ∧
    GodPossiblyExistsAt boolSignature swapped false ∧
    ¬ GodPresencePersistsAt boolSignature swapped false ∧
    ¬ NecessaryGodConcreteAt boolSignature swapped false ∧
    ¬ NecessaryConcreteAt swapped false) ∧
  (EuclideanAt fixedOne.ontic.frame false ∧ ActualReflexive fixedOne.ontic false ∧
    GodNecessaryIfExistentAt boolSignature fixedOne false ∧
    GodPossiblyExistsAt boolSignature fixedOne false ∧
    GodPresencePersistsAt boolSignature fixedOne false ∧
    NecessaryGodConcreteAt boolSignature fixedOne false ∧
    NecessaryConcreteAt fixedOne false) ∧
  (NecessaryGodConcreteAt boolSignature fixedPlusVisitor false ∧
    GodPresencePersistsAt boolSignature fixedPlusVisitor false ∧
    ¬ GodPresenceRigidAt boolSignature fixedPlusVisitor false) ∧
  (NecessaryGodConcreteAt boolSignature fixedPlusLocal false ∧
    NecessaryConcreteAt fixedPlusLocal false ∧
    ¬ GodPresencePersistsAt boolSignature fixedPlusLocal false)

end TruthCore.Modal.ModalOntologicalCase
