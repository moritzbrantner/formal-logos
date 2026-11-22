module

public import TruthCore.Causality.GodNamingSenses
public import TruthCore.Results.Modal.RigidDesignation.Solution

@[expose] public section

namespace TruthCore.Results.Causality.GodNamingSenses

open TruthCore.Causality.GodNamingSenses
open TruthCore.Causality.GodNamingSenses.Control
open TruthCore.Modal.RigidDesignation (Name RigidAt CoRef)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Isabelle.AFP.GoedelGod (Box)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessarySenseFork (RootFacts NecessaryRootBoxK necessaryAt_iff_boxExistsAt)
open TruthCore.Case.Catholicism (Signature IsTheOneGod)

/-- A reference-fixed name is rigid for the unique existing satisfier at its
reference world. -/
theorem referenceFixed_rigid {W B : Type} (o : Ontic W B) (D : Description W B) (w₀ : W)
    (x : B) (hx : UniqueExistentAt o D w₀ x) (w : W) :
    RigidAt o (ReferenceFixedName o D w₀) w x := by
  intro v _ y
  constructor
  · rintro ⟨hy, hex⟩
    have hyx : y = x := hx.2.2 y hy.1 hy.2.1
    subst hyx
    exact ⟨rfl, hex⟩
  · rintro ⟨rfl, hex⟩
    exact ⟨hx, hex⟩

/-- Necessity of identity for two reference-fixed names with one actual
bearer, from the rigid-designation library's `laws`. -/
theorem referenceFixed_identity {W B : Type} (o : Ontic W B) (D D' : Description W B)
    (w₀ : W) (x : B) (hx : UniqueExistentAt o D w₀ x) (hx' : UniqueExistentAt o D' w₀ x) :
    (∀ v, o.frame.access w₀ v → o.ExistsAt v x →
        CoRef (ReferenceFixedName o D w₀) (ReferenceFixedName o D' w₀) v) ∧
      (Box o.frame (CoRef (ReferenceFixedName o D w₀) (ReferenceFixedName o D' w₀)) w₀ ↔
        NecessaryAt o w₀ x) := by
  obtain ⟨hiff, hpersist, _⟩ :=
    TruthCore.Results.Modal.RigidDesignation.laws W B o o.frame
      (ReferenceFixedName o D w₀) (ReferenceFixedName o D' w₀) w₀ x
      ⟨hx, hx.2.1⟩ ⟨hx', hx'.2.1⟩
      (referenceFixed_rigid o D w₀ x hx w₀) (referenceFixed_rigid o D' w₀ x hx' w₀)
  exact ⟨hpersist, hiff⟩

theorem laws : Control.Laws := by
  intro W B o D D' w₀ x
  exact ⟨fun hx w => referenceFixed_rigid o D w₀ x hx w,
    fun y => ⟨fun h => ⟨h, h.2.1⟩, fun h => h.1⟩,
    fun hx hx' => referenceFixed_identity o D D' w₀ x hx hx'⟩

/-- The route's root facts make `n` the unique existing GOD_4 at `w`. -/
theorem rootFacts_unique {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (n : σ.Being) (h : RootFacts σ m w n) :
    UniqueExistentAt m.ontic (fun _ => σ.IsGod) w n :=
  ⟨h.2.1, h.1.1.2, fun y hy _ => h.2.2.1 y hy⟩

/-- For a root, strict necessary self-co-designation of the reference-fixed
name "God" is necessary existence of the root. -/
theorem rigidBox_iff {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (n : σ.Being) (h : RootFacts σ m w n) :
    Box m.ontic.frame
        (CoRef (ReferenceFixedName m.ontic (fun _ => σ.IsGod) w)
          (ReferenceFixedName m.ontic (fun _ => σ.IsGod) w)) w ↔
      NecessaryAt m.ontic w n :=
  (referenceFixed_identity m.ontic _ _ w n (rootFacts_unique σ m w n h)
    (rootFacts_unique σ m w n h)).2

/-- Rigid-name reading gives the route's box K node. -/
theorem rigidToBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (h : NecessaryRootRigidName σ m w) (CN : σ.Being → σ.Being → Prop) :
    NecessaryRootBoxK σ m w CN := by
  obtain ⟨n, hRoot, hBox⟩ := h
  exact ⟨n, (necessaryAt_iff_boxExistsAt m.ontic w n).mp
    ((rigidBox_iff σ m w n hRoot).mp hBox), hRoot⟩

theorem rigidIffBoxK : Control.RigidIffBoxK := by
  intro W σ m w CN
  constructor
  · exact fun h => rigidToBoxK σ m w h CN
  · rintro ⟨n, hNec, hRoot⟩
    exact ⟨n, hRoot, (rigidBox_iff σ m w n hRoot).mpr
      ((necessaryAt_iff_boxExistsAt m.ontic w n).mpr hNec)⟩

/-- Descriptive reading plus the no-other-possible-God bridge gives the box K
node: at each accessible world the existing unique God-satisfier is actually
GOD_4, hence the one GOD_4, the root. -/
theorem descToBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being)
    (hDesc : NecessaryRootDescriptiveName σ m w GodAt)
    (hNoOther : NoOtherPossibleGod σ m w GodAt)
    (CN : σ.Being → σ.Being → Prop) :
    NecessaryRootBoxK σ m w CN := by
  obtain ⟨n, hRoot, hBox⟩ := hDesc
  refine ⟨n, ?_, hRoot⟩
  intro v hv
  obtain ⟨y, hy, _⟩ := hBox v hv
  have hyGod : σ.IsGod y := hNoOther v hv y hy.1 hy.2.1
  have hyn : y = n := hRoot.2.2.1 y hyGod
  subst hyn
  exact hy.2.1

/-- The box K node plus essential Godhood and the no-other-possible-God bridge
gives the descriptive reading. -/
theorem boxKToDesc {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (GodAt : Description W σ.Being) (CN : σ.Being → σ.Being → Prop)
    (hBoxK : NecessaryRootBoxK σ m w CN)
    (hEss : GodhoodEssentialToGod σ m w GodAt)
    (hNoOther : NoOtherPossibleGod σ m w GodAt) :
    NecessaryRootDescriptiveName σ m w GodAt := by
  obtain ⟨n, hNec, hRoot⟩ := hBoxK
  refine ⟨n, hRoot, ?_⟩
  intro v hv
  have hex : m.ontic.ExistsAt v n := hNec v hv
  have hName : DescriptiveName m.ontic GodAt v n :=
    ⟨hEss n hRoot.2.1 v hv hex, hex,
      fun y hy hey => hRoot.2.2.1 y (hNoOther v hv y hy hey)⟩
  exact ⟨n, hName, hName⟩

theorem separation : Control.Separation := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the descriptive node in the migrating model, with root `false`
    refine ⟨false, ⟨⟨⟨trivial, rfl⟩, fun _ h => h.2.2⟩, rfl, fun g h => h, rfl⟩, ?_⟩
    intro v _
    refine ⟨v, ?_, ?_⟩ <;>
      exact ⟨rfl, rfl, fun y hy _ => hy⟩
  · rintro ⟨n, hNec, hRoot⟩
    have hn : n = false := hRoot.2.1
    subst hn
    exact Bool.noConfusion (show true = false from hNec true trivial)
  · intro h
    exact Bool.noConfusion (show true = false from h true trivial true rfl rfl)
  · refine ⟨false, fun _ _ => trivial, ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩, rfl,
      fun g h => h, rfl⟩
  · intro v _ y hy _
    exact hy.2
  · rintro ⟨n, _, hBox⟩
    obtain ⟨y, hy, _⟩ := hBox true trivial
    exact Bool.noConfusion (show true = false from hy.1.1)
  · intro h
    exact Bool.noConfusion (show true = false from (h false rfl true trivial trivial).1)
  · exact ⟨rfl, rfl, fun y hy _ => hy⟩
  · rintro y ⟨hy, hex⟩
    have : y = false := hy.1
    subst this
    exact Bool.noConfusion (show true = false from hex)
  · exact ⟨false, ⟨rfl, trivial, fun y hy _ => hy⟩, ⟨rfl, trivial, fun y hy _ => hy⟩⟩
  · trivial
  · rintro ⟨y, hy, hy'⟩
    have h1 : y = false := hy.1
    have h2 : y = true := hy'.1
    exact Bool.noConfusion (h1.symm.trans h2)
  · exact ⟨false, ⟨⟨rfl, trivial, fun y hy _ => hy⟩, trivial⟩,
      ⟨⟨rfl, trivial, fun y hy _ => hy⟩, trivial⟩⟩

theorem nonvacuity : Control.Nonvacuity := by
  have hRoot : RootFacts boolSignature fullProfile false false :=
    ⟨⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩, rfl, fun g h => h, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rigidIffBoxK Bool boolSignature fullProfile false (fun _ _ => False)).mpr
      ⟨false, fun _ _ => trivial, hRoot⟩
  · refine ⟨false, hRoot, fun v _ => ?_⟩
    exact ⟨false, ⟨rfl, trivial, fun y hy _ => hy⟩, ⟨rfl, trivial, fun y hy _ => hy⟩⟩
  · intro v _ y hy _
    exact hy
  · intro g hg v _ _
    exact hg

theorem checks : Control.Checks :=
  ⟨laws, rigidIffBoxK, separation, nonvacuity⟩

end TruthCore.Results.Causality.GodNamingSenses
