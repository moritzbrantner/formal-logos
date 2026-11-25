module

public import Mathlib.Order.FixedPoints
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Set.Finite.Basic
public import TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource

/-!
# Closed supplier cones and retained fixed assignments

The operator and its states are structural interpretations. The designated
profile fixes actuality and the same-respect supplier relation; the operator
does not supply modal accessibility or certify an exercised productive cause.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte.ClosedSupplierCone

open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.DeEnte.ClosedEsseSource
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Causality.ClosedGroundingRoots (GroundClosedActual)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Logic (ExcludedMiddle)

variable {B P R : Type}

/-- The designated actual bearers, keeping the q.3 a.4 respect fixed. -/
def roster (p : Profile B P R) : Set B := {x | p.InAct x p.esse}

/-- If a state is confined to the outside region, every outside postfixed
substate lies in one greatest outside fixed substate. The rule needs
monotonicity only for inputs contained in that region. -/
theorem greatestFixedSubstate {rule : Set B → Set B} {U : Set B}
    (hMaps : rule U ⊆ U)
    (hMono : ∀ ⦃S T : Set B⦄, S ⊆ T → T ⊆ U → rule S ⊆ rule T) :
    ∃ V, V ⊆ U ∧ SupplierStateFixed rule V ∧
      ∀ S, S ⊆ U → S ⊆ rule S → S ⊆ V := by
  let restricted : Set B →o Set B :=
    ⟨fun S => rule (S ∩ U),
      fun _ _ h => hMono (fun _ hx => ⟨h hx.1, hx.2⟩) (fun _ hx => hx.2)⟩
  have hm : ∀ S, restricted S ⊆ U := fun _ =>
    (hMono (fun _ hx => hx.2) (Set.Subset.rfl)).trans hMaps
  have he : restricted restricted.gfp = restricted.gfp := restricted.map_gfp
  have hV : restricted.gfp ⊆ U := he ▸ hm restricted.gfp
  refine ⟨restricted.gfp, hV, ?_, ?_⟩
  · change rule (restricted.gfp ∩ U) = restricted.gfp at he
    rw [Set.inter_eq_left.mpr hV] at he
    exact fun x => Set.ext_iff.mp he x
  · intro S hS hPost
    apply restricted.le_gfp
    change S ⊆ rule (S ∩ U)
    rw [Set.inter_eq_left.mpr hS]
    exact hPost

/-- Guard the original actual supplier menu only where the proof uses it:
at the deleted input and for members of the tested cone. -/
theorem greatestOutsideClosedCone (p : Profile B P R) {rule : Set B → Set B}
    {C : Set B}
    (hClosed : GroundClosedActual (esseCauseGraph p) () C)
    (hRootless : ∀ x ∈ C, ∃ c, ActualEsseCause p c x)
    (hRange : rule (roster p \ C) ⊆ roster p)
    (hGuard : ∀ x ∈ C, (∃ c, ActualEsseCause p c x) →
      x ∈ rule (roster p \ C) → ∃ c ∈ roster p \ C, ActualEsseCause p c x)
    (hMono : ∀ ⦃S T : Set B⦄, S ⊆ T → T ⊆ roster p \ C → rule S ⊆ rule T) :
    ∃ V, V ⊆ roster p \ C ∧ SupplierStateFixed rule V ∧
      ∀ S, S ⊆ roster p \ C → S ⊆ rule S → S ⊆ V := by
  apply greatestFixedSubstate (hMono := hMono)
  intro x hx
  refine ⟨hRange hx, fun hxC => ?_⟩
  obtain ⟨c, hc, hCause⟩ := hGuard x hxC (hRootless x hxC) hx
  exact hc.2 (hClosed.2 x c hxC ⟨hCause.2.1, hCause.2.1, hCause⟩)

/-- Cone-wise non-deletion on the candidate states that retain all outside
postfixed witnesses. This can express populated-only non-deletion if an
independent outside postfixed witness is available for each tested cone. -/
def ConeRetention (p : Profile B P R) (rule : Set B → Set B) : Prop :=
  ∀ C : Set B, C.Nonempty → GroundClosedActual (esseCauseGraph p) () C →
    (∀ x ∈ C, ∃ c, ActualEsseCause p c x) →
    ∀ V ⊆ roster p, SupplierStateFixed rule V →
      (∀ S, S ⊆ roster p \ C → S ⊆ rule S → S ⊆ V) →
      (C ∩ V).Nonempty

/-- CCR already rules out the nonempty rootless collections tested by
cone-wise non-deletion, regardless of the activation rule. -/
theorem coneRetentionOfClosed (p : Profile B P R) (rule : Set B → Set B)
    (hClosed : ClosedActualEsseCollectionsRooted p) :
    ConeRetention p rule := by
  intro C hPop hC hSup
  obtain ⟨x, hx⟩ := hPop
  have hNoRoot : ∀ y, C y → ¬ ActualRoot (esseCauseGraph p) () y := by
    intro y hy hRoot
    obtain ⟨c, hc⟩ := hSup y hy
    exact hRoot.2 c ⟨hc.2.1, hc.2.1, hc⟩
  exact (hClosed C hC hNoRoot x hx).elim

/-- Relative to the structural hypotheses, cone-wise non-deletion is
equivalent to the exact CCR predicate. The reverse direction depends on
no structure of the rule, so this equivalence supplies no independent
justification of the non-deletion premise. -/
theorem closedIffConeRetention (p : Profile B P R) (rule : Set B → Set B)
    (em : ExcludedMiddle)
    (hRange : ∀ U ⊆ roster p, rule U ⊆ roster p)
    (hGuard : ∀ U ⊆ roster p, ∀ x, (∃ c, ActualEsseCause p c x) →
      x ∈ rule U → ∃ c ∈ U, ActualEsseCause p c x)
    (hMono : ∀ C : Set B, GroundClosedActual (esseCauseGraph p) () C →
      (∀ x ∈ C, ∃ c, ActualEsseCause p c x) →
      ∀ ⦃S T : Set B⦄, S ⊆ T → T ⊆ roster p \ C → rule S ⊆ rule T) :
    ClosedActualEsseCollectionsRooted p ↔ ConeRetention p rule := by
  refine ⟨coneRetentionOfClosed p rule, ?_⟩
  intro hRetain C hClosed hNoRoot x hx
  let cone : Set B := C
  have hs : ∀ y ∈ cone, ∃ c, ActualEsseCause p c y := by
    intro y hy
    rcases em (∃ c, ActualEsseCause p c y) with h | h
    · exact h
    · exact (hNoRoot y hy ⟨hClosed.1 y hy, fun c hc => h ⟨c, hc.2.2⟩⟩).elim
  have hout : roster p \ cone ⊆ roster p := fun _ hy => hy.1
  obtain ⟨V, hV, hFixed, hGreatest⟩ :=
    greatestOutsideClosedCone p (C := cone) hClosed hs (hRange _ hout)
      (fun y _ => hGuard _ hout y) (hMono C hClosed hs)
  obtain ⟨y, hyC, hyV⟩ := hRetain C ⟨x, hx⟩ hClosed hs V (hV.trans hout) hFixed hGreatest
  exact (hV hyV).2 hyC

/-- With the component guard, a single jointly retaining output is equivalent
to stability at the deleted input. No deterministic selection is required. -/
theorem stableOutsideIffRetained {D : Set B → Set B → Prop} {U : Set B}
    (hGuard : ∀ T, D U T → T ⊆ U) :
    D U U ↔ ∃ T, D U T ∧ U ⊆ T := by
  constructor
  · intro h
    exact ⟨U, h, Set.Subset.rfl⟩
  · rintro ⟨T, hT, hRetain⟩
    have hEq := Set.Subset.antisymm (hGuard T hT) hRetain
    exact hEq ▸ hT

/-- A nonempty directed family that individually covers a finite retained
assignment contains a single output covering it all. -/
theorem jointRetentionOfFiniteDirected {U : Set B} {outputs : Set (Set B)}
    (hFinite : U.Finite) (hOutputs : outputs.Nonempty)
    (hDirected : Directed (· ⊆ ·) (fun T : outputs => T.1))
    (hCover : ∀ x ∈ U, ∃ T ∈ outputs, x ∈ T) :
    ∃ T ∈ outputs, U ⊆ T := by
  classical
  let : Nonempty outputs := ⟨⟨hOutputs.choose, hOutputs.choose_spec⟩⟩
  let pick (x : U) : outputs :=
    ⟨(hCover x x.2).choose, (hCover x x.2).choose_spec.1⟩
  let chosen : Finset outputs := hFinite.toFinset.attach.image fun x =>
    pick ⟨x.1, hFinite.mem_toFinset.mp x.2⟩
  obtain ⟨T, hT⟩ := hDirected.finset_le chosen
  refine ⟨T.1, T.2, fun x hx => ?_⟩
  have hxFin := hFinite.mem_toFinset.mpr hx
  have hMem : pick ⟨x, hx⟩ ∈ chosen :=
    Finset.mem_image.mpr ⟨⟨x, hxFin⟩, Finset.mem_attach _ _, rfl⟩
  exact hT _ hMem (hCover x hx).choose_spec.2

namespace Control

open TruthCore.Causality.ClosedGroundingRoots.Control (mediateFoundation)

/-- Use the existing roster-only profile, with the exact same successors
and isolated actual identity bearer. -/
def tailProfile : Profile (Option Nat) Bool Unit :=
  controlProfile (mediateFoundation.grounds ())

/-- The independently activated root and the rootless strict chain can be
evaluated together or with just the independently activated root. -/
def tailRule (S : Set (Option Nat)) : Set (Option Nat) :=
  {x | match x with
    | none => True
    | some n => some (n + 1) ∈ S}

theorem tailCauseIff {c x : Option Nat} :
    ActualEsseCause tailProfile c x ↔
      ∃ n, c = some (n + 1) ∧ x = some n := by
  constructor
  · exact fun h => h.2.2.2
  · rintro ⟨n, rfl, rfl⟩
    exact ⟨fun he => Nat.succ_ne_self n (Option.some.inj he),
      trivial, trivial, n, rfl, rfl⟩

/-- Strict supplier priority, the uniform supplier guard, monotonicity and
a populated actual roster with an uncaused identity bearer still allow
a populated fixed omission of a whole supplier-complete cone. -/
theorem strictTailOmission :
    (∀ c x, ActualEsseCause tailProfile c x →
      x.getD 0 < c.getD 0) ∧
    Monotone tailRule ∧
    (∀ (S : Set (Option Nat)) x, (∃ c, ActualEsseCause tailProfile c x) →
      x ∈ tailRule S → ∃ c ∈ S, ActualEsseCause tailProfile c x) ∧
    SupplierStateFixed tailRule (roster tailProfile) ∧
    SupplierStateFixed tailRule ({none} : Set (Option Nat)) ∧
    (none ∈ ({none} : Set (Option Nat)) ∧ ∀ c, ¬ ActualEsseCause tailProfile c none) ∧
    ¬ ClosedActualEsseCollectionsRooted tailProfile := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro c x h
    obtain ⟨n, rfl, rfl⟩ := tailCauseIff.mp h
    exact Nat.lt_succ_self n
  · intro S T h x hx
    cases x with
    | none => trivial
    | some n => exact h hx
  · intro S x hIn hx
    obtain ⟨c, hc⟩ := hIn
    obtain ⟨n, rfl, rfl⟩ := tailCauseIff.mp hc
    exact ⟨some (n + 1), hx, hc⟩
  · intro x
    cases x <;> exact Iff.rfl
  · intro x
    cases x with
    | none => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | some n =>
      change (some (n + 1) = none) ↔ (some n = none)
      constructor <;> intro h <;> contradiction
  · intro c hc
    obtain ⟨_, _, hn⟩ := tailCauseIff.mp hc
    exact nomatch hn
  · intro h
    let cone : Set (Option Nat) := {x | ∃ n, x = some n}
    refine h cone ⟨fun _ _ => ⟨trivial, trivial⟩, ?_⟩ ?_ (some 0) ⟨0, rfl⟩
    · intro x y _ hy
      obtain ⟨n, hn, _⟩ := tailCauseIff.mp hy.2.2
      exact ⟨n + 1, hn⟩
    · rintro x ⟨n, rfl⟩ hroot
      exact hroot.2 (some (n + 1))
        ⟨trivial, trivial, tailCauseIff.mpr ⟨n, rfl, rfl⟩⟩

/-- At the designated roster, keep the strict-tail rule. Otherwise,
inhibit the isolated bearer when that very bearer is present. -/
noncomputable def inhibitedTailRule (S : Set (Option Nat)) : Set (Option Nat) :=
  open Classical in
  if S = roster tailProfile then tailRule S else
    {x | match x with
      | none => none ∉ S
      | some n => some (n + 1) ∈ S}

/-- Even preserving the actual guard, the designated fixed state and the
strict carrier, forward closure of the outside region alone gives no fixed
substate there. The isolated bearer toggles in that region. -/
theorem guardedInhibitionWithoutOutsideFixed :
    SupplierStateFixed inhibitedTailRule (roster tailProfile) ∧
    (∀ (S : Set (Option Nat)) x, (∃ c, ActualEsseCause tailProfile c x) →
      x ∈ inhibitedTailRule S → ∃ c ∈ S, ActualEsseCause tailProfile c x) ∧
    inhibitedTailRule ({none} : Set (Option Nat)) ⊆ {none} ∧
    ¬ ∃ V : Set (Option Nat), V ⊆ {none} ∧ SupplierStateFixed inhibitedTailRule V := by
  classical
  have hNotRoster {S : Set (Option Nat)} (hS : S ⊆ {none}) :
      S ≠ roster tailProfile := by
    intro he
    have h : (some 0 : Option Nat) ∈ S := by rw [he]; trivial
    have hNone := hS h
    change some 0 = none at hNone
    cases hNone
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simpa [inhibitedTailRule] using strictTailOmission.2.2.2.1 x
  · intro S x hIn hx
    obtain ⟨c, hc⟩ := hIn
    obtain ⟨n, rfl, rfl⟩ := tailCauseIff.mp hc
    have hs : some (n + 1) ∈ S := by
      by_cases he : S = roster tailProfile
      · simpa [inhibitedTailRule, he, tailRule] using hx
      · simpa [inhibitedTailRule, he] using hx
    exact ⟨_, hs, hc⟩
  · intro x hx
    rw [inhibitedTailRule, ite_eq_right (hNotRoster (Set.Subset.rfl))] at hx
    cases x with
    | none => rfl
    | some n =>
      change some (n + 1) = none at hx
      cases hx
  · rintro ⟨V, hV, hFixed⟩
    have h := hFixed none
    rw [inhibitedTailRule, ite_eq_right (hNotRoster hV)] at h
    exact (fun hn => hn (h.mp hn)) (fun hn => (h.mpr hn) hn)

/-- The family of singleton outputs covers both retained members, while
no one output covers them jointly. -/
theorem individualRetentionWithoutJoint :
    let allowed : Set Bool → Prop := fun T => ∃ x : Bool, T = {x}
    (∀ x, ∃ T, allowed T ∧ x ∈ T) ∧
      ¬ ∃ T, allowed T ∧ (Set.univ : Set Bool) ⊆ T := by
  dsimp
  refine ⟨fun x => ⟨{x}, ⟨x, rfl⟩, rfl⟩, ?_⟩
  rintro ⟨_, ⟨x, rfl⟩, hAll⟩
  cases x with
  | false => exact Bool.noConfusion (hAll (Set.mem_univ true) : true = false)
  | true => exact Bool.noConfusion (hAll (Set.mem_univ false) : false = true)

/-- Directedness and individual coverage do not suffice for an infinite
retained state. Finite outputs can be joined by union but cannot cover
the whole infinite carrier in a single output. -/
theorem finiteOutputsWithoutInfiniteJoint [Infinite B] :
    let outputs : Set (Set B) := {S | S.Finite}
    Directed (· ⊆ ·) (fun T : outputs => T.1) ∧
      (∀ x, ∃ T ∈ outputs, x ∈ T) ∧
      ¬ ∃ T ∈ outputs, (Set.univ : Set B) ⊆ T := by
  dsimp
  refine ⟨?_, fun x => ⟨{x}, Set.finite_singleton x, rfl⟩, ?_⟩
  · intro S T
    exact ⟨⟨S.1 ∪ T.1, S.2.union T.2⟩,
      fun _ hx => Or.inl hx, fun _ hx => Or.inr hx⟩
  · rintro ⟨T, hFinite, hCover⟩
    exact Set.infinite_univ (hFinite.subset hCover)

end Control

end TruthCore.Latin.Aquinas.DeEnte.ClosedSupplierCone
