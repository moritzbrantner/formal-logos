module

public import Mathlib.Data.Int.Order.Basic
public import TruthCore.Modal.CounterfactualSelection
public import TruthCore.Causality.CounterfactualDependence
public import TruthCore.Metaethics.InternalCounterfactual
public import TruthCore.Results.Modal.CounterpossibleConservativity.Solution

/-! Explicit controls for the selection profiles. The causal rival keeps the
existing model's background and repair operation fixed. -/

@[expose] public section

namespace TruthCore.Modal.CounterfactualSelectionControls

open TruthCore.Modal.CounterfactualSelection

inductive World | actual | near | far deriving DecidableEq

open World

/-- Strictly centered ascending distances from the origin at actual.
At other origins the origin remains strictly closest. -/
def rank (w v : World) : Nat :=
  if w = v then 0 else
    match v with
    | actual => 1
    | near => 2
    | far => 3

def away : Set World := {v | v ≠ actual}
def nearOnly : Set World := {near}
def farOnly : Set World := {far}
def actualOrNear : Set World := {v | v ≠ far}
def actualOnly : Set World := {actual}

theorem least_at_actual {A : Set World} {best : World} (hBest : best ∈ A)
    (hLower : ∀ v ∈ A, v ≠ best → rank actual best < rank actual v) {v : World} :
    v ∈ leastSelection rank actual A ↔ v = best := by
  constructor
  · intro hv
    by_cases he : v = best
    · exact he
    · exact (not_lt_of_ge (hv.2.2 ⟨best, hBest, rfl⟩) (hLower v hv.1 he)).elim
  · intro he
    subst v
    refine ⟨hBest, ⟨⟨best, hBest, rfl⟩, ?_⟩⟩
    rintro _ ⟨u, hu, rfl⟩
    by_cases h : u = best
    · rw [h]
    · exact le_of_lt (hLower u hu h)

theorem least_away (v : World) : v ∈ leastSelection rank actual away ↔ v = near := by
  apply least_at_actual (A := away) (best := near) (fun h => World.noConfusion h)
  intro u hu hn
  cases u with
  | actual => exact (hu rfl).elim
  | near => exact (hn rfl).elim
  | far => decide

theorem least_away_and_far (v : World) :
    v ∈ leastSelection rank actual (away ∩ farOnly) ↔ v = far := by
  apply least_at_actual
  · exact ⟨fun h => World.noConfusion h, rfl⟩
  · intro u hu hf
    exact (hf hu.2).elim

theorem least_actualOrNear (v : World) :
    v ∈ leastSelection rank actual actualOrNear ↔ v = actual := by
  apply least_at_actual (A := actualOrNear) (best := actual) (fun h => World.noConfusion h)
  intro u hu hn
  cases u with
  | actual => exact (hn rfl).elim
  | near => decide
  | far => exact (hu rfl).elim

/-- A and A ∩ B both have closest witnesses. Strengthening A to the latter
changes the selected world from near (Q) to far (outside Q). -/
theorem strengthening_fails :
    HasSelection (leastSelection rank) actual away ∧
    HasSelection (leastSelection rank) actual (away ∩ farOnly) ∧
    Would (leastSelection rank) actual away nearOnly ∧
    ¬ Would (leastSelection rank) actual (away ∩ farOnly) nearOnly := by
  exact ⟨⟨near, (least_away near).mpr rfl⟩,
    ⟨far, (least_away_and_far far).mpr rfl⟩,
    fun v hv => (least_away v).mp hv,
    fun h => World.noConfusion (h (a := far) ((least_away_and_far far).mpr rfl))⟩

/-- The same ranks and origin validate A ⇒ B and B ⇒ C, while A ⇒ C fails.
Here B includes the origin, so its closest world is actual. -/
theorem transitivity_fails :
    Would (leastSelection rank) actual away actualOrNear ∧
    Would (leastSelection rank) actual actualOrNear actualOnly ∧
    ¬ Would (leastSelection rank) actual away actualOnly := by
  refine ⟨?_, fun v hv => (least_actualOrNear v).mp hv, ?_⟩
  · intro v hv
    rw [(least_away v).mp hv]
    exact fun h => World.noConfusion h
  · intro h
    exact World.noConfusion (h (a := near) ((least_away near).mpr rfl))

def tiedRank (w v : World) : Nat :=
  if w = v then 0 else 1

theorem both_tied (v : World) (hv : v ∈ away) :
    v ∈ leastSelection tiedRank actual away := by
  refine ⟨hv, ⟨⟨v, hv, rfl⟩, ?_⟩⟩
  rintro _ ⟨u, hu, rfl⟩
  exact Nat.le_of_eq (by
    simp [tiedRank, Ne.symm (show v ≠ actual from hv), Ne.symm (show u ≠ actual from hu)])

/-- At the tested point a single supplied choice of a least A-world gives
conditional excluded middle. Retaining both least A-worlds defeats it. -/
theorem tied_excluded_middle_fails (choose : World → Set World → Option World)
    (hChoose : choose actual away = some near) :
    Would (singleSelection choose) actual away nearOnly ∧
    ¬ Would (leastSelection tiedRank) actual away nearOnly ∧
    ¬ Would (leastSelection tiedRank) actual away nearOnlyᶜ := by
  exact ⟨(single_would_iff hChoose).mpr rfl,
    fun h => World.noConfusion (h (a := far) (both_tied far (fun h => World.noConfusion h))),
    fun h => h (a := near) (both_tied near (fun h => World.noConfusion h)) rfl⟩

def integerRank (_ v : Int) : Int := v

/-- Integers have a closer antecedent world below every proposed least one.
The least-world universal is vacuous, while the limit-free clause rejects
the impossible consequent on this same inhabited antecedent. -/
theorem no_least_integer :
    NormallyPossible (⟨fun _ _ => True⟩ : Frame Int) 0 Set.univ ∧
    ¬ HasSelection (leastSelection integerRank) 0 Set.univ ∧
    Would (leastSelection integerRank) 0 Set.univ ∅ ∧
    ¬ LewisWould integerRank 0 Set.univ ∅ := by
  have noLeast : ∀ v, v ∉ leastSelection integerRank 0 Set.univ := by
    intro v hv
    have h := hv.2.2 ⟨v - 1, Set.mem_univ _, rfl⟩
    change v ≤ v - 1 at h
    omega
  refine ⟨⟨0, Set.mem_univ _, trivial⟩, fun ⟨v, hv⟩ => noLeast v hv,
    fun v hv => (noLeast v hv).elim, ?_⟩
  rintro (h | ⟨v, _, h⟩)
  · exact h 0 (Set.mem_univ _)
  · exact (lt_irrefl v) (h v (Set.mem_univ _) (fun hv => hv))

namespace Repair

open TruthCore.Modal.CounterpossibleConservativity
open TruthCore.Results.Modal.CounterpossibleConservativity
open TruthCore.Causality.CounterfactualDependence (interventionSelection intervention_would_iff)

def context : State → Bool
  | .normal u | .repair u => u

def normalAccess : Frame State :=
  ⟨fun _ v => match v with | .normal _ => True | .repair _ => False⟩

def repaired : Selector State := fun w A => Selected (context w) A

def publicSwitchOff (w : State) : State := .repair (context w)

theorem normal_witness_iff (w : State) (A : Set State) :
    NormallyPossible normalAccess w A ↔ NormalWitness A := by
  constructor
  · rintro ⟨v, hv, hAccess⟩
    cases v with
    | normal u => exact ⟨u, hv⟩
    | repair _ => exact hAccess.elim
  · rintro ⟨u, hu⟩
    exact ⟨.normal u, hu, trivial⟩

theorem repair_success : Success repaired :=
  fun w A v hv => success (context w) A v hv

theorem repair_nonempty : NonemptyForPossible normalAccess repaired :=
  fun w A h => let ⟨u, hu⟩ := (normal_witness_iff w A).mp h; ⟨.normal u, hu⟩

theorem repair_normalFirst : NormalFirst normalAccess repaired := by
  intro w A h v hv
  cases v with
  | normal _ => trivial
  | repair _ => exact hv.1 ((normal_witness_iff w A).mp h)

theorem normal_agreement_of_selectors (w : State) (A Q : Set State)
    (h : NormallyPossible normalAccess w A) :
    Would repaired w A Q ↔ Would (accessibleSelection normalAccess) w A Q := by
  rw [show Would repaired w A Q ↔ NormalConditional A Q from
    conservative (context w) A Q ((normal_witness_iff w A).mp h)]
  constructor
  · intro hQ v hv
    cases v with
    | normal u => exact hQ u hv.2
    | repair _ => exact hv.1.elim
  · intro hQ u hu
    exact hQ (a := .normal u) ⟨trivial, hu⟩

theorem repair_is_intervention (mode : Mode) (w : State) (Q : Set State) :
    Would repaired w (sourceAbsent mode) Q ↔
      Would (interventionSelection publicSwitchOff) w (sourceAbsent mode) Q :=
  (repaired_iff mode (context w) Q).trans
    (intervention_would_iff publicSwitchOff w (sourceAbsent mode) Q (repair_absence mode (context w))).symm

/-- Same natural observations, same normal worlds, same fixed-context surgery.
The public-off antecedent is normally impossible in both runs. Under normal
evaluation both consequents hold vacuously. Under repair evaluation only the
AND mechanism drops the effect, while the idle lookup retains it. -/
theorem public_off_comparison :
    (∀ u, observation .active (.normal u) = observation .idle (.normal u)) ∧
    (∀ mode, ¬ NormallyPossible normalAccess (.normal true) (sourceAbsent mode) ∧
      Would (accessibleSelection normalAccess) (.normal true)
        (sourceAbsent mode) (effectPresent mode) ∧
      Would (accessibleSelection normalAccess) (.normal true)
        (sourceAbsent mode) (effectPresent mode)ᶜ) ∧
    (Would (interventionSelection publicSwitchOff) (.normal true)
        (sourceAbsent .active) (effectPresent .active)ᶜ ∧
      ¬ Would (interventionSelection publicSwitchOff) (.normal true)
        (sourceAbsent .active) (effectPresent .active) ∧
      Would (interventionSelection publicSwitchOff) (.normal true)
        (sourceAbsent .idle) (effectPresent .idle) ∧
      ¬ Would (interventionSelection publicSwitchOff) (.normal true)
        (sourceAbsent .idle) (effectPresent .idle)ᶜ) := by
  refine ⟨normal_agreement, ?_, ?_⟩
  · intro mode
    have h : ¬ NormallyPossible normalAccess (.normal true) (sourceAbsent mode) :=
      fun hp => no_normal_absence mode ((normal_witness_iff _ _).mp hp)
    exact ⟨h, accessible_vacuity _ _ _ _ h, accessible_vacuity _ _ _ _ h⟩
  · obtain ⟨ha, hna, hi, hni⟩ := repair_discrimination
    exact ⟨(repair_is_intervention _ _ _).mp ha,
      fun h => hna ((repair_is_intervention _ _ _).mpr h),
      (repair_is_intervention _ _ _).mp hi,
      fun h => hni ((repair_is_intervention _ _ _).mpr h)⟩

end Repair

/-- The fixed moral content is tested at the actual profile and every supplied
alternative. This restates only the selection clause of the existing test. -/
theorem internal_counterfactual_profile (f : TruthCore.Metaethics.InternalCounterfactual.Frame) :
    TruthCore.Metaethics.InternalCounterfactual.Counterfactual f ↔
      f.truth.holds f.truth.actual f.content ∧
      Would (accessibleSelection ⟨fun _ _ => True⟩) f.truth.actual f.alternatives
        (fun v => f.truth.holds v f.content) := by
  exact ⟨fun ⟨ha, h⟩ => ⟨ha, fun _ hv => h _ hv.2⟩,
    fun ⟨ha, h⟩ => ⟨ha, fun v hv => h (a := v) ⟨trivial, hv⟩⟩⟩

namespace Replacement

open TruthCore.Causality.Frame
open TruthCore.Causality.CounterfactualDependence
open TruthCore.Causality.Round2PerfectionPrimacy

/-- Agent (true) exists at actual only. Effect (false) exists with the agent
at actual, drops at near, and persists without the agent at far. The second
disjunct is a supplied alternative availability condition for the same effect. -/
def existsAt (w : World) (x : Bool) : Prop :=
  if x then w = actual else w = actual ∨ w = far

def causalFrame : CausalityFrame World Bool Unit Unit where
  history := ⟨⟨⟨fun _ _ => True⟩, existsAt, fun _ _ _ => False⟩,
    fun w x _ => existsAt w x, ()⟩
  GivesAt := fun w agent effect _ => w = actual ∧ agent = true ∧ effect = false
  CausesIn := fun _ _ _ => False
  MovesIn := fun _ _ _ => False
  DependsForBeing := fun effect agent => effect = false ∧ agent = true
  PriorSimply := fun _ _ => False
  esse := ()

def canBeWithout (x y : Bool) : Prop :=
  ∃ v, existsAt v x ∧ ¬ existsAt v y

theorem selected_loss : DependenceTracksSelectedAbsence causalFrame (leastSelection rank) actual := by
  rintro _ _ ⟨rfl, rfl⟩ v hv
  have h := (least_away v).mp hv
  subst v
  rintro (h | h) <;> cases h

theorem realization : BeingWithoutHasAccessibleWitness causalFrame actual canBeWithout :=
  fun _ _ ⟨v, hx, hy⟩ => ⟨v, trivial, hx, hy⟩

/-- An omission model for accessible coverage. The local intervention and the
closest absence agree on loss. An accessible alternative retains that same
effect. This witnesses a gap in the inference under the stipulated premises. -/
theorem omission_of_coverage :
    SustainingRemovalTest causalFrame (fun _ _ => near) actual false true ∧
    DependenceTracksSelectedAbsence causalFrame (leastSelection rank) actual ∧
    BeingWithoutHasAccessibleWitness causalFrame actual canBeWithout ∧
    ¬ CoversAccessibleAbsence causalFrame (leastSelection rank) actual ∧
    ¬ DependenceExcludesBeingWithout causalFrame.DependsForBeing canBeWithout := by
  have farNoAgent : far ∈ absent causalFrame true := fun h => World.noConfusion h
  refine ⟨⟨Or.inl rfl, rfl, ⟨rfl, rfl, rfl⟩, fun h => World.noConfusion h, ?_⟩,
    selected_loss, realization, ?_, ?_⟩
  · rintro (h | h) <;> cases h
  · intro h
    exact World.noConfusion ((least_away far).mp (h true far trivial farNoAgent))
  · intro h
    exact h false true ⟨rfl, rfl⟩ ⟨far, Or.inr rfl, farNoAgent⟩

/-- Omit near, where neither being exists, from every accessible selection. -/
def skipEmptyWorld : Selector World :=
  fun w A v => v ∈ accessibleSelection causalFrame.history.ontic.frame w A ∧ v ≠ near

/-- The same frame, selector and origin witness failure of the reverse
strength implication. Neither soundness nor real-world warrant is asserted. -/
def WitnessCoverageStrictness : Prop :=
  PreservesAccessibleAbsenceWitnesses causalFrame skipEmptyWorld actual ∧
    ¬ CoversAccessibleAbsence causalFrame skipEmptyWorld actual

end Replacement

end TruthCore.Modal.CounterfactualSelectionControls
