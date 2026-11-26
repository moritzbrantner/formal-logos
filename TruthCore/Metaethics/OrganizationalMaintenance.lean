module

public import Mathlib.Data.Fintype.Basic
public import TruthCore.Mereology.ArrangementDynamics

/-!
# Finite renewal and maintenance fixture

One stipulated bearer retains its identity throughout each history. The
recurrence tracks reserve, sites and recruitment. It makes no normative,
biochemical or persistence claim about actual organisms.
-/

@[expose] public section

namespace TruthCore.Metaethics.OrganizationalMaintenance

open TruthCore.Mereology.ArrangementDynamics (run)

structure State where
  reserve : Fin 5
  barrier : Bool
  nativeSite : Bool
  backupSite : Bool
  recruited : Bool
  deriving DecidableEq

structure Input where
  capacity : Fin 3 := 2
  drive : Bool := true
  regulator : Bool := true
  help : Fin 3 := 0
  shock : Bool := false
  emission : Bool := false

/-- Natural subtraction subtracts loss and drain from reserve plus inflow in
one clamp at zero. The cap at four supplies the other clamp. -/
def step (i : Input) (s : State) : State :=
  let inflow := i.capacity.val * i.drive.toNat * s.nativeSite.toNat +
    2 * s.recruited.toNat * s.backupSite.toNat + i.help.val
  let drain := 2 + 2 * (1 - s.barrier.toNat)
  let remaining := min 4 (s.reserve.val + inflow - (2 * i.shock.toNat + drain))
  let rebuilt := decide (remaining > 0)
  ⟨⟨remaining, Nat.lt_of_le_of_lt (Nat.min_le_left ..) (by decide)⟩,
    rebuilt, rebuilt, rebuilt, i.regulator && rebuilt && decide (remaining ≤ 2)⟩

def full : State := ⟨4, true, true, true, false⟩
def recruited : State := ⟨2, true, true, true, true⟩
def collapsed : State := ⟨0, false, false, false, false⟩

def trace (s : State) (inputs : List Input) : List State :=
  (List.range (inputs.length + 1)).map fun n => run step s (inputs.take n)

def reserves (s : State) (inputs : List Input) : List (Fin 5) :=
  (trace s inputs).map State.reserve

def steady (i : Input) : List (Fin 5) := reserves full (List.replicate 5 i)

theorem trajectories :
    steady {} = [4, 4, 4, 4, 4, 4] ∧
    steady { capacity := 0, regulator := false } = [4, 2, 0, 0, 0, 0] ∧
    steady { capacity := 1, regulator := false } = [4, 3, 2, 1, 0, 0] ∧
    steady { capacity := 0 } = [4, 2, 2, 2, 2, 2] ∧
    steady { capacity := 0, help := 2 } = [4, 4, 4, 4, 4, 4] ∧
    steady { drive := false, help := 2 } = [4, 4, 4, 4, 4, 4] ∧
    step { capacity := 0 } { full with reserve := 2 } = collapsed := by
  decide +kernel

theorem nativeDemand :
    let healthy : Input := { drive := false, help := 2 }
    let defect : Input := { healthy with capacity := 0 }
    let demand (i : Input) : Input := { i with drive := true, help := 0, regulator := false }
    let aided (i : Input) := List.replicate 5 i
    trace full (aided healthy) = trace full (aided defect) ∧
    (run step full (aided healthy ++ [demand healthy])).reserve = 4 ∧
    (run step full (aided defect ++ [demand defect])).reserve = 2 := by
  decide +kernel

def withShock (i : Input) : List Input := [i, i, { i with shock := true }, i, i]

theorem shocks :
    reserves full (withShock { capacity := 0 }) = [4, 2, 2, 0, 0, 0] ∧
    reserves full (withShock {}) = [4, 4, 4, 2, 4, 4] := by
  decide +kernel

theorem normalTransitions :
    step {} full = full ∧ step { shock := true } full = recruited ∧
    step {} recruited = full ∧ step { shock := true } recruited = recruited := by
  decide +kernel

theorem normalHistory (shocks : List Bool) (s : State)
    (h : s = full ∨ s = recruited) :
    let final := run step s (shocks.map fun shock => { shock := shock })
    final = full ∨ final = recruited := by
  induction shocks generalizing s with
  | nil => exact h
  | cons shock rest ih =>
    apply ih
    rcases h with rfl | rfl <;> cases shock
    · exact Or.inl normalTransitions.1
    · exact Or.inr normalTransitions.2.1
    · exact Or.inl normalTransitions.2.2.1
    · exact Or.inr normalTransitions.2.2.2

/-- The reserve bound and emission independence hold for the whole typed
space: 80 states and 72 inputs when the emitted bit is excluded. -/
theorem boundAndSignal (s : State) (i : Input) :
    (step i s).reserve.val ≤ 4 ∧
      step { i with emission := false } s = step { i with emission := true } s :=
  ⟨Nat.le_of_lt_succ (step i s).reserve.isLt, rfl⟩

theorem referenceThreshold :
    ∀ (r : Fin 5) (capacity : Fin 3), r ≠ 0 →
      let next := step { capacity := capacity, regulator := false } { full with reserve := r }
      (next.reserve = r ↔ capacity = 2) ∧ (capacity ≠ 2 → next.reserve < r) := by
  decide +kernel

end TruthCore.Metaethics.OrganizationalMaintenance
