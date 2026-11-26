module

public import TruthCore.Causality.ProductiveDeletion

/-!
# Seven-event census for source-specific productive deletion

The two fixed esse records are 0 → 1 and 0 → 2. The optional records
have effects only at intermediate 5 and target 6. When the productive
input 3 is cut, its seed remains and its contributor records are removed.
All assignments are structural fixtures for the actuality and esse note.
-/

@[expose] public section

namespace TruthCore.Causality.ProductiveDeletionCensus

open TruthCore.Causality.JointGroups (Groups)
open TruthCore.Causality.DerivativeJointPower (Supply)
open TruthCore.Causality.ParticularActuality (restrict)
open TruthCore.Causality.ProductiveDeletion (SuppliedStep withoutInputs)

/-- Optional record numbers follow the original enumeration order. -/
abbrev Assignment := Fin 13 → Bool

/-- Each removal policy is also used to assign the initial supply after the
fixed esse records have been processed. Retention additionally seeds event 5. -/
inductive Context where
  | original | productiveCut | bearerCut | retention
  deriving DecidableEq

def keeps (c : Context) (g : Fin 13) : Bool :=
  if g == 0 || g == 1 || g == 10 then c != .productiveCut else true

/-- Base events are 0, 3, 4 and the bearers' derived esse 1 and 2.
Only the bearer cut deletes the fixed record supplying 1. -/
def base (c : Context) (e : Fin 7) : Bool :=
  e == 0 || e == 2 || e == 3 || e == 4 || (e == 1 && c != .bearerCut)

/-- Each bit denotes one optional record. The retention context seeds 5.
These four clauses distinguish independently supplied endpoints from the
two directions of feedback. -/
def startIntermediate (c : Context) (on : Assignment) : Bool :=
  c == .retention || (keeps c 0 && on 0) || on 2 || (base c 1 && on 4) || on 6

def startTarget (c : Context) (on : Assignment) : Bool :=
  (keeps c 1 && on 1) || on 3 || (base c 1 && on 5) || on 7 || (keeps c 10 && on 10)

def intermediateToTarget (c : Context) (on : Assignment) : Bool :=
  on 8 || (base c 1 && on 11) || on 12

def supply (c : Context) (on : Assignment) (e : Fin 7) : Bool :=
  base c e ||
    (e == 5 && (startIntermediate c on || (startTarget c on && on 9))) ||
    (e == 6 && (startTarget c on || (startIntermediate c on && intermediateToTarget c on)))

abbrev Event := Fin 7
abbrev Record := Fin 15

def contributors (g : Record) : List Event :=
  ![[3], [3], [4], [4], [1], [1], [2], [2], [5], [6],
    [3, 4], [1, 5], [2, 5], [0], [0]] g

def effect (g : Record) : Event := ![5, 6, 5, 6, 5, 6, 5, 6, 6, 5, 6, 6, 6, 1, 2] g

def admitted (c : Context) (on : Assignment) (g : Record) : Bool :=
  if h : g.val < 13 then keeps c ⟨g.val, h⟩ && on ⟨g.val, h⟩
  else g == 14 || c != .bearerCut

def records (c : Context) (on : Assignment) : Groups Event Record where
  contributors := fun g e => e ∈ contributors g
  enablers := fun _ => ∅
  effect := effect
  admitted := fun g => admitted c on g = true

def seed (c : Context) (e : Event) : Prop :=
  e = 0 ∨ e = 3 ∨ e = 4 ∨ (c = .retention ∧ e = 5)

theorem productiveCutRecords (on : Assignment) :
    records .productiveCut on = withoutInputs (records .original on) ({3} : Set Event) := by
  unfold records withoutInputs restrict
  congr 1
  funext g
  apply propext
  change admitted .productiveCut on g = true ↔
    admitted .original on g = true ∧ ∀ u ∈ contributors g, u ≠ 3
  fin_cases g <;> simp [contributors, admitted, keeps]

theorem bearerCutRecords (on : Assignment) :
    records .bearerCut on = restrict (records .original on) (fun g => effect g ≠ 1) := by
  unfold records restrict
  congr 1
  funext g
  apply propext
  fin_cases g <;> simp [effect, admitted, keeps]

private theorem supplyClosed (c : Context) (on : Assignment) (g : Record)
    (active : admitted c on g = true)
    (inputs : ∀ e ∈ contributors g, supply c on e = true) :
    supply c on (effect g) = true := by
  fin_cases g <;> cases c <;>
    simp [admitted, contributors, effect, keeps, supply, base, startIntermediate,
      startTarget, intermediateToTarget] at active inputs ⊢ <;> grind

private theorem supplySound {c : Context} {on : Assignment} {e : Event}
    (h : Supply (records c on) (seed c) e) : supply c on e = true := by
  induction h with
  | intrinsic e h =>
    rcases h with rfl | rfl | rfl | ⟨rfl, rfl⟩ <;> rfl
  | joint g active _ ih => exact supplyClosed c on g active ih

private theorem fire {c : Context} {on : Assignment} (g : Record)
    (active : admitted c on g = true)
    (inputs : ∀ e ∈ contributors g, Supply (records c on) (seed c) e) :
    Supply (records c on) (seed c) (effect g) :=
  Supply.joint g active inputs

private theorem baseSupplied {c : Context} {on : Assignment} {e : Event}
    (h : base c e = true) : Supply (records c on) (seed c) e := by
  have input0 : Supply (records c on) (seed c) 0 := .intrinsic 0 (Or.inl rfl)
  fin_cases e
  · exact input0
  · refine fire 13 ?_ (by simpa [contributors] using input0)
    cases c <;> simp [base, admitted] at h ⊢
  · exact fire 14 rfl (by simpa [contributors] using input0)
  · exact .intrinsic 3 (Or.inr (Or.inl rfl))
  · exact .intrinsic 4 (Or.inr (Or.inr (Or.inl rfl)))
  · simp [base] at h
  · simp [base] at h

private theorem firstIntermediate {c : Context} {on : Assignment}
    (h : startIntermediate c on = true) : Supply (records c on) (seed c) 5 := by
  simp only [startIntermediate, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((hc | ⟨hk, ho⟩) | ho) | ⟨hb, ho⟩) | ho
  · have hc' : c = .retention := by simpa using hc
    exact .intrinsic 5 (Or.inr (Or.inr (Or.inr ⟨hc', rfl⟩)))
  · exact fire 0 (by change (keeps c 0 && on 0) = true; simp [hk, ho]) (by
      simpa [contributors] using (baseSupplied (e := 3) (c := c) (on := on) rfl))
  · exact fire 2 ho (by
      simpa [contributors] using (baseSupplied (e := 4) (c := c) (on := on) rfl))
  · exact fire 4 ho (by simpa [contributors] using (baseSupplied (on := on) hb))
  · exact fire 6 ho (by
      simpa [contributors] using (baseSupplied (e := 2) (c := c) (on := on) rfl))

private theorem firstTarget {c : Context} {on : Assignment}
    (h : startTarget c on = true) : Supply (records c on) (seed c) 6 := by
  simp only [startTarget, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((⟨hk, ho⟩ | ho) | ⟨hb, ho⟩) | ho) | ⟨hk, ho⟩
  · exact fire 1 (by change (keeps c 1 && on 1) = true; simp [hk, ho]) (by
      simpa [contributors] using (baseSupplied (e := 3) (c := c) (on := on) rfl))
  · exact fire 3 ho (by
      simpa [contributors] using (baseSupplied (e := 4) (c := c) (on := on) rfl))
  · exact fire 5 ho (by simpa [contributors] using (baseSupplied (on := on) hb))
  · exact fire 7 ho (by
      simpa [contributors] using (baseSupplied (e := 2) (c := c) (on := on) rfl))
  · exact fire 10 (by change (keeps c 10 && on 10) = true; simp [hk, ho]) (by
      simpa [contributors] using
        (And.intro (baseSupplied (e := 3) (c := c) (on := on) rfl)
          (baseSupplied (e := 4) (c := c) (on := on) rfl)))

private theorem throughIntermediate {c : Context} {on : Assignment}
    (hs : Supply (records c on) (seed c) 5) (h : intermediateToTarget c on = true) :
    Supply (records c on) (seed c) 6 := by
  simp only [intermediateToTarget, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (ho | ⟨hb, ho⟩) | ho
  · exact fire 8 ho (by simpa [contributors] using hs)
  · exact fire 11 ho (by simpa [contributors] using And.intro (baseSupplied hb) hs)
  · exact fire 12 ho (by
      simpa [contributors] using And.intro (baseSupplied (e := 2) rfl) hs)

/-- The fixture evaluator calculates inductive supply for each event. -/
theorem supply_iff (c : Context) (on : Assignment) (e : Event) :
    supply c on e = true ↔ Supply (records c on) (seed c) e := by
  refine ⟨?_, supplySound⟩
  intro h
  fin_cases e
  · exact baseSupplied rfl
  · exact baseSupplied (by simpa [supply] using h)
  · exact baseSupplied rfl
  · exact baseSupplied rfl
  · exact baseSupplied rfl
  · simp [supply, base] at h
    rcases h with h | ⟨ht, hg⟩
    · exact firstIntermediate h
    · exact fire 9 hg (by simpa [contributors] using (firstTarget ht))
  · simp [supply, base] at h
    rcases h with h | ⟨hi, hg⟩
    · exact firstTarget h
    · exact throughIntermediate (firstIntermediate hi) hg

/-- In the original and retention contexts, any nonempty path from 3 to 6
first reaches 6 directly or takes a step through 5. A feedback edge from 6
to 5 cannot precede the first visit to 6. -/
def selectedPath (c : Context) (on : Assignment) : Bool :=
  on 1 || on 10 || (on 0 && intermediateToTarget c on)

private theorem pathEnvelope {c : Context} {on : Assignment} {v : Event}
    (h : Relation.TransGen (SuppliedStep (records c on) (seed c)) 3 v) :
    (v = 5 ∧ (on 0 = true ∨ selectedPath c on = true)) ∨
      (v = 6 ∧ selectedPath c on = true) := by
  have extend {u v : Event}
      (hu : u = 3 ∨ (u = 5 ∧ (on 0 = true ∨ selectedPath c on = true)) ∨
        (u = 6 ∧ selectedPath c on = true))
      (hstep : SuppliedStep (records c on) (seed c) u v) :
      (v = 5 ∧ (on 0 = true ∨ selectedPath c on = true)) ∨
        (v = 6 ∧ selectedPath c on = true) := by
    obtain ⟨g, active, rfl, member, inputs⟩ := hstep
    change admitted c on g = true at active
    change u ∈ contributors g at member
    change (∀ e ∈ contributors g, Supply (records c on) (seed c) e) at inputs
    change (effect g = 5 ∧ _) ∨ (effect g = 6 ∧ _)
    have computed (e : Event) (he : e ∈ contributors g) := supplySound (inputs e he)
    clear inputs
    fin_cases g <;> cases c <;>
      simp [contributors, effect, admitted, keeps, selectedPath, intermediateToTarget, base, supply]
        at active member hu computed ⊢ <;> grind
  induction h with
  | single h => exact extend (Or.inl rfl) h
  | tail _ h ih => exact extend (Or.inr ih) h

private theorem step {c : Context} {on : Assignment} {u : Event} (g : Record)
    (active : admitted c on g = true) (member : u ∈ contributors g)
    (inputs : ∀ e ∈ contributors g, Supply (records c on) (seed c) e) :
    SuppliedStep (records c on) (seed c) u (effect g) :=
  ⟨g, active, rfl, member, inputs⟩

/-- Positive selected-input reachability in the two uncut record contexts. -/
theorem selectedPath_iff (c : Context) (on : Assignment)
    (uncut : c = .original ∨ c = .retention) :
    selectedPath c on = true ↔ Relation.TransGen (SuppliedStep (records c on) (seed c)) 3 6 := by
  refine ⟨?_, fun h => ?_⟩
  · have input3 : Supply (records c on) (seed c) 3 := baseSupplied rfl
    have input4 : Supply (records c on) (seed c) 4 := baseSupplied rfl
    have keep (g : Record) (h : g.val < 13) (ho : on ⟨g.val, h⟩ = true) :
        admitted c on g = true := by
      rcases uncut with rfl | rfl <;> simp [admitted, h, keeps, ho]
    intro h
    simp only [selectedPath, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (ho | ho) | ⟨h0, indirectly⟩
    · exact .single (step 1 (keep 1 (by decide) ho) (by decide)
        (by simpa [contributors] using input3))
    · exact .single (step 10 (keep 10 (by decide) ho) (by decide)
        (by simpa [contributors] using And.intro input3 input4))
    · have active := keep 0 (by decide) h0
      have inputs : ∀ e ∈ contributors 0, Supply (records c on) (seed c) e := by
        simpa [contributors] using input3
      have p : Relation.TransGen (SuppliedStep (records c on) (seed c)) 3 5 :=
        .single (step 0 active (by decide) inputs)
      have input5 : Supply (records c on) (seed c) 5 := fire 0 active inputs
      simp only [intermediateToTarget, Bool.or_eq_true, Bool.and_eq_true] at indirectly
      rcases indirectly with (ho | ⟨hb, ho⟩) | ho
      · exact p.tail (step 8 ho (by decide) (by simpa [contributors] using input5))
      · exact p.tail (step 11 ho (by decide)
          (by simpa [contributors] using And.intro (baseSupplied hb) input5))
      · exact p.tail (step 12 ho (by decide)
          (by simpa [contributors] using And.intro (baseSupplied (e := 2) rfl) input5))
  · rcases pathEnvelope h with ⟨impossible, _⟩ | ⟨_, found⟩
    · contradiction
    · exact found

def assignment (mask : Nat) : Assignment := fun g => mask.testBit g.val

/-- Per-assignment results in census order. -/
def outcomes (on : Assignment) : List Bool :=
  let supplied := supply .original on 6
  let survives := supply .productiveCut on 6
  let path := selectedPath .original on
  [supplied, supplied && !survives, supplied && !survives && !path,
    supplied && survives && path, supplied && !(supply .bearerCut on 6) && !path]

def countBlock (start : Nat) : List Nat :=
  (List.range 256).foldl (fun counts offset =>
    List.zipWith (fun count test => count + test.toNat)
      counts (outcomes (assignment (start + offset)))) [0, 0, 0, 0, 0]

def censusCounts : List Nat :=
  (List.range 32).foldl (fun totals block =>
    List.zipWith (· + ·) totals (countBlock (block * 256))) [0, 0, 0, 0, 0]

theorem census :
    32 * 256 = 8192 ∧ censusCounts = [8146, 194, 0, 6846, 98] := by
  decide +kernel

theorem bearersPreserved (on : Assignment) :
    supply .productiveCut on 1 = true ∧ supply .productiveCut on 2 = true := by
  exact ⟨rfl, rfl⟩

theorem retention :
    let historical : Assignment := fun g => g == 0 || g == 8
    let present : Assignment := fun g => g == 8
    selectedPath .original historical = true ∧
    supply .retention present 6 = true ∧ selectedPath .retention present = false := by
  decide

end TruthCore.Causality.ProductiveDeletionCensus
