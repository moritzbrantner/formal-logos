module

public import TruthCore.Logic.EpistemicReasons
public import TruthCore.Logic.ReflectiveCoherence
public import TruthCore.Results.Logic.CorrectionCriterion.Solution
public import Mathlib.Data.Rat.Defs

/-!
# Acceptance and validity under a fixed interpretation

These comparisons for #1990 use classical two-atom semantics to test classification
of modus ponens and affirming the consequent. The coverage theorem applies to
interpretations that can isolate each omitted valuation. The final comparisons
test which Boolean connectives satisfy specified soundness conditions.
-/

@[expose] public section

namespace TruthCore.Logic.LogicalPsychologism

open TruthCore.Logic.ReflectiveCoherence
open TruthCore.Logic.CorrectionCriterion
open TruthCore.Logic.EpistemicReasons

abbrev Valuation := Bool × Bool
abbrev Content := Valuation → Bool

def atomP : Content := fun w => w.1
def atomQ : Content := fun w => w.2
def impPQ : Content := fun w => (!w.1) || w.2

def sem : Semantics Valuation Content where
  trueAt := fun w p => p w = true
  neg := fun p w => !(p w)
  neg_true_iff := by
    intro w p
    change (!(p w) = true) ↔ ¬ (p w = true)
    cases p w <;> decide

inductive Rule | mp | ac deriving DecidableEq

def premises : Rule → Worldview Content
  | .mp => fun c => c = atomP ∨ c = impPQ
  | .ac => fun c => c = atomQ ∨ c = impPQ

def conclusion : Rule → Content
  | .mp => atomQ
  | .ac => atomP

def valid (i : Rule) : Prop := Entails sem (premises i) (conclusion i)

theorem mpValid : valid .mp := by
  intro w hw
  have hp : w.1 = true := hw atomP (Or.inl rfl)
  have hi : ((!w.1) || w.2) = true := hw impPQ (Or.inr rfl)
  change w.2 = true
  simpa [hp] using hi

theorem acInvalid : ¬ valid .ac := by
  intro h
  have hm : Models sem (premises .ac) (false, true) := by
    intro c hc
    change c = atomQ ∨ c = impPQ at hc
    rcases hc with rfl | rfl <;> rfl
  have hbad : false = true := h (false, true) hm
  exact Bool.false_ne_true hbad

-- A supplied psychological projection identifies the two rules.
-- E may contain richer data than one acceptance bit.
theorem equalDataNoCriterion {E : Type} (observe : Rule → E)
    (same : observe .mp = observe .ac) :
    ¬ AdmitsCriterion observe valid := by
  intro h
  have inv :=
    (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
      Rule E observe valid).mp h
  exact acInvalid ((inv .mp .ac same).mp mpValid)

-- An acceptance-only projection can fail even if everybody approves.
def allAccepted : Rule → Bool := fun _ => true
def noneAccepted : Rule → Bool := fun _ => false

theorem unanimityNoCriterion :
    ¬ AdmitsCriterion allAccepted valid :=
  equalDataNoCriterion allAccepted rfl

theorem omissionControl :
    allAccepted .mp ≠ noneAccepted .mp ∧ valid .mp ∧ ¬ valid .ac := by
  exact ⟨by decide, mpValid, acInvalid⟩

-- A richer projection distinguishes the two inputs; no metaphysical
-- reduction or explanation is implied by this extensional classifier.
theorem richerProjectionControl :
    AdmitsCriterion (fun r : Rule => r) valid :=
  ⟨valid, fun _ => Iff.rfl⟩

-- F6 and pure semantic validity are separate. The empty/nonempty Reason
-- fields are stipulated controls, not claims about actual human subjects.
theorem f6OmissionControls :
    valid .mp ∧ ¬ valid .ac ∧
      ¬ ThereAreEpistemicReasons (fun (_ : Unit) (_ : Unit) => False) ∧
      ThereAreEpistemicReasons (fun (_ : Unit) (_ : Unit) => True) := by
  refine ⟨mpValid, acInvalid, ?_, ⟨(), (), trivial⟩⟩
  rintro ⟨_, _, h⟩
  exact h

def restrictedEntails {W C : Type} (S : Semantics W C)
    (scope : W → Prop) (Γ : Worldview C) (p : C) : Prop :=
  ∀ w, scope w → Models S Γ w → S.trueAt w p

theorem omittedValuationFalsePositive {W C : Type} (S : Semantics W C)
    (scope : W → Prop) (top : C) (hTop : ∀ w, S.trueAt w top)
    (v : W) (hMiss : ¬ scope v)
    (hSeparate : ∃ q : C, ∀ w, S.trueAt w q ↔ w ≠ v) :
    ∃ q : C,
      restrictedEntails S scope (fun p => p = top) q ∧
      ¬ Entails S (fun p => p = top) q := by
  obtain ⟨q, hq⟩ := hSeparate
  refine ⟨q, ?_, ?_⟩
  · intro w hw _
    apply (hq w).2
    intro hEq
    exact hMiss (hEq ▸ hw)
  · intro h
    have hm : Models S (fun p => p = top) v := by
      intro p hp
      subst p
      exact hTop v
    exact ((hq v).1 (h v hm)) rfl

theorem separatingScopeExactIffCoverage {W C : Type} (S : Semantics W C)
    (scope : W → Prop) (top : C) (hTop : ∀ w, S.trueAt w top)
    (hSeparate : ∀ v : W, ∃ q : C, ∀ w, S.trueAt w q ↔ w ≠ v) :
    (∀ (Γ : Worldview C) (q : C),
      restrictedEntails S scope Γ q → Entails S Γ q) ↔
      ∀ v, scope v := by
  classical
  constructor
  · intro h v
    apply Classical.byContradiction
    intro hMiss
    obtain ⟨q, hScoped, hNot⟩ :=
      omittedValuationFalsePositive S scope top hTop v hMiss (hSeparate v)
    exact hNot (h (fun p => p = top) q hScoped)
  · intro h Γ q hScoped v hm
    exact hScoped v (h v) hm

-- The content is a truth function on the existing four-valuations carrier.
-- The premise sets vary only by the selected connective's interpretation.
def tableContent (f : Bool → Bool → Bool) : Content :=
  fun w => f w.1 w.2

def mpFor (f : Bool → Bool → Bool) : Prop :=
  Entails sem (fun c => c = atomP ∨ c = tableContent f) atomQ

def acFor (f : Bool → Bool → Bool) : Prop :=
  Entails sem (fun c => c = atomQ ∨ c = tableContent f) atomP

theorem mpForIff (f : Bool → Bool → Bool) :
    mpFor f ↔ f true false = false := by
  constructor
  · intro h
    cases hf : f true false with
    | false => rfl
    | true =>
      have hm : Models sem
          (fun c => c = atomP ∨ c = tableContent f) (true, false) := by
        intro c hc
        rcases hc with rfl | rfl
        · rfl
        · exact hf
      exact (Bool.false_ne_true (h (true, false) hm)).elim
  · intro hf w hm
    have hp : w.1 = true := hm atomP (Or.inl rfl)
    have hc : f w.1 w.2 = true := hm (tableContent f) (Or.inr rfl)
    change w.2 = true
    cases hq : w.2 with
    | false =>
      simp [hp, hq, hf] at hc
    | true => rfl

theorem acForIff (f : Bool → Bool → Bool) :
    acFor f ↔ f false true = false := by
  constructor
  · intro h
    cases hf : f false true with
    | false => rfl
    | true =>
      have hm : Models sem
          (fun c => c = atomQ ∨ c = tableContent f) (false, true) := by
        intro c hc
        rcases hc with rfl | rfl
        · rfl
        · exact hf
      exact (Bool.false_ne_true (h (false, true) hm)).elim
  · intro hf w hm
    have hq : w.2 = true := hm atomQ (Or.inl rfl)
    have hc : f w.1 w.2 = true := hm (tableContent f) (Or.inr rfl)
    change w.1 = true
    cases hp : w.1 with
    | false =>
      simp [hp, hq, hf] at hc
    | true => rfl

def materialTable (p q : Bool) : Bool := (!p) || q
def equivalenceTable (p q : Bool) : Bool := p == q

theorem diagonalAndMPFork (f : Bool → Bool → Bool)
    (h00 : f false false = true) (h11 : f true true = true)
    (hMP : mpFor f) :
    f = materialTable ∨ f = equivalenceTable := by
  have h10 := (mpForIff f).mp hMP
  cases h01 : f false true with
  | false =>
    right
    funext p q
    cases p <;> cases q <;>
      simp [equivalenceTable, h00, h01, h10, h11]
  | true =>
    left
    funext p q
    cases p <;> cases q <;>
      simp [materialTable, h00, h01, h10, h11]

theorem bothSoundSelectsEquivalence (f : Bool → Bool → Bool)
    (h00 : f false false = true) (h11 : f true true = true)
    (hMP : mpFor f) (hAC : acFor f) :
    f = equivalenceTable := by
  have h01 := (acForIff f).mp hAC
  have h10 := (mpForIff f).mp hMP
  funext p q
  cases p <;> cases q <;>
    simp [equivalenceTable, h00, h01, h10, h11]

theorem offDiagonalSelectsMaterial (f : Bool → Bool → Bool)
    (h00 : f false false = true) (h11 : f true true = true)
    (h01 : f false true = true) (hMP : mpFor f) :
    f = materialTable := by
  have h10 := (mpForIff f).mp hMP
  funext p q
  cases p <;> cases q <;>
    simp [materialTable, h00, h01, h10, h11]

end TruthCore.Logic.LogicalPsychologism

namespace TruthCore.Logic.LogicalPsychologism

def valuations : List Valuation := [(false, false), (false, true), (true, false), (true, true)]

def truePremises (r : Rule) (w : Valuation) : Bool :=
  (if r = .mp then atomP w else atomQ w) && impPQ w

def failures (r : Rule) : List Valuation :=
  valuations.filter fun w => truePremises r w && !(conclusion r w)

def boolMaps : List (Bool → Bool) :=
  (List.range 4).map fun n b => n.testBit b.toNat

def classifiers (mp ac : Bool) : List (Bool → Bool) :=
  boolMaps.filter fun classify => classify mp && !classify ac

theorem finiteRules :
    failures .mp = [] ∧ failures .ac = [(false, true)] ∧
    truePremises .mp (true, true) ∧ truePremises .ac (true, true) ∧
    conclusion .mp (true, true) ∧ conclusion .ac (true, true) ∧
    ∀ mp ac, (classifiers mp ac).length = (if mp = ac then 0 else 1) := by
  decide +kernel

def scopes : List (List Valuation) :=
  (List.range 16).map fun n =>
    (valuations.zip (List.range 4)).filterMap fun (w, bit) =>
      if n.testBit bit then some w else none

theorem properScopeCount :
    (scopes.filter fun scope => !scope.isEmpty && scope.length != 4).length = 14 := by
  decide +kernel

/-- Every proper scope has the same nonvacuous omission witness used in the
enumeration. The existing general theorem supplies the exact counterexample. -/
theorem valuationOmission (scope : Valuation → Prop) (v : Valuation) (omitted : ¬ scope v) :
    ∃ q : Content,
      restrictedEntails sem scope (fun p => p = (fun _ => true)) q ∧
      ¬ TruthCore.Logic.ReflectiveCoherence.Entails sem (fun p => p = (fun _ => true)) q :=
  omittedValuationFalsePositive sem scope (fun _ => true) (fun _ => rfl) v omitted
    ⟨fun w => decide (w ≠ v), fun _ => Iff.of_eq decide_eq_true_eq⟩

def transition (p q c : Bool) : Bool × Bool × Bool :=
  (p || (q && c), q || (p && c), c)

/-- Indexed in order (false,false), (false,true), (true,false), (true,true). -/
def table (n : Nat) : Valuation → Bool := fun (p, q) => n.testBit (2 * p.toNat + q.toNat)

def tables : List Nat := List.range 16

def mpTest (f : Content) : Bool := valuations.all fun (p, q) => !(p && f (p, q)) || q
def acTest (f : Content) : Bool := valuations.all fun (p, q) => !(q && f (p, q)) || p

theorem connectiveCensus :
    (valuations.flatMap fun (p, q) => [false, true].map (transition p q)).length = 8 ∧
    (∀ b : Bool, materialTable b b ∧ equivalenceTable b b ∧
      transition b b (materialTable b b) = transition b b (equivalenceTable b b)) ∧
    (∀ i ∈ tables, mpTest (table i) = !table i (true, false) ∧
      acTest (table i) = !table i (false, true)) ∧
    (tables.filter fun i => table i (false, false) && table i (true, true) && mpTest (table i)) =
      [9, 11] ∧
    (∀ w ∈ valuations, table 9 w = equivalenceTable w.1 w.2 ∧
      table 11 w = materialTable w.1 w.2) ∧
    acTest (table 9) ∧ ¬ acTest (table 11) ∧
    ¬ table 9 (false, true) ∧ table 11 (false, true) := by
  decide +kernel

def mass (n : ℚ) (w : Valuation) : ℚ :=
  if w = (true, true) then (n - 3) / n else 1 / n

def selectedMass (n : ℚ) (p : Content) : ℚ :=
  ((valuations.filter p).map (mass n)).sum

def acConditionalError (n : ℚ) : ℚ :=
  selectedMass n (fun w => truePremises .ac w && !atomP w) /
    selectedMass n (truePremises .ac)

theorem reliabilitySamples :
    ∀ n ∈ ([4, 10, 100, 1000, 1000000] : List ℚ),
      selectedMass n (fun _ => true) = 1 ∧
      (∀ w ∈ valuations, 0 < mass n w) ∧
      acConditionalError n = 1 / (n - 2) ∧ 0 < acConditionalError n ∧
      selectedMass n atomP = (n - 2) / n ∧
      1 - acConditionalError n = (n - 3) / (n - 2) ∧
      (selectedMass n atomP < 1 - acConditionalError n ↔ 4 < n) := by
  decide +kernel

theorem uniformReliability :
    tables.all (fun i => tables.all fun j =>
      let error := fun w => table i w && !table j w
      decide (selectedMass 4 error = 0) == valuations.all (fun w => !error w)) = true := by
  decide +kernel

end TruthCore.Logic.LogicalPsychologism
