module

public import TruthCore.Logic.EpistemicReasons
public import TruthCore.Logic.ReflectiveCoherence
public import TruthCore.Results.Logic.CorrectionCriterion.Solution

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
