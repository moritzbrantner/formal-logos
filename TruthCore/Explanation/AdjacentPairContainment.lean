module

public import TruthCore.Explanation.NoFoundationLawChaos

/-! Which range of alternative outputs is needed for each obstruction?

This refines #1809/#1874 over their existing Boolean traces, selector admission,
local transition Profiles and record-only estimators. No new causal relation,
modal accessibility, source identity or probability is introduced. In particular,
a Profile sees one current Boolean value: failure of every restrictive such
Profile need not exclude a deterministic rule with a larger state or memory.
-/

@[expose] public section

namespace TruthCore.Explanation.AdjacentPairContainment

open TruthCore.Modern.Hume.Induction (Trace)
open TruthCore.Epistemology.UltimateExplanation (Profile Follows)
open TruthCore.Explanation.LawActuality (UsesRecord)
open TruthCore.Explanation.NoFoundationLawChaos

/-- Both values occur at the selected coordinate among complete histories
admitted after the same observed prefix. This requires populated alternatives,
not merely an unconstrained value slot. -/
def BitRich (allowed : Trace → Prop) (n k : Nat) : Prop :=
  ∀ b : Bool, ∃ f, Admitted allowed n f ∧ f k = b

/-- At each fully unobserved adjacent pair, all four assignments have admitted
complete witnesses. Witnesses may differ between pairs; this does not license
joint realization of an arbitrary three-bit or longer prescription. -/
def AdjacentPairRich (allowed : Trace → Prop) (n : Nat) : Prop :=
  ∀ t a b, n+1 ≤ t → ∃ f, Admitted allowed n f ∧ f t = a ∧ f (t+1) = b

/-- Every one-bit, first-order, possibly time-dependent Profile holding on
every admitted complete history permits all fully unobserved adjacent pairs.
This concerns the supplied observation resolution, not all possible laws. -/
def ProfileObstruction (allowed : Trace → Prop) (n : Nat) : Prop :=
  ∀ q : Profile, (∀ f, Admitted allowed n f → Follows q f) →
    ∀ t a b, n+1 ≤ t → q.step t a b

/-- No estimator depending only on the common recorded prefix is exactly
correct at k on every admitted history. This is a uniform equality condition,
not a norm of fallible epistemic warrant or a probability-of-error claim. -/
def ForecastObstruction (allowed : Trace → Prop) (n k : Nat) : Prop :=
  ∀ predict : Trace → Bool, UsesRecord n predict →
    ¬ ∀ f, Admitted allowed n f → predict f = f k

/-- Exact weakest output-range conditions within the stated model classes,
and their place below #1874's finite-pattern premise. The final implication
consumes its existing populated one-step-to-finite theorem. Prefix closure
and whole-infinite-suffix freedom are unnecessary for these obstructions. -/
def ExposureCertificate : Prop :=
  (∀ allowed n, AdjacentPairRich allowed n ↔ ProfileObstruction allowed n) ∧
  (∀ allowed n k, BitRich allowed n k ↔ ForecastObstruction allowed n k) ∧
  (∀ allowed n, FiniteRich allowed n → AdjacentPairRich allowed n) ∧
  (∀ allowed n, AdjacentPairRich allowed n →
    ∀ k, n+1 ≤ k → BitRich allowed n k) ∧
  (∀ allowed n, (∃ f, Admitted allowed n f) → OneStepRich allowed n →
    AdjacentPairRich allowed n)

/-- Two possible constant suffixes after the fixed observed prefix. -/
def constantClass (n : Nat) (f : Trace) : Prop :=
  ∃ b : Bool, f = splice n (fun _ => b)

/-- The three-periodic pattern a,b,a XOR b, with four possible seed pairs. -/
def parityCycle (a b : Bool) (t : Nat) : Bool :=
  if t % 3 = 0 then a else if t % 3 = 1 then b else a.xor b

def parityTrace (n : Nat) (a b : Bool) : Trace :=
  splice n (fun t => parityCycle a b (t-(n+1)))

/-- Exactly the four seeded suffixes. The observation cutoff is fixed when
this selector is chosen; this is not one selector rich after every new record. -/
def parityClass (n : Nat) (f : Trace) : Prop :=
  ∃ a b : Bool, f = parityTrace n a b

/-- A fixed rule with memory: the next value is the XOR of the two preceding
values. It applies entirely after the common recorded prefix. -/
def TwoStepRule (n : Nat) (f : Trace) : Prop :=
  ∀ t, n+1 ≤ t → f (t+2) = (f t).xor (f (t+1))

/-- Strictness with concrete complete-history selectors. Constant suffixes
allow either value at each future coordinate but not every adjacent pair.
The parity selector allows every adjacent pair yet obeys a fixed two-step
rule; its first two suffix values determine the whole history. It excludes
some three-bit pattern, hence both finite and whole-suffix richness fail.
All claims concern these mathematical interpretations, not real possibility. -/
def MemoryControls : Prop :=
  (∀ n k, n+1 ≤ k → BitRich (constantClass n) n k) ∧
  (∀ n, ¬ AdjacentPairRich (constantClass n) n) ∧
  (∀ n, AdjacentPairRich (parityClass n) n) ∧
  (∀ n f, Admitted (parityClass n) n f → TwoStepRule n f) ∧
  (∀ n f g, Admitted (parityClass n) n f → Admitted (parityClass n) n g →
    f (n+1) = g (n+1) → f (n+2) = g (n+2) → f = g) ∧
  (∀ n, ¬ FiniteRich (parityClass n) n ∧ ¬ WholeSuffixRich (parityClass n) n)

end TruthCore.Explanation.AdjacentPairContainment
