module

public import TruthCore.Explanation.PSRLaterAxes
public import TruthCore.Causality.SelectedAncestry

/-! Objective probabilistic order: physical outcomes are NOT metaphysical worlds.
The PMF is mathematical data. Its interpretation as an operative propensity
requires a separate realization relation. This is an extension of the later
PSR axes and selected-ancestry route, not an attribution or a new root. -/

@[expose] public section

namespace TruthCore.Explanation.ObjectiveProbability

open TruthCore.Explanation.PSRStrength
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.SelectedAncestry
open TruthCore.Logic (ExcludedMiddle)
open scoped ENNReal

/-- Two strictly positive normalized binary outcome laws. The index names a
favored PHYSICAL outcome, not a world sampled from metaphysical possibilities. -/
noncomputable def binaryLaw (high : Bool) : PMF Bool :=
  PMF.ofFintype (fun b => if b = high then (3 : ℝ≥0∞) / 4 else 1 / 4) (by
    rw [Fintype.sum_bool]
    have h : (3 : ℝ≥0∞) / 4 + 1 / 4 = 1 := by
      rw [← ENNReal.add_div]
      have he : (3 : ℝ≥0∞) + 1 = 4 := by norm_num
      rw [he]
      exact ENNReal.div_self (by norm_num) (by norm_num)
    cases high
    · change (1 : ℝ≥0∞) / 4 + 3 / 4 = 1
      rw [add_comm]
      exact h
    · exact h)

/-- Likelihood of a specified finite ordered record under an explicitly
stationary independent-trials model. The product rule is a model assumption,
not derived from observed frequencies. -/
noncomputable def iidLikelihood {O : Type} (μ : PMF O) : List O → ℝ≥0∞
  | [] => 1
  | x :: xs => μ x * iidLikelihood μ xs

/-- Both distributions have full point support. Every finite observation record,
hence the very same empirical frequencies calculated from that record, has
nonzero likelihood in both IID models. The one-trial prediction differs. -/
def BinaryControls : Prop :=
  (∀ h b, 0 < binaryLaw h b) ∧
  binaryLaw true true = 3 / 4 ∧ binaryLaw false true = 1 / 4 ∧
  binaryLaw true ≠ binaryLaw false ∧
  (∀ xs, iidLikelihood (binaryLaw true) xs ≠ 0 ∧
    iidLikelihood (binaryLaw false) xs ≠ 0)

/-- The observed record and epistemic credence do not define the physical law.
Operative is a primitive claim that a distribution is physically instantiated;
it is not a synonym for mathematical consistency or actual causal supply.
No probability measure over W is assumed. -/
structure LawProfile (W O : Type) where
  propensity : W → PMF O
  credence : W → PMF O
  record : W → List O
  admitted : W → O → Prop
  operative : W → Prop

/-- Same essential description implies the same law wherever operative.
Whether a proposed description is genuinely intrinsic, necessary and
exhaustive of the powers is a separate philosophical premise. -/
def FixedBy {W O E : Type} (L : LawProfile W O) (essence : W → E) : Prop :=
  ∀ w v, L.operative w → L.operative v →
    essence w = essence v → L.propensity w = L.propensity v

/-- The matched contexts retain all physical outcomes, a fixed epistemic
credence, and exactly the same finite record. The second bit independently
controls realization of the otherwise identical mathematical law. -/
noncomputable def matched (xs : List Bool) : LawProfile (Bool × Bool) Bool where
  propensity w := binaryLaw w.1
  credence _ := binaryLaw true
  record _ := xs
  admitted _ _ := True
  operative w := w.2 = true

/-- A law's exact obtaining is a fact, not the existence of a reified abstract
measure. This adapter uses the existing PSR Arena, with no causal relation
and no claim of metaphysical admissibility of the matched contexts. -/
inductive LawFact | base | actualLaw | operative deriving DecidableEq

def lawArena (reason : Bool) : Arena (Bool × Bool) Empty LawFact :=
  basic everywhere
    (fun w f => match f with
      | .base => True
      | .actualLaw => w.1 = true ∧ w.2 = true
      | .operative => w.2 = true)
    (fun w r f => reason = true ∧ r = .base ∧ f = .actualLaw ∧
      w.1 = true ∧ w.2 = true)
    (fun r f => r = f)

/-- A reason fixes the law among accessible operative alternatives in which
the reason obtains. This asks for determination of the distribution, NOT
necessitation of each stochastic outcome. -/
def FixesLaw {W B F O : Type} (A : Arena W B F) (L : LawProfile W O)
    (a : W) (r : F) : Prop :=
  ∀ v, Access A a v → A.holds v r → L.operative v →
    L.propensity v = L.propensity a

/-- Exact bridge to the contingent-fact PSR: the law fact denotes the obtaining
of THIS distribution, not merely the existence of its mathematical object. -/
def RepresentsLaw {W B F O : Type} (A : Arena W B F) (L : LawProfile W O)
    (f : F) (μ : PMF O) : Prop :=
  ∀ w, A.holds w f ↔ L.operative w ∧ L.propensity w = μ

/-- Productive source is kept on the existing concrete grounding profile.
A concrete realization relation (not an abstract measure's existence) is
supplied as an application premise. The selected bearer is the SAME witness
in the realization and its complete actual concrete ancestry. -/
def RealizationRoute : Prop :=
  ∀ (W B O : Type) (m : Profile W B) (w : W) (selected : B)
    (μ : PMF O) (realizes : B → PMF O → Prop),
    (∀ b q, realizes b q → ActualConcrete m w b) →
    realizes selected μ → ConeWellFounded m w selected →
    ConeContingentGrounded m w selected → ExcludedMiddle →
    realizes selected μ ∧ NecessaryRootAncestor m w selected

/-- The law data alone cannot infer physical realization or distinguish causal
supply. The latter control attaches the same physical PMF to the existing
actual target2 exercises of the single and source-free chain configurations.
No claim is made that the attached PMF is produced by either exercise. -/
noncomputable def ExerciseLaw (_ : TruthCore.Explanation.UltimateAdequacy.Kind) : PMF Bool :=
  binaryLaw true

def ProductiveControl : Prop :=
  let U := TruthCore.Explanation.UltimateAdequacy.Kind.single
  let C := TruthCore.Explanation.UltimateAdequacy.Kind.chain
  ExerciseLaw U = ExerciseLaw C ∧
    (TruthCore.Explanation.UltimateAdequacy.exercise U).occurs
      (TruthCore.Explanation.UltimateAdequacy.exercise U).actual 2 ∧
    (TruthCore.Explanation.UltimateAdequacy.exercise C).occurs
      (TruthCore.Explanation.UltimateAdequacy.exercise C).actual 2 ∧
    TruthCore.Causality.DerivativeJointPower.Supply
      (TruthCore.Explanation.UltimateAdequacy.groups U)
      (TruthCore.Explanation.UltimateAdequacy.intrinsic U) 2 ∧
    ¬ TruthCore.Causality.DerivativeJointPower.Supply
      (TruthCore.Explanation.UltimateAdequacy.groups C)
      (TruthCore.Explanation.UltimateAdequacy.intrinsic C) 2

/-- Closed conditional certificate. The law-identification and realization
bridges are not established of reality. In particular neither an impersonal
necessitated distribution nor an intentionally selected law is excluded. -/
def Certificate : Prop :=
  BinaryControls ∧
  (∀ xs : List Bool,
    let L := matched xs
    let a : Bool × Bool := (true, true)
    let v : Bool × Bool := (false, true)
    let absent : Bool × Bool := (true, false)
    L.operative a ∧ L.operative v ∧
    (∀ b, L.admitted a b ↔ L.admitted v b) ∧
    L.record a = L.record v ∧ L.credence a = L.credence v ∧
    L.propensity a ≠ L.propensity v ∧
    L.propensity a = L.propensity absent ∧ ¬ L.operative absent ∧
    FixedBy L Prod.fst ∧ ¬ FixedBy L (fun _ => ()) ∧
    RepresentsLaw (lawArena false) L .actualLaw (L.propensity a) ∧
    Contingent (lawArena false) a .actualLaw ∧
    ¬ ContingentPSR (lawArena false) a ∧
    (lawArena true).explains a .base .actualLaw ∧
    ¬ FixesLaw (lawArena true) L a .base) ∧
  (∀ (W B F O : Type) (A : Arena W B F) (L : LawProfile W O)
    (a v : W) (f : F),
    RepresentsLaw A L f (L.propensity a) →
    L.operative a → Access A a v → L.operative v →
    L.propensity v ≠ L.propensity a →
    Contingent A a f ∧ (ContingentPSR A a → Explained A a f)) ∧
  (∀ (W O E : Type) (L : LawProfile W O) (essence : W → E) (a v : W),
    FixedBy L essence → L.operative a → L.operative v →
    L.propensity a ≠ L.propensity v → essence a ≠ essence v) ∧
  ProductiveControl ∧ RealizationRoute

end TruthCore.Explanation.ObjectiveProbability
