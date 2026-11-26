module

public import TruthCore.Causality.StructuralCausalModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
Finite identification controls. The two reported coordinates are X (false)
and Y (true). A fair bit and an independent uniform four-way draw generate
a one-in-four disturbance. Three distinct mechanisms share the joint law.
-/

@[expose] public section

namespace TruthCore.Causality.StructuralCausalModel

open scoped ENNReal NNReal

/-- One root and a second equation allowed to read its value. -/
def binary (root : Bool) (rootEq : U → Bool) (childEq : U → Bool → Bool) :
    Model Bool U Bool where
  graph := ⟨fun p v => p = root ∧ v ≠ root⟩
  acyclic := Subrelation.wf (r := fun p v : Bool =>
      (if p = root then 0 else 1) < (if v = root then 0 else 1))
    (fun ⟨hp, hv⟩ => by simp [hp, hv]) (measure (fun p : Bool => if p = root then 0 else 1)).wf
  equation := fun v u parents =>
    if h : v = root then rootEq u else childEq u (parents ⟨root, rfl, h⟩)

theorem binary_root (root : Bool) (f : U → Bool) (g : U → Bool → Bool)
    (u : U) (s : Setting Bool Bool) :
    (binary root f g).response u s root = (s root).getD (f u) := by
  cases h : s root with
  | none => simpa [binary, h] using (binary root f g).response_unforced u s h
  | some b => simpa [h] using (binary root f g).response_forced u s h

theorem binary_child (root child : Bool) (ne : child ≠ root)
    (f : U → Bool) (g : U → Bool → Bool) (u : U) (s : Setting Bool Bool) :
    (binary root f g).response u s child = (s child).getD (g u ((s root).getD (f u))) := by
  cases h : s child with
  | none =>
    rw [(binary root f g).response_unforced u s h]
    simp [binary, ne, ← binary_root root f g u s]
  | some b => simpa [h] using (binary root f g).response_forced u s h

namespace Identification

abbrev Context := Bool × Fin 4

noncomputable def fraction (numerator denominator : ℕ) : ℝ≥0∞ :=
  ((numerator : ℝ≥0) / (denominator : ℝ≥0) : ℝ≥0)

noncomputable def contextLaw : PMF Context :=
  PMF.ofFintype (fun _ => fraction 1 8) (by
    rw [Finset.sum_const, Finset.card_univ, show Fintype.card Context = 8 by decide]
    rw [fraction, nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul, ← ENNReal.coe_one]
    congr 1
    norm_num)

/-- Point-mass product factorization for ALL values of the two exogenous
coordinates. On these finite carriers this is independence. -/
theorem independent_coordinates (b : Bool) (n : Fin 4) :
    contextLaw (b, n) =
      (contextLaw.map Prod.fst) b * (contextLaw.map Prod.snd) n := by
  classical
  cases b <;> fin_cases n <;>
    simp only [contextLaw, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
      Fin.sum_univ_succ, PMF.ofFintype_apply]
  all_goals
    simp
    simp only [fraction, ← ENNReal.coe_add, ← ENNReal.coe_mul, ENNReal.coe_inj]
    norm_num

def disturbance (u : Context) : Bool := u.2 == 0

def forward : Model Bool Context Bool :=
  binary false Prod.fst (fun u x => x.xor (disturbance u))

def reverse : Model Bool Context Bool :=
  binary true Prod.fst (fun u y => y.xor (disturbance u))

/-- Common exogenous bit, used in BOTH equations. Its independent companion
is the noise, so independent background coordinates do not rule out a
shared exogenous parent. -/
def confounded : Model Bool Context Bool where
  graph := ⟨fun _ _ => False⟩
  acyclic := ⟨fun v => Acc.intro v (fun _ h => h.elim)⟩
  equation := fun v u _ => if v then u.1.xor (disturbance u) else u.1

def observe (values : Bool → Bool) : Bool × Bool := (values false, values true)

private theorem forward_response (u : Context) (s : Setting Bool Bool) :
    observe (forward.response u s) =
      ((s false).getD u.1, (s true).getD (((s false).getD u.1).xor (disturbance u))) := by
  simp [observe, forward, binary_root, binary_child]

private theorem reverse_response (u : Context) (s : Setting Bool Bool) :
    observe (reverse.response u s) =
      ((s false).getD (((s true).getD u.1).xor (disturbance u)), (s true).getD u.1) := by
  simp [observe, reverse, binary_root, binary_child]

private theorem confounded_response (u : Context) (s : Setting Bool Bool) :
    observe (confounded.response u s) =
      ((s false).getD u.1, (s true).getD (u.1.xor (disturbance u))) := by
  change ((confounded.intervene s).solve u false, (confounded.intervene s).solve u true) = _
  rw [(confounded.intervene s).solve_equation u false,
    (confounded.intervene s).solve_equation u true]
  rfl

noncomputable def observational (m : Model Bool Context Bool) : PMF (Bool × Bool) :=
  m.responseLaw contextLaw (fun _ => none) observe

/-- Full joint law, including both off-diagonal observations. -/
theorem forward_observational (x y : Bool) :
    observational forward (x, y) = if x = y then fraction 3 8 else fraction 1 8 := by
  classical
  cases x <;> cases y <;>
    simp only [observational, Model.responseLaw, PMF.map_apply, forward_response, disturbance,
      contextLaw, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
      PMF.ofFintype_apply] <;> simp
  all_goals
    simp only [fraction, ← ENNReal.coe_add, ENNReal.coe_inj]
    norm_num

theorem same_observational :
    observational forward = observational reverse ∧
    observational forward = observational confounded := by
  classical
  constructor
  · ext ⟨x, y⟩
    rw [forward_observational]
    cases x <;> cases y <;>
      simp only [observational, Model.responseLaw, PMF.map_apply, reverse_response, disturbance,
        contextLaw, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
        PMF.ofFintype_apply] <;> simp
    all_goals
      simp only [fraction, ← ENNReal.coe_add, ENNReal.coe_inj]
      norm_num
  · apply PMF.ext
    intro xy
    simp only [observational, Model.responseLaw, PMF.map_apply, forward_response,
      confounded_response, Option.getD_none]

noncomputable def outcomeUnderSetX (m : Model Bool Context Bool) : PMF Bool :=
  m.responseLaw contextLaw (setOne false true) (fun values => (observe values).2)

theorem intervention_masses :
    outcomeUnderSetX forward true = fraction 3 4 ∧
      outcomeUnderSetX reverse true = fraction 1 2 ∧
      outcomeUnderSetX confounded true = fraction 1 2 := by
  classical
  simp only [outcomeUnderSetX, Model.responseLaw, PMF.map_apply, forward_response, reverse_response,
    confounded_response, setOne, disturbance, contextLaw, tsum_fintype, Fintype.sum_prod_type,
    Fintype.sum_bool, Fin.sum_univ_succ, PMF.ofFintype_apply]
  simp
  simp only [fraction, ← ENNReal.coe_add, ENNReal.coe_inj]
  norm_num

/-- Event-mass ratio for X = true. It gives the conditional probability when
X = true has positive mass. -/
noncomputable def observedYGivenX (m : Model Bool Context Bool) : ℝ≥0∞ :=
  let law := observational m
  law (true, true) / (law (true, false) + law (true, true))

theorem observed_forward_mass : observedYGivenX forward = fraction 3 4 := by
  rw [observedYGivenX, forward_observational, forward_observational]
  simp only [Bool.true_eq_false, ite_false, ite_true, fraction, Nat.cast_ofNat, Nat.cast_one]
  rw [← ENNReal.coe_add, ← ENNReal.coe_div (by norm_num : (1 / 8 + 3 / 8 : ℝ≥0) ≠ 0)]
  rw [ENNReal.coe_inj]
  norm_num

theorem conditioning_disagrees_with_intervention :
    observedYGivenX confounded = fraction 3 4 ∧
      outcomeUnderSetX confounded true ≠ observedYGivenX confounded := by
  have observed : observedYGivenX confounded = fraction 3 4 := by
    simpa only [observedYGivenX, ← same_observational.2] using observed_forward_mass
  refine ⟨observed, ?_⟩
  rw [observed, intervention_masses.2.2]
  simp only [fraction, Nat.cast_ofNat, Nat.cast_one, ne_eq, ENNReal.coe_inj]
  norm_num

/-- The full observational law cannot recover this surgical mass on a class
that includes both the forward and reverse mechanisms. -/
theorem no_observational_identification :
    ¬ ∃ recover : PMF (Bool × Bool) → ℝ≥0∞, ∀ m : Model Bool Context Bool,
      recover (observational m) = outcomeUnderSetX m true := by
  rintro ⟨recover, h⟩
  have eq := (h forward).symm.trans ((congrArg recover same_observational.1).trans (h reverse))
  rw [intervention_masses.1, intervention_masses.2.1] at eq
  simp only [fraction, Nat.cast_ofNat, Nat.cast_one, ENNReal.coe_inj] at eq
  norm_num at eq

end Identification
end TruthCore.Causality.StructuralCausalModel
