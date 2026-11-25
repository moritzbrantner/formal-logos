module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Euclidean and round-sphere right triangles for the possibility argument in #1790. -/

@[expose] public section

namespace TruthCore.German.Kant.TrianglePossibility

/-- The endpoint distance is forced by the lengths and orthogonality. -/
theorem thirdSide {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 3) (hv : ‖v‖ = 4) (hright : inner ℝ u v = 0) :
    dist u v = 5 := by
  rw [dist_eq_norm]
  have h := norm_sub_sq_eq_norm_sq_add_norm_sq_real hright
  rw [hu, hv] at h
  nlinarith [norm_nonneg (u - v)]

/-- All coordinates are in fifths of the common unit. -/
def dot (u v : ℤ × ℤ) : ℤ := u.1 * v.1 + u.2 * v.2

theorem coordinateWitness :
    let u : ℤ × ℤ := (9, 12)
    let v : ℤ × ℤ := (-16, 12)
    dot u u = 225 ∧ dot v v = 400 ∧ dot u v = 0 ∧ dot (v-u) (v-u) = 625 := by
  decide

theorem incompatibleSix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 3) (hv : ‖v‖ = 4) (hright : inner ℝ u v = 0) :
    dist u v ≠ 6 := by
  rw [thirdSide u v hu hv hright]
  norm_num

/-- Euclidean dot product of three real coordinates. -/
def rayDot (u v : ℝ × ℝ × ℝ) : ℝ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- Points on the round sphere are specified by unit radial directions. -/
abbrev UnitRay := {u : ℝ × ℝ × ℝ // rayDot u u = 1}

noncomputable def xMeridian (θ : ℝ) : UnitRay :=
  ⟨(Real.sin θ, 0, Real.cos θ), by
    simpa [rayDot, sq] using Real.sin_sq_add_cos_sq θ⟩

noncomputable def yMeridian (θ : ℝ) : UnitRay :=
  ⟨(0, Real.sin θ, Real.cos θ), by
    simpa [rayDot, sq] using Real.sin_sq_add_cos_sq θ⟩

/-- Shorter great-circle arc length for the stipulated round metric. -/
noncomputable def minorArc (radius : ℝ) (u v : UnitRay) : ℝ := radius * Real.arccos (rayDot u.val v.val)

/-- Both meridians start at the north pole with nonzero perpendicular tangents. -/
theorem meridiansAtPole :
    xMeridian 0 = yMeridian 0 ∧
    deriv (fun t => (xMeridian t).val) 0 = (1, 0, 0) ∧
    deriv (fun t => (yMeridian t).val) 0 = (0, 1, 0) ∧
    rayDot (1, 0, 0) (0, 1, 0) = 0 := by
  have hs := Real.hasDerivAt_sin (0 : ℝ)
  have hc := Real.hasDerivAt_cos (0 : ℝ)
  have hz := hasDerivAt_const (0 : ℝ) (0 : ℝ)
  refine ⟨Subtype.ext (by simp [xMeridian, yMeridian]), ?_, ?_, by norm_num [rayDot]⟩
  · simpa [xMeridian] using (hs.prodMk (hz.prodMk hc)).deriv
  · simpa [yMeridian] using (hz.prodMk (hs.prodMk hc)).deriv

/-- At radius 6/π the two meridians give legs 3 and 4, with a third arc of length 3. -/
theorem sphericalControl :
    let radius := 6 / Real.pi
    let pole := xMeridian 0
    let a := xMeridian (Real.pi / 2)
    let b := yMeridian (2 * Real.pi / 3)
    minorArc radius pole a = 3 ∧ minorArc radius pole b = 4 ∧ minorArc radius a b = 3 := by
  dsimp only
  have hcos : Real.arccos (Real.cos (2 * Real.pi / 3)) = 2 * Real.pi / 3 :=
    Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simp only [minorArc, xMeridian, yMeridian, rayDot, Real.sin_zero, Real.cos_zero,
    Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, zero_mul, one_mul, add_zero, zero_add,
    Real.arccos_zero, hcos]
  constructor
  · field_simp [Real.pi_ne_zero]
    norm_num
  constructor <;> field_simp [Real.pi_ne_zero] <;> ring

end TruthCore.German.Kant.TrianglePossibility
