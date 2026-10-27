/- Exact derivatives and minimum curvature for the constructed area formulas. -/
module

public import Plank.Proofs.Quant.PlanarPolygonCharts
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.QuadraticChartCalculus

open Set PlanarPolygonCharts
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full derivative of a finite sum of affine products. -/
def derivative (q : QuadraticFormula E) (x : E) : E →L[ℝ] ℝ :=
  ∑ k ∈ Finset.range q.size,
    (q.right k x • (q.left k).linear.toContinuousLinearMap +
      q.left k x • (q.right k).linear.toContinuousLinearMap)

/-- The fixed Hessian, viewed as a linear map into the continuous dual. -/
def hessian (q : QuadraticFormula E) : E →ₗ[ℝ] (E →L[ℝ] ℝ) :=
  ∑ k ∈ Finset.range q.size,
    ((q.right k).linear.smulRight (q.left k).linear.toContinuousLinearMap +
      (q.left k).linear.smulRight (q.right k).linear.toContinuousLinearMap)

theorem derivative_apply (q : QuadraticFormula E) (x z : E) :
    derivative q x z = ∑ k ∈ Finset.range q.size,
      (q.right k x*(q.left k).linear z+q.left k x*(q.right k).linear z) := by
  simp [derivative]

theorem hessian_apply (q : QuadraticFormula E) (z w : E) :
    hessian q z w = ∑ k ∈ Finset.range q.size,
      ((q.right k).linear z*(q.left k).linear w+
        (q.left k).linear z*(q.right k).linear w) := by
  simp [hessian]

theorem hessian_symm (q : QuadraticFormula E) (z w : E) :
    hessian q z w = hessian q w z := by
  rw [hessian_apply, hessian_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hasFDerivAt_affine (f : E →ᵃ[ℝ] ℝ) (x : E) :
    HasFDerivAt f f.linear.toContinuousLinearMap x := by
  rw [f.decomp]
  simpa only [add_zero, LinearMap.coe_toContinuousLinearMap'] using
    f.linear.toContinuousLinearMap.hasFDerivAt.add (hasFDerivAt_const (f 0) x)

theorem hasFDerivAt_eval (q : QuadraticFormula E) (x : E) :
    HasFDerivAt q.eval (derivative q x) x := by
  unfold QuadraticFormula.eval derivative
  apply HasFDerivAt.fun_sum
  intro k _
  convert! (hasFDerivAt_affine (q.left k) x).mul
    (hasFDerivAt_affine (q.right k) x) using 1
  exact add_comm _ _

theorem derivative_add (q : QuadraticFormula E) (x z : E) :
    derivative q (x+z) = derivative q x+hessian q z := by
  ext w
  simp only [add_apply, derivative_apply, hessian_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hl := affine_eval_line (q.left k) x z 1
  have hr := affine_eval_line (q.right k) x z 1
  simp only [one_smul, one_mul] at hl hr
  rw [hl, hr]
  ring

/-- The derivative is an actual affine map; its linear part is the Hessian. -/
def gradient (q : QuadraticFormula E) : E →ᵃ[ℝ] (E →L[ℝ] ℝ) where
  toFun := derivative q
  linear := hessian q
  map_vadd' x z := by
    simpa only [vadd_eq_add, add_comm] using derivative_add q x z

@[simp] theorem gradient_apply (q : QuadraticFormula E) (x : E) :
    gradient q x = derivative q x := rfl

theorem continuous_derivative (q : QuadraticFormula E) : Continuous (derivative q) :=
  (gradient q).continuous_of_finiteDimensional

/-- The exact Taylor expansion has no remainder. -/
theorem eval_add (q : QuadraticFormula E) (x z : E) :
    q.eval (x+z) = q.eval x+derivative q x z+hessian q z z/2 := by
  simp only [QuadraticFormula.eval, derivative_apply, hessian_apply,
    Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hl := affine_eval_line (q.left k) x z 1
  have hr := affine_eval_line (q.right k) x z 1
  simp only [one_smul, one_mul] at hl hr
  rw [hl, hr]
  ring

theorem eval_line (q : QuadraticFormula E) (x z : E) (t : ℝ) :
    q.eval (x+t • z) = q.eval x+t*derivative q x z+t^2*hessian q z z/2 := by
  rw [eval_add]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Adding a scaling coordinate turns a globally positive quadratic with
positive-definite Hessian into a positive-definite homogeneous quadratic.
The evaluation outside the chart concerns only the polynomial. -/
theorem positive_homogenization (q : QuadraticFormula E) (x : E)
    (hvalue : ∀ y, 0 < q.eval y)
    (hcurv : ∀ z, z ≠ 0 → 0 < hessian q z z)
    (w : E × ℝ) (hw : w ≠ 0) :
    0 < hessian q w.1 w.1 + 2*w.2*derivative q x w.1 + 2*q.eval x*w.2^2 := by
  by_cases ht : w.2 = 0
  · have hz : w.1 ≠ 0 := fun hz => hw (Prod.ext hz ht)
    simpa only [ht, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero]
      using hcurv w.1 hz
  · have he : hessian q w.1 w.1 + 2*w.2*derivative q x w.1 + 2*q.eval x*w.2^2 =
        2*w.2^2*q.eval (x+w.2⁻¹ • w.1) := by
      rw [eval_line]
      field_simp
      ring
    rw [he]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ht)) (hvalue _)

/-- Exact extrapolation replaces a limiting argument: an area direction
with curvature at most half the value reaches a nonpositive polynomial value.
The extrapolated point need not belong to the geometric chart. -/
theorem eval_nonpos_of_area_direction (q : QuadraticFormula E) (x z : E)
    (hder : derivative q x z = q.eval x)
    (hcurv : hessian q z z ≤ q.eval x/2) :
    q.eval (x+(-2 : ℝ) • z) ≤ 0 := by
  rw [eval_line, hder]
  linarith only [hcurv]

/-- A stationary quadratic with positive-definite Hessian is strictly
larger away from its stationary point, on the whole parameter space. -/
theorem eval_lt_of_stationary (q : QuadraticFormula E) (x : E)
    (hstat : derivative q x = 0)
    (hpos : ∀ z : E, z ≠ 0 → 0 < hessian q z z)
    {y : E} (hy : y ≠ x) : q.eval x < q.eval y := by
  have he := eval_add q x (y-x)
  rw [add_sub_cancel, hstat, zero_apply, add_zero] at he
  have hp := hpos (y-x) (sub_ne_zero.mpr hy)
  linarith only [he, hp]

/-- A linear perturbation changes the first derivative but not the Hessian. -/
def tilt (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x : E) : ℝ := q.eval x-v x

theorem hasFDerivAt_tilt (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (tilt q v) (derivative q x-v) x :=
  (hasFDerivAt_eval q x).sub v.hasFDerivAt

theorem stationary_of_localMin (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x : E)
    (hmin : IsLocalMin (tilt q v) x) : derivative q x = v :=
  sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hasFDerivAt_tilt q v x))

theorem tilt_add (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x z : E) :
    tilt q v (x+z) = tilt q v x+(derivative q x-v) z+hessian q z z/2 := by
  simp only [tilt, eval_add, map_add, sub_apply]
  ring

/-- The exact expansion gives nonnegative curvature at any local minimum. -/
theorem hessian_nonneg_of_localMin (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x : E)
    (hmin : IsLocalMin (tilt q v) x) (z : E) : 0 ≤ hessian q z z := by
  have hs := stationary_of_localMin q v x hmin
  have hc : Continuous (fun t : ℝ => x+t • z) := continuous_const.add (continuous_id.smul continuous_const)
  have hevent : ∀ᶠ t : ℝ in nhds 0, tilt q v x ≤ tilt q v (x+t • z) := by
    have htend : Filter.Tendsto (fun t : ℝ => x+t • z) (nhds 0) (nhds x) := by
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    exact htend.eventually hmin
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have ht : 0 < ε/2 := by linarith
  have hh := hball (show ε/2 ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
    linarith)
  change tilt q v x ≤ tilt q v (x+(ε/2) • z) at hh
  rw [tilt_add, hs, sub_self, zero_apply, add_zero] at hh
  simp only [map_smul, smul_apply, smul_eq_mul] at hh
  have hm : 0 ≤ (ε/2)^2*hessian q z z := by nlinarith only [hh]
  exact nonneg_of_mul_nonneg_right hm (sq_pos_of_pos ht)

/-- Every local minimum of a quadratic is a global minimum. -/
theorem global_of_localMin (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x : E)
    (hmin : IsLocalMin (tilt q v) x) (y : E) : tilt q v x ≤ tilt q v y := by
  have hs := stationary_of_localMin q v x hmin
  have h := tilt_add q v x (y-x)
  rw [add_sub_cancel, hs, sub_self, zero_apply, add_zero] at h
  have hn := hessian_nonneg_of_localMin q v x hmin (y-x)
  linarith only [h, hn]

/-- At a local minimum, injectivity of the fixed Hessian improves
nonnegative curvature to strictly positive curvature in every nonzero
direction. This uses exact quadratic expansion and first derivatives. -/
theorem hessian_pos_of_localMin (q : QuadraticFormula E) (v : E →L[ℝ] ℝ) (x : E)
    (hmin : IsLocalMin (tilt q v) x) (hinj : Function.Injective (hessian q)) :
    ∀ z : E, z ≠ 0 → 0 < hessian q z z := by
  intro z hz
  have hs := stationary_of_localMin q v x hmin
  apply lt_of_le_of_ne (hessian_nonneg_of_localMin q v x hmin z)
  intro hzero
  have heq : tilt q v (x+z) = tilt q v x := by
    rw [tilt_add, hs, sub_self, zero_apply, add_zero, ← hzero, zero_div, add_zero]
  have hminz : IsLocalMin (tilt q v) (x+z) :=
    Filter.Eventually.of_forall (fun y => heq.trans_le (global_of_localMin q v x hmin y))
  have hs' := stationary_of_localMin q v (x+z) hminz
  have hH : hessian q z = 0 := by
    have h := derivative_add q x z
    rw [hs, hs'] at h
    exact (add_eq_left.mp h.symm)
  exact hz (hinj (hH.trans (map_zero (hessian q)).symm))

end Plank.QuadraticChartCalculus
