/- A three-variable box inequality, proved by checking affine endpoint values. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace Plank.Convex.CyclicBox
abbrev Triple := Fin 3 → ℝ

/-- An affine function nonnegative at the interval endpoints is nonnegative inside. -/
private theorem affine_nonneg {x M c k : ℝ} (hx : 0 ≤ x) (hM : x ≤ M)
    (h0 : 0 ≤ c) (h1 : 0 ≤ c + k*M) : 0 ≤ c + k*x := by
  rcases le_total 0 k with hk | hk
  · exact add_nonneg h0 (mul_nonneg hk hx)
  · have h := mul_le_mul_of_nonpos_left hM hk
    linarith only [h1,h]

/-- A separately affine expression is checked on the box vertices. At a vertex
with a zero coordinate its negative product vanishes; at the remaining vertex
the whole expression vanishes. -/
theorem cyclic_product_le (u v : Triple) (hv : ∀ i, 0 ≤ v i)
    (hu : ∀ i, 0 ≤ u i) (hbound : ∀ i, u i ≤ 1+v i) :
    (∏ i, u i) ≤ 1 + (∏ i, v i) + (∑ i, u i * v (i+2)) := by
  have v0 := hv 0; have v1 := hv 1; have v2 := hv 2
  have u1 := hu 1; have u2 := hu 2
  have h2 := affine_nonneg (hu 2) (hbound 2)
    (c := 1+v 0*v 1*v 2+(1+v 0)*v 2+(1+v 1)*v 0)
    (k := v 1-(1+v 0)*(1+v 1)) (by positivity) (by ring_nf; rfl)
  have h1 := affine_nonneg (hu 1) (hbound 1)
    (c := 1+v 0*v 1*v 2+(1+v 0)*v 2+u 2*v 1)
    (k := v 0-(1+v 0)*u 2) (by positivity) (by nlinarith only [h2])
  have h0 := affine_nonneg (hu 0) (hbound 0)
    (c := 1+v 0*v 1*v 2+u 1*v 0+u 2*v 1)
    (k := v 2-u 1*u 2) (by positivity) (by nlinarith only [h1])
  simp [Fin.sum_univ_three, Fin.prod_univ_three]
  nlinarith only [h0]

end Plank.Convex.CyclicBox
