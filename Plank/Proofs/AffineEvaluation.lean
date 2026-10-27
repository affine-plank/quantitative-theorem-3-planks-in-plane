/- Affine evaluation on segments and barycentric combinations.
These algebraic identities do not use topology or widths. -/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open Set Finset
namespace Plank.Body
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An affine map is affine along the segment `x + t·(y − x)`. -/
theorem map_add_smul_sub (f : E →ᵃ[ℝ] ℝ) (x y : E) (t : ℝ) :
    f (x + t • (y - x)) = f x + t * (f y - f x) := by
  have := f.apply_lineMap x y t
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_ring', add_comm] at this
  linarith

/-- An affine map of a barycentric combination is the combination of
the values. -/
theorem map_comb (f : E →ᵃ[ℝ] ℝ) (l : Fin 3 → ℝ) (v : Fin 3 → E) (hl : ∑ i, l i = 1) :
    f (∑ i, l i • v i) = ∑ i, l i * f (v i) := by
  rw [AffineMap.decomp]
  simp only [Pi.add_apply, Fin.sum_univ_three, map_add, map_smul, smul_eq_mul] at *
  linear_combination -(f 0) * hl

/-- A barycentric combination is bounded by the largest vertex value. -/
theorem map_comb_le (f : E →ᵃ[ℝ] ℝ) {l : Fin 3 → ℝ} {v : Fin 3 → E} (h0 : ∀ i, 0 ≤ l i)
    (hl : ∑ i, l i = 1) {a : Fin 3} (ha : ∀ i, f (v i) ≤ f (v a)) :
    f (∑ i, l i • v i) ≤ f (v a) := by
  rw [map_comb f l v hl]
  calc ∑ i, l i * f (v i) ≤ ∑ i, l i * f (v a) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (h0 i)
    _ = f (v a) := by rw [← sum_mul, hl, one_mul]

end Plank.Body

/-- info: 'Plank.Body.map_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Body.map_comb
