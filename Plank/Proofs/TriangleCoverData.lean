/- Normalized affine windows on barycentric coordinates of a triangle. -/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Real.Basic
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.TriangleNormalization
open scoped BigOperators

/-- Each row records the values of one affine function at the three vertices.
Its minimum and maximum are normalized to `0` and `1`; its window is `[lo, hi]`.
Coverage is stated on all nonnegative barycentric coordinates of sum one. -/
structure Cover (n : ℕ) where
  g : Fin n → Fin 3 → ℝ
  σ : Fin n → Equiv.Perm (Fin 3)
  lo : Fin n → ℝ
  hi : Fin n → ℝ
  bounds : ∀ i j, 0 ≤ g i j ∧ g i j ≤ 1
  zero : ∀ i, g i (σ i 0) = 0
  one : ∀ i, g i (σ i 2) = 1
  ordered : ∀ i, lo i ≤ hi i
  covered : ∀ l : Fin 3 → ℝ, (∀ j, 0 ≤ l j) → ∑ j, l j = 1 →
    ∃ i, lo i ≤ ∑ j, l j * g i j ∧ (∑ j, l j * g i j) ≤ hi i

/-- In normalized coordinates, each relative width is simply `hi - lo`. -/
def Cover.width {n : ℕ} (C : Cover n) : ℝ := ∑ i, (C.hi i - C.lo i)

end Plank.TriangleNormalization
