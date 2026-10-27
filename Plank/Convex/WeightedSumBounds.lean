/- A weighted sum dominating each coefficient controls the total weight. -/
module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace Plank.Convex.WeightedSumBounds

/-- If a positive weighted sum dominates every coefficient, the weights sum to at least one. -/
theorem one_le_sum {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : 0 < ∑ i, w i * a i)
    (ha : ∀ i, a i ≤ ∑ j, w j * a j) : 1 ≤ ∑ i, w i := by
  have hs : ∑ i, w i * a i ≤ ∑ i, w i * (∑ j, w j * a j) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (hw i)
  rw [← Finset.sum_mul] at hs
  exact le_of_mul_le_mul_right (by simpa only [one_mul] using hs) hp

/-- Equality forces every coefficient with positive weight to equal the weighted sum. -/
theorem coeff_eq_of_sum_one {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, a i ≤ ∑ j, w j * a j) :
    ∀ i, 0 < w i → a i = ∑ j, w j * a j := by
  let M := ∑ j, w j * a j
  have hn (i : ι) : 0 ≤ w i * (M - a i) :=
    mul_nonneg (hw i) (sub_nonneg.mpr (ha i))
  have hz : ∑ i, w i * (M - a i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, M, sub_self]
  intro i hi
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz i (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hi.ne')).symm

end Plank.Convex.WeightedSumBounds

/-- info: 'Plank.Convex.WeightedSumBounds.one_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WeightedSumBounds.one_le_sum

/-- info: 'Plank.Convex.WeightedSumBounds.coeff_eq_of_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WeightedSumBounds.coeff_eq_of_sum_one
