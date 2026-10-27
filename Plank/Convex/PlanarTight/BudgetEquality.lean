/- Equality in positive finite width budgets. -/
module
public import Plank.Convex.WidthBudgets
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.BudgetEquality

/-- At total weight one, coefficients bounded by their common weighted
average are all equal to that average. No sign assumption on the
coefficients or the average is required. -/
theorem coefficients_eq {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hbudget : ∀ i, a i ≤ ∑ j, a j * w j) :
    ∀ i, a i = ∑ j, a j * w j := by
  let B := ∑ j, a j * w j
  have hz : (∑ i, (B - a i) * w i) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
    exact sub_self B
  have hnonneg (i : ι) : 0 ≤ (B - a i) * w i :=
    mul_nonneg (sub_nonneg.mpr (hbudget i)) (hw i).le
  have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hz
  intro i
  have hi := (mul_eq_zero.mp (he i (Finset.mem_univ i))).resolve_right (hw i).ne'
  exact (sub_eq_zero.mp hi).symm

/-- Every coefficient of a saturated bounded row with positive weights is one. -/
theorem bounded_row_eq_one {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, a i ≤ 1) (hbudget : 1 ≤ ∑ i, a i * w i) : ∀ i, a i = 1 := by
  have hupper : (∑ i, a i * w i) ≤ 1 := by
    calc
      (∑ i, a i * w i) ≤ ∑ i, w i := Finset.sum_le_sum fun i _ => by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i) (hw i).le
      _ = 1 := hsum
  have he := coefficients_eq w a hw hsum (fun i => (ha i).trans hbudget)
  intro i
  exact (he i).trans (le_antisymm hupper hbudget)

/-- Equality in a positive weighted sum of two inequalities saturates both. -/
theorem split_eq (a b L R S T : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hL : L ≤ R) (hS : S ≤ T) (hsum : a * L + b * S = a * R + b * T) :
    L = R ∧ S = T := by
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr hL)
  have h2 := mul_nonneg hb.le (sub_nonneg.mpr hS)
  constructor <;> nlinarith only [hsum, h1, h2, ha, hb]

end Plank.Convex.PlanarTight.BudgetEquality

/-- info: 'Plank.Convex.PlanarTight.BudgetEquality.coefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BudgetEquality.coefficients_eq

/-- info: 'Plank.Convex.PlanarTight.BudgetEquality.bounded_row_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.BudgetEquality.bounded_row_eq_one
