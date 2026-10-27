/- Equality in the product comparison for positive width budgets. -/
module
public import Plank.Convex.PlanarTight.BudgetEquality
public import Plank.Convex.SameSignCapProduct
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.ProductBudgetEquality

/-- Positive weights of total one saturate every factor in a product
comparison. This statement has an arbitrary finite index set. -/
theorem factors_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w d : ι → ℝ) (hw : ∀ i, 0 < w i) (hd : ∀ i, 1 ≤ d i)
    (hsum : ∑ i, w i = 1)
    (hcomp : (∏ i, d i) ≤ ∑ i, w i * ∏ j ∈ Finset.univ.erase i, d j) :
    ∀ i, d i = 1 := by
  let a : ι → ℝ := fun i => ∏ j ∈ Finset.univ.erase i, d j
  let P := ∏ i, d i
  have ha (i : ι) : a i ≤ P :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset i Finset.univ)
      (fun j _ => zero_le_one.trans (hd j)) (fun j _ _ => hd j)
  have hcomp' : P ≤ ∑ i, a i * w i := by
    simpa only [a, P, mul_comm] using hcomp
  have hupper : (∑ i, a i * w i) ≤ P := by
    calc
      (∑ i, a i * w i) ≤ ∑ i, P * w i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (hw i).le
      _ = P := by rw [← Finset.mul_sum, hsum, mul_one]
  have he := BudgetEquality.coefficients_eq w a hw hsum (fun i => (ha i).trans hcomp')
  intro i
  have hi : a i = P := (he i).trans (le_antisymm hupper hcomp')
  have hap : 0 < a i := Finset.prod_pos fun j _ => zero_lt_one.trans_le (hd j)
  have hprod : d i * a i = P := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)
  nlinarith only [hi, hap, hprod]

open SameSignCapAlgebra SameSignCapProduct

/-- At positive-width equality, all three contracting cycle budgets are
exactly one. An individual strict budget therefore excludes equality. -/
theorem budgets_eq_one (w f r : Point)
    (hw : ∀ i, 0 < w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (next i) ≤ 1)
    (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ budget w f r i) (hsum : ∑ i, w i = 1) :
    ∀ i, budget w f r i = 1 := by
  have hN : 0 ≤ (∑ i, w i * budget w f r (next i) * budget w f r (prev i)) -
      (∏ i, budget w f r i) := by
    rw [budget_identity]
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (sub_nonneg.mpr (hpair i))
      exact add_nonneg
        (mul_nonneg (mul_nonneg (hf (prev i)) (sq_nonneg _)) (hw (next i)).le)
        (mul_nonneg (mul_nonneg (hr (prev i)) (hw i).le) (sq_nonneg _))
    · exact mul_nonneg (by linarith only [hcycle]) (Finset.prod_nonneg fun i _ => (hw i).le)
  apply factors_eq_one w (budget w f r) hw hbudget hsum
  have he (i : Fin 3) : Finset.univ.erase i = {next i, prev i} := by
    fin_cases i <;> decide
  have hn (i : Fin 3) : next i ≠ prev i := by
    fin_cases i <;> decide
  convert sub_nonneg.mp hN using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [he i, Finset.prod_pair (hn i)]
  ring

end Plank.Convex.PlanarTight.ProductBudgetEquality

/-- info: 'Plank.Convex.PlanarTight.ProductBudgetEquality.factors_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ProductBudgetEquality.factors_eq_one

/-- info: 'Plank.Convex.PlanarTight.ProductBudgetEquality.budgets_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ProductBudgetEquality.budgets_eq_one
