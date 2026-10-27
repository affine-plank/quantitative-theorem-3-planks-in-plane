/- Product bounds for the all-singleton transfer obstruction.
A deficit forces a large separation of the upper and lower slope products. -/
module
public import Plank.Convex.SameSignCapTransfer
public import Plank.Convex.CyclicWidthBudgets
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.SameSignCapProduct
open scoped BigOperators
open SameSignCapAlgebra SameSignCapTransfer

def budget (w f r : Point) (i : Fin 3) : ℝ :=
  w i + f i * w (next i) + r i * w (prev i)

/-- The cyclic product expression is the three-index instance of the finite
product comparison. Its nonnegativity forces the width bound. -/
theorem width_bound_of_budget_nonneg (w f r : Point) (hw : ∀ i, 0 ≤ w i)
    (hbudget : ∀ i, 1 ≤ budget w f r i)
    (hN : 0 ≤ (∑ i, w i * budget w f r (next i) * budget w f r (prev i)) -
      (∏ i, budget w f r i)) : 1 ≤ ∑ i, w i := by
  apply WidthBudgets.width_bound_of_product_comparison w (budget w f r) hw hbudget
  have he (i : Fin 3) : Finset.univ.erase i = {next i, prev i} := by
    fin_cases i <;> decide
  have hn (i : Fin 3) : next i ≠ prev i := by
    fin_cases i <;> decide
  convert sub_nonneg.mp hN using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [he i, Finset.prod_pair (hn i)]
  ring

/-- A polynomial identity for three coordinate budgets. Opposite pairs
and the sum of the two cycle products determine the signs of all terms. -/
theorem budget_identity (w f r : Point) :
    (∑ i, w i * budget w f r (next i) * budget w f r (prev i)) -
      (∏ i, budget w f r i) =
    (∑ i, (1 - f i * r (next i)) *
      (f (prev i) * (w i) ^ 2 * w (next i) +
        r (prev i) * w i * (w (next i)) ^ 2)) +
      (2 - (∏ i, f i) - (∏ i, r i)) * (∏ i, w i) := by
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, budget, next, prev,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Pair contraction and a bound on the sum of the two directed cycle
products suffice for the width bound. -/
theorem width_bound_of_cycle_products (w f r : Point)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (next i) ≤ 1)
    (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ budget w f r i) : 1 ≤ ∑ i, w i := by
  let σ : Fin 3 ≃ Fin 3 :=
    ⟨next, prev, prev_next, next_prev⟩
  have hreach : ∀ i j, ∃ n : ℕ, (σ : Fin 3 → Fin 3)^[n] i = j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩
  exact CyclicWidthBudgets.width_bound σ w f r hreach hw hf hr hpair hcycle
    (fun i => (SameSignCapAlgebra.sum_cycle w i).symm.le) hbudget

def cycleGap (a b : Point) : ℝ :=
  2 * (slopeProduct a b + 1) + mixedSum a b + mixedSum b a -
    (∏ i, a i) - (∏ i, b i)

/-- The sum of the two transfer products has a square factor and a short
remaining expression in the separate separator products and mixed sums. -/
theorem cycle_product_gap (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    2 - (∏ i, forward a b i) - (∏ i, reverse a b i) =
      (slopeProduct a b - 1) ^ 2 * cycleGap a b / denProduct a b := by
  calc
    _ = (1 - (∏ i, forward a b i)) + (1 - (∏ i, reverse a b i)) := by ring
    _ = _ := by
      rw [forward_product_gap a b ha hb, reverse_product_gap a b ha hb]
      dsimp [cycleGap]
      ring

/-- The nonnegative cycle-gap region satisfies the width bound using
only the opposite-contact rows, in any ambient geometry. -/
theorem width_bound_of_cycle_gap (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hgap : 0 ≤ cycleGap a b) : 1 ≤ ∑ i, (hi i - lo i) := by
  apply width_bound_of_cycle_products (fun i => hi i - lo i) (forward a b) (reverse a b)
    (fun i => sub_nonneg.mpr (horder i))
  · intro i
    exact add_nonneg
      (div_nonneg (hb i).le (lowerDen_pos a b ha hb i).le)
      (div_nonneg (ha i).le (upperDen_pos a b ha hb i).le)
  · intro i
    exact add_nonneg
      (div_nonneg (mul_nonneg (hb i).le (ha (next i)).le) (lowerDen_pos a b ha hb i).le)
      (div_nonneg (mul_nonneg (ha i).le (hb (next i)).le) (upperDen_pos a b ha hb i).le)
  · exact pair_le_one a b ha hb
  · have hnonneg : 0 ≤ 2 - (∏ i, forward a b i) - (∏ i, reverse a b i) := by
      rw [cycle_product_gap a b ha hb]
      exact div_nonneg (mul_nonneg (sq_nonneg _) hgap) (denProduct_pos a b ha hb).le
    linarith only [hnonneg]
  · exact transfer_bound lo hi a b ha hb hrows

theorem mixedSum_nonneg (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    0 ≤ mixedSum a b := Finset.sum_nonneg fun i _ =>
  mul_nonneg (mul_nonneg (ha i).le (hb (next i)).le) (ha (prev i)).le

/-- In particular, the upper and lower separator products may both be
at most one, or both at least one. Either situation rules out a deficit. -/
theorem width_bound_of_same_product_side (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hside : 0 ≤ ((∏ i, a i) - 1) * ((∏ i, b i) - 1)) :
    1 ≤ ∑ i, (hi i - lo i) := by
  apply width_bound_of_cycle_gap lo hi a b ha hb hrows horder
  have hP : 0 < slopeProduct a b :=
    mul_pos (Finset.prod_pos fun i _ => ha i) (Finset.prod_pos fun i _ => hb i)
  have hs := mixedSum_nonneg a b ha hb
  have ht := mixedSum_nonneg b a hb ha
  dsimp [cycleGap, slopeProduct] at *
  nlinarith only [hside, hP, hs, ht]

/-- A deficit requires the two separator products to dominate all of
the positive terms in the cycle gap. -/
theorem product_imbalance_of_deficit (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1) :
    2 * (slopeProduct a b + 1) + mixedSum a b + mixedSum b a <
      (∏ i, a i) + (∏ i, b i) := by
  have hg : cycleGap a b < 0 := by
    by_contra hn
    exact (not_le_of_gt hdef)
      (width_bound_of_cycle_gap lo hi a b ha hb hrows horder (le_of_not_gt hn))
  dsimp [cycleGap] at hg
  linarith only [hg]

private theorem separated_products (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgap : 2 * (A * B + 1) < A + B) :
    (2 < A ∧ 2 * B < 1) ∨ (2 < B ∧ 2 * A < 1) := by
  have hsmall (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hx1 : x ≤ 1)
      (hh : 2 * (x * y + 1) < x + y) : 2 < y ∧ 2 * x < 1 := by
    have hy1 : 1 < y := by
      by_contra hn
      have hm := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (le_of_not_gt hn))
      nlinarith only [hh, hm, mul_pos hx hy]
    have hxy := mul_nonneg hx.le (show 0 ≤ 2 * y - 1 by linarith only [hy1])
    refine ⟨by nlinarith only [hh, hxy], ?_⟩
    by_contra hn
    have hm := mul_nonneg (show 0 ≤ 2 * x - 1 by linarith only [le_of_not_gt hn]) hy.le
    nlinarith only [hh, hm, hx1]
  by_cases hA1 : A ≤ 1
  · exact Or.inr (hsmall A B hA hB hA1 hgap)
  · have hB1 : B ≤ 1 := by
      by_contra hn
      have hm := mul_nonneg (show 0 ≤ A - 1 by linarith only [lt_of_not_ge hA1])
        (show 0 ≤ B - 1 by linarith only [lt_of_not_ge hn])
      nlinarith only [hgap, hm, mul_pos hA hB]
    exact Or.inl (hsmall B A hB hA hB1 (by nlinarith only [hgap]))

/-- A deficit needs considerably more than products on opposite sides
of one: one is above two, and the other is below one half. -/
theorem products_far_apart_of_deficit (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1) :
    (2 < (∏ i, a i) ∧ 2 * (∏ i, b i) < 1) ∨
      (2 < (∏ i, b i) ∧ 2 * (∏ i, a i) < 1) := by
  have hg := product_imbalance_of_deficit lo hi a b ha hb hrows horder hdef
  have hs := mixedSum_nonneg a b ha hb
  have ht := mixedSum_nonneg b a hb ha
  exact separated_products _ _ (Finset.prod_pos fun i _ => ha i)
    (Finset.prod_pos fun i _ => hb i) (by dsimp [slopeProduct] at hg; linarith only [hg, hs, ht])

end Plank.Convex.SameSignCapProduct

/-- info: 'Plank.Convex.SameSignCapProduct.width_bound_of_budget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.width_bound_of_budget_nonneg

/-- info: 'Plank.Convex.SameSignCapProduct.budget_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.budget_identity

/-- info: 'Plank.Convex.SameSignCapProduct.width_bound_of_cycle_products' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.width_bound_of_cycle_products

/-- info: 'Plank.Convex.SameSignCapProduct.cycle_product_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.cycle_product_gap

/-- info: 'Plank.Convex.SameSignCapProduct.width_bound_of_cycle_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.width_bound_of_cycle_gap

/-- info: 'Plank.Convex.SameSignCapProduct.width_bound_of_same_product_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.width_bound_of_same_product_side

/-- info: 'Plank.Convex.SameSignCapProduct.product_imbalance_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.product_imbalance_of_deficit

/-- info: 'Plank.Convex.SameSignCapProduct.products_far_apart_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapProduct.products_far_apart_of_deficit
