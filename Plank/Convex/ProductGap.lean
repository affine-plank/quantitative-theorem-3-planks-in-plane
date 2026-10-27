/- A product comparison reduces a nonnegative box to its upper corner, in any finite number of variables. -/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.ProductGap

def gap {ι : Type*} [Fintype ι] (c : ℝ) (a b : ι → ℝ) : ℝ :=
  c * ((∏ i, a i) - 1) * ((∏ i, b i) - 1) + ∏ i, (a i + b i)

/-- A quantitative comparison with the upper corner of a nonnegative box. -/
theorem mul_gap_upper_corner_le {ι : Type*} [Fintype ι]
    (c : ℝ) (a b H : ι → ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (haH : ∀ i, a i ≤ H i) (hB : (∏ i, b i) ≤ 1) :
    (∏ i, a i) * gap c H b ≤ (∏ i, H i) * gap c a b := by
  have hprod : (∏ i, a i) * (∏ i, (H i + b i)) ≤
      (∏ i, H i) * (∏ i, (a i + b i)) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro i _
      exact mul_nonneg (ha i) (add_nonneg ((ha i).trans (haH i)) (hb i))
    · intro i _
      nlinarith only [mul_le_mul_of_nonneg_right (haH i) (hb i)]
  have hAH : (∏ i, a i) ≤ ∏ i, H i :=
    Finset.prod_le_prod₀ (fun i _ => ha i) (fun i _ => haH i)
  have hm : 0 ≤ c * (1 - (∏ i, b i)) * ((∏ i, H i) - ∏ i, a i) :=
    mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hB)) (sub_nonneg.mpr hAH)
  have he : (∏ i, H i) * gap c a b =
      ((∏ i, H i) * (∏ i, (a i + b i)) - (∏ i, a i) * (∏ i, (H i + b i))) +
      c * (1 - (∏ i, b i)) * ((∏ i, H i) - ∏ i, a i) +
      (∏ i, a i) * gap c H b := by
    unfold gap
    ring
  rw [he]
  linarith only [hprod, hm]

/-- A single upper corner controls the product gap on a nonnegative box. -/
theorem nonneg_of_upper_corner {ι : Type*} [Fintype ι]
    (c : ℝ) (a b H : ι → ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hH : ∀ i, 0 < H i)
    (haH : ∀ i, a i ≤ H i) (hB : (∏ i, b i) ≤ 1)
    (hcorner : 0 ≤ gap c H b) : 0 ≤ gap c a b := by
  have hnonneg := (mul_nonneg (Finset.prod_nonneg fun i _ => ha i) hcorner).trans
    (mul_gap_upper_corner_le c a b H hc ha hb haH hB)
  exact nonneg_of_mul_nonneg_right hnonneg (Finset.prod_pos fun i _ => hH i)

/-- Strict corner positivity is preserved when the first product is positive. -/
theorem pos_of_upper_corner {ι : Type*} [Fintype ι]
    (c : ℝ) (a b H : ι → ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (haH : ∀ i, a i ≤ H i) (hB : (∏ i, b i) ≤ 1)
    (hA : 0 < ∏ i, a i) (hcorner : 0 < gap c H b) : 0 < gap c a b := by
  have hpos := (mul_pos hA hcorner).trans_le
    (mul_gap_upper_corner_le c a b H hc ha hb haH hB)
  by_contra! h
  have hle : (∏ i, H i) * gap c a b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (Finset.prod_nonneg fun i _ => (ha i).trans (haH i)) h
  exact (not_lt_of_ge hle) hpos

/-- Above product one in the first variables, the gap increases with the second. -/
theorem mono_right {ι : Type*} [Fintype ι]
    (c : ℝ) (a b B : ι → ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hA : 1 ≤ ∏ i, a i) (hbB : ∀ i, b i ≤ B i) :
    gap c a b ≤ gap c a B := by
  unfold gap
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Finset.prod_le_prod₀ (fun i _ => hb i) (fun i _ => hbB i)) 1)
      (mul_nonneg hc (sub_nonneg.mpr hA))
  · exact Finset.prod_le_prod₀ (fun i _ => add_nonneg (ha i) (hb i))
      (fun i _ => add_le_add le_rfl (hbB i))

theorem nonneg_of_products_le_one {ι : Type*} [Fintype ι]
    (c : ℝ) (a b : ι → ℝ) (hc : 0 ≤ c) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hA : (∏ i, a i) ≤ 1) (hB : (∏ i, b i) ≤ 1) : 0 ≤ gap c a b := by
  unfold gap
  have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hA) (sub_nonpos.mpr hB)
  exact add_nonneg (by nlinarith only [mul_nonneg hc hm])
    (Finset.prod_nonneg fun i _ => add_nonneg (ha i) (hb i))

theorem pos_of_products_le_one {ι : Type*} [Fintype ι]
    (c : ℝ) (a b : ι → ℝ) (hc : 0 ≤ c) (hs : ∀ i, 0 < a i + b i)
    (hA : (∏ i, a i) ≤ 1) (hB : (∏ i, b i) ≤ 1) : 0 < gap c a b := by
  unfold gap
  have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hA) (sub_nonpos.mpr hB)
  exact add_pos_of_nonneg_of_pos (by nlinarith only [mul_nonneg hc hm])
    (Finset.prod_pos fun i _ => hs i)

end Plank.Convex.ProductGap

/-- info: 'Plank.Convex.ProductGap.mul_gap_upper_corner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ProductGap.mul_gap_upper_corner_le

/-- info: 'Plank.Convex.ProductGap.pos_of_upper_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ProductGap.pos_of_upper_corner
