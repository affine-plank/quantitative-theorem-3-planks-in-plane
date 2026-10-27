/- Reciprocal complements and a finite-product comparison prove the central slope inequality. -/
module
public import Plank.Convex.SameSignCapProduct
public import Plank.Convex.ReciprocalCorner
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Plank.Convex.SameSignCapAlgebra Plank.Convex.SameSignCapTransfer
open Plank.Convex.SameSignCapProduct
namespace Plank.Convex.SameSignCapSingleCorner

theorem gap_product (a b : Point) : cycleGap a b = ProductGap.gap 2 a b := by
  simp only [cycleGap, slopeProduct, mixedSum, ProductGap.gap, Fin.sum_univ_three,
    Fin.prod_univ_three, next, prev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem gap_swap (a b : Point) : cycleGap b a = cycleGap a b := by
  rw [gap_product, gap_product]
  unfold ProductGap.gap
  congr 1
  · ring
  · congr 1; ext i; exact add_comm _ _

def lowerAt (w : Point) (t : ℝ) (i : Fin 3) : ℝ := (t - w i) / w (next i)
def upperAt (w : Point) (t : ℝ) (i : Fin 3) : ℝ := w i / (t - w (next i))

/-- An expanded form of the corner identity, retained for compatibility. -/
theorem corner_factor (w : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hw : ∀ i, 0 < w i) (hδ : ∀ i, w i < δ) :
    cycleGap (upperAt w δ) (lowerAt w τ) =
      (∏ i, (τ * (τ - w i) + (δ - τ) * w (next i))) /
        ((∏ i, (δ - w i)) * ∏ i, w i) := by
  rw [gap_product]
  unfold ProductGap.gap
  simp only [upperAt, lowerAt, Fin.prod_univ_three, next,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp [(hw 0).ne', (hw 1).ne', (hw 2).ne',
    (sub_pos.mpr (hδ 0)).ne', (sub_pos.mpr (hδ 1)).ne', (sub_pos.mpr (hδ 2)).ne']
  have hD : δ = w 0 + w 1 + w 2 - τ := by
    simpa only [Fin.sum_univ_three] using (eq_sub_iff_add_eq.mpr hsum.symm)
  rw [hD]
  ring

/-- Reciprocal complements make the corner gap a product of positive differences. -/
theorem corner_pos (w : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hw : ∀ i, 0 < w i)
    (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ) :
    0 < cycleGap (upperAt w δ) (lowerAt w τ) := by
  rw [gap_product]
  apply ReciprocalCorner.pos
  · intro i
    have hs : w i + w (next i) + w (prev i) = δ + τ := by
      rw [← Plank.Convex.SameSignCapAlgebra.sum_cycle]
      exact hsum
    apply le_of_lt
    apply (one_lt_div (sub_pos.mpr (hδ (next i)))).mpr
    linarith only [hs, hτ (prev i)]
  · intro i
    have hn : i + 1 = next i := by fin_cases i <;> rfl
    rw [hn]
    simp only [lowerAt, upperAt, next_next, inv_div]
    field_simp [(hw (next i)).ne']
    have hs : w i + w (next i) + w (prev i) = δ + τ := by
      rw [← Plank.Convex.SameSignCapAlgebra.sum_cycle]
      exact hsum
    linarith only [hs]

theorem corner_nonneg (w : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hw : ∀ i, 0 < w i)
    (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ) :
    0 ≤ cycleGap (upperAt w δ) (lowerAt w τ) :=
  (corner_pos w δ τ hsum hw hδ hτ).le

theorem lowerAt_le_one (w : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hw : ∀ i, 0 < w i) (hδ : ∀ i, w i < δ)
    (i : Fin 3) : lowerAt w τ i ≤ 1 := by
  apply (div_le_one (hw (next i))).mpr
  have hs : w i + w (next i) + w (prev i) = δ + τ := by
    rw [← Plank.Convex.SameSignCapAlgebra.sum_cycle]
    exact hsum
  linarith only [hs, hδ (prev i)]

theorem gap_large_product_pos (w a b : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hw : ∀ i, 0 < w i)
    (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ upperAt w δ i)
    (hb : ∀ i, lowerAt w τ i ≤ b i) (hA : 1 ≤ ∏ i, a i) : 0 < cycleGap a b := by
  have hl (i : Fin 3) : 0 < lowerAt w τ i := div_pos (sub_pos.mpr (hτ i)) (hw _)
  have hsmall := ProductGap.pos_of_upper_corner 2 a (lowerAt w τ) (upperAt w δ)
    (by norm_num) ha0 (fun i => (hl i).le)
    ha
      (by simpa using (Finset.prod_le_prod₀ (fun i _ => (hl i).le)
      (fun i _ => lowerAt_le_one w δ τ hsum hw hδ i)))
    (zero_lt_one.trans_le hA)
    (by rw [← gap_product]; exact corner_pos w δ τ hsum hw hδ hτ)
  have hmono := ProductGap.mono_right 2 a (lowerAt w τ) b (by norm_num) ha0
    (fun i => (hl i).le) hA hb
  simp only [← gap_product] at hsmall hmono
  exact hsmall.trans_le hmono

theorem gap_large_product (w a b : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hw : ∀ i, 0 < w i)
    (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ upperAt w δ i)
    (hb : ∀ i, lowerAt w τ i ≤ b i) (hA : 1 ≤ ∏ i, a i) : 0 ≤ cycleGap a b :=
  (gap_large_product_pos w a b δ τ hsum hw hδ hτ ha0 ha hb hA).le

/-- The complete central-interval theorem, without endpoint enumeration or interpolation. -/
theorem cycleGap_pos_of_intervals (w a b : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ)
    (ha : ∀ i, (δ - w i) / w (next i) ≤ a i ∧ a i ≤ w i / (δ - w (next i)))
    (hb : ∀ i, (τ - w i) / w (next i) ≤ b i ∧ b i ≤ w i / (τ - w (next i))) :
    0 < cycleGap a b := by
  have hw (i : Fin 3) : 0 < w i := by
    have hs : w i + w (next i) + w (prev i) = δ + τ := by
      rw [← Plank.Convex.SameSignCapAlgebra.sum_cycle]
      exact hsum
    linarith only [hs, hδ (next i), hτ (prev i)]
  have ha_pos (i : Fin 3) : 0 < a i :=
    (div_pos (sub_pos.mpr (hδ i)) (hw _)).trans_le (ha i).1
  have hb_pos (i : Fin 3) : 0 < b i :=
    (div_pos (sub_pos.mpr (hτ i)) (hw _)).trans_le (hb i).1
  by_cases hA : 1 ≤ ∏ i, a i
  · exact gap_large_product_pos w a b δ τ hsum hw hδ hτ (fun i => (ha_pos i).le)
      (fun i => (ha i).2) (fun i => (hb i).1) hA
  by_cases hB : 1 ≤ ∏ i, b i
  · rw [← gap_swap]
    exact gap_large_product_pos w b a τ δ (by linarith only [hsum]) hw hτ hδ (fun i => (hb_pos i).le)
      (fun i => (hb i).2) (fun i => (ha i).1) hB
  · rw [gap_product]
    exact ProductGap.pos_of_products_le_one 2 a b (by norm_num)
      (fun i => add_pos (ha_pos i) (hb_pos i))
      (le_of_not_ge hA) (le_of_not_ge hB)

theorem cycleGap_nonneg_of_intervals (w a b : Point) (δ τ : ℝ)
    (hsum : (∑ i, w i) = δ + τ) (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ)
    (ha : ∀ i, (δ - w i) / w (next i) ≤ a i ∧ a i ≤ w i / (δ - w (next i)))
    (hb : ∀ i, (τ - w i) / w (next i) ≤ b i ∧ b i ≤ w i / (τ - w (next i))) :
    0 ≤ cycleGap a b :=
  (cycleGap_pos_of_intervals w a b δ τ hsum hδ hτ ha hb).le

end Plank.Convex.SameSignCapSingleCorner

/-- info: 'Plank.Convex.SameSignCapSingleCorner.cycleGap_pos_of_intervals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapSingleCorner.cycleGap_pos_of_intervals
