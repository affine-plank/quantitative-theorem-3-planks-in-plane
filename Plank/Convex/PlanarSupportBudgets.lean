/- The three coordinate budgets satisfy a nonnegative polynomial identity.
Dividing by their positive product gives the relative-width bound directly. -/
module
public import Plank.Convex.PlanarSlopeGap
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace Plank.Convex.PlanarSupportMatrix
open PlanarSlopeGap (Triple)

-- Retain the historical namespace of the shared support coefficients.
def lower (a b : Triple) (i : Fin 3) : ℝ := 1 + b i * a (i + 1) * b (i + 2)
def upper (a b : Triple) (i : Fin 3) : ℝ := lower b a i
def denom (a b : Triple) (i : Fin 3) : ℝ := lower a b i * upper a b i

def budget (a b w : Triple) (i : Fin 3) : ℝ :=
  denom a b i * w i +
    b i * upper a b i * (w (i + 1) + a (i + 1) * w (i + 2)) +
    a i * lower a b i * (w (i + 1) + b (i + 1) * w (i + 2))

/-- The scalar identity underlying the width bound. It requires neither
positivity nor nonvanishing of widths, slopes, or the cycle defect. -/
theorem budget_identity (a b w : Triple) :
    (∑ i, denom a b i * w i * budget a b w (i + 1) * budget a b w (i + 2)) -
      (∏ i, budget a b w i) =
    ((∏ i, a i) * (∏ i, b i) - 1) ^ 2 *
      ((∑ i, (budget a b w i - denom a b i * w i) * w (i + 1) * w (i + 2)) +
        PlanarSlopeGap.gap a b * ∏ i, w i) := by
  simp [budget, denom, lower, upper, PlanarSlopeGap.gap,
    Fin.prod_univ_three, Fin.sum_univ_three]
  ring

/-- Actual positive ranges and nonnegative widths satisfy the plank bound
whenever the three support budgets hold and the slope gap is nonnegative. -/
theorem scalar_width_bound (a b w R : Triple)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hw : ∀ i, 0 ≤ w i) (hR : ∀ i, 0 < R i)
    (hbudget : ∀ i, denom a b i * R i ≤ budget a b w i)
    (hgap : 0 ≤ PlanarSlopeGap.gap a b) : 1 ≤ ∑ i, w i / R i := by
  have hL (i : Fin 3) : 0 < lower a b i :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (hb i) (ha (i + 1))) (hb (i + 2)))
  have hU (i : Fin 3) : 0 < upper a b i :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (ha i) (hb (i + 1))) (ha (i + 2)))
  have hD (i : Fin 3) : 0 < denom a b i := mul_pos (hL i) (hU i)
  have hS (i : Fin 3) : 0 < budget a b w i :=
    (mul_pos (hD i) (hR i)).trans_le (hbudget i)
  have hoff (i : Fin 3) : 0 ≤ budget a b w i - denom a b i * w i := by
    have h1 := mul_nonneg (mul_nonneg (hb i) (hU i).le)
      (add_nonneg (hw (i + 1)) (mul_nonneg (ha (i + 1)) (hw (i + 2))))
    have h2 := mul_nonneg (mul_nonneg (ha i) (hL i).le)
      (add_nonneg (hw (i + 1)) (mul_nonneg (hb (i + 1)) (hw (i + 2))))
    dsimp only [budget]
    linarith only [h1, h2]
  have hrem : 0 ≤
      (∑ i, denom a b i * w i * budget a b w (i + 1) * budget a b w (i + 2)) -
        (∏ i, budget a b w i) := by
    rw [budget_identity]
    exact mul_nonneg (sq_nonneg _) (add_nonneg
      (Finset.sum_nonneg (fun i _ => mul_nonneg
        (mul_nonneg (hoff i) (hw (i + 1))) (hw (i + 2))))
      (mul_nonneg hgap (Finset.prod_nonneg (fun i _ => hw i))))
  have hid : (∑ i, denom a b i * w i / budget a b w i) - 1 =
      ((∑ i, denom a b i * w i * budget a b w (i + 1) * budget a b w (i + 2)) -
        ∏ i, budget a b w i) / ∏ i, budget a b w i := by
    simp [Fin.sum_univ_three, Fin.prod_univ_three]
    field_simp [(hS 0).ne', (hS 1).ne', (hS 2).ne']
  have hratio : 1 ≤ ∑ i, denom a b i * w i / budget a b w i := by
    apply sub_nonneg.mp
    rw [hid]
    exact div_nonneg hrem (Finset.prod_pos (fun i _ => hS i)).le
  apply hratio.trans
  apply Finset.sum_le_sum
  intro i _
  apply (div_le_div_iff₀ (hS i) (hR i)).mpr
  have h := mul_le_mul_of_nonneg_left (hbudget i) (hw i)
  nlinarith only [h]

end Plank.Convex.PlanarSupportMatrix

/-- info: 'Plank.Convex.PlanarSupportMatrix.budget_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarSupportMatrix.budget_identity

/-- info: 'Plank.Convex.PlanarSupportMatrix.scalar_width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarSupportMatrix.scalar_width_bound
