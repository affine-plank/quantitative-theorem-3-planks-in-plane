/- The slope gap is a sum of nonnegative products of the six contact slacks. -/
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace Plank.Convex.PlanarSlopeGap

abbrev Triple := Fin 3 → ℝ

def gap (a b : Triple) : ℝ :=
  2 * ((∏ i, a i) - 1) * ((∏ i, b i) - 1) + ∏ i, (a i + b i)

def slack (a b p : Triple) (i : Fin 3) : ℝ :=
  p (i + 2) - a (i + 1) * p (i + 1) + a (i + 1) * b i * p i

/-- The gap is a sum of products of the six weighted slope slacks. -/
theorem identity (a b p : Triple) :
    (∏ i, p i) * gap a b =
      (∏ i, slack a b p i) + (∏ i, slack b a p i) +
      ∑ i, p (i + 1) * (a (i + 2) + b (i + 2)) *
        slack a b p i * slack b a p i := by
  simp [gap, slack, Fin.prod_univ_three, Fin.sum_univ_three]
  ring

/-- The exact weighted inequalities from the six planar pair contacts suffice.
The slopes may be zero; only the three weights must be strictly positive. -/
theorem gap_nonneg (a b p : Triple)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hp : ∀ i, 0 < p i)
    (hab : ∀ i, a (i + 1) * p (i + 1) ≤
      p (i + 2) + a (i + 1) * b i * p i)
    (hba : ∀ i, b (i + 1) * p (i + 1) ≤
      p (i + 2) + b (i + 1) * a i * p i) : 0 ≤ gap a b := by
  have hq (i : Fin 3) : 0 ≤ slack a b p i := by
    unfold slack
    linarith only [hab i]
  have hr (i : Fin 3) : 0 ≤ slack b a p i := by
    unfold slack
    linarith only [hba i]
  have hprod : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => hp i)
  have hgap : 0 ≤ (∏ i, p i) * gap a b := by
    rw [identity]
    apply add_nonneg
    · exact add_nonneg (Finset.prod_nonneg (fun i _ => hq i))
        (Finset.prod_nonneg (fun i _ => hr i))
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg
        (mul_nonneg (mul_nonneg (hp _).le (add_nonneg (ha _) (hb _))) (hq i)) (hr i))
  exact nonneg_of_mul_nonneg_right hgap hprod

end Plank.Convex.PlanarSlopeGap
