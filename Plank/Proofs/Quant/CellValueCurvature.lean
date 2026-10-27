/- Scalar value-curvature contradiction and the cyclic three-cell linear system.
Brunn--Minkowski, actual gap cells and their Jacobian remain hand geometry. -/
module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace Plank.CellValueCurvature

/-- If a direction differentiates every cell area into that same area,
planar Brunn--Minkowski bounds the total curvature by G/2. At a stationary
point, positive margin curvature then forces a strictly negative margin. -/
theorem strict_negative_margin (V delta G velocity curvature : ℝ)
    (hV : 0 < V) (hd : 0 < delta) (hG : 0 < G)
    (hstationary : G = 2*V*delta*velocity)
    (hconcave : curvature ≤ G/2)
    (hpositive : 2*V*velocity^2 < curvature) : G < V*delta^2 := by
  have hcoef : 0 < 2*V*delta := mul_pos (mul_pos (by norm_num) hV) hd
  have hv : 0 < velocity := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hcoef.le (le_of_not_gt hn)
    linarith only [hm,hstationary,hG]
  have hf : 0 < (2*V*velocity)*(delta-2*velocity) := by
    nlinarith only [hstationary,hconcave,hpositive]
  have hpos : 0 < 2*V*velocity := mul_pos (mul_pos (by norm_num) hV) hv
  have hdiff : 0 < delta-2*velocity := (mul_pos_iff_of_pos_left hpos).mp hf
  have hlast := mul_pos (mul_pos hV hd) hdiff
  nlinarith only [hstationary,hlast]

/-- The cyclic pair-cell Jacobian is onto when its two determinant monomials
have positive sum. The coefficients need not separately be positive. -/
theorem cyclic_system_onto (a b c d e f A B C : ℝ)
    (hdet : a*c*f+b*d*e ≠ 0) :
    ∃ x y z : ℝ, a*x+b*y=A ∧ c*y+d*z=B ∧ e*x+f*z=C := by
  let D := a*c*f+b*d*e
  let X := c*f*A-b*f*B+b*d*C
  let Y := d*e*A+a*f*B-a*d*C
  let Z := -c*e*A+b*e*B+a*c*C
  refine ⟨X/D,Y/D,Z/D,?_,?_,?_⟩
  · calc
      a*(X/D)+b*(Y/D) = (a*X+b*Y)/D := by ring
      _ = A := by
        apply (div_eq_iff hdet).2
        dsimp [D,X,Y]
        ring
  · calc
      c*(Y/D)+d*(Z/D) = (c*Y+d*Z)/D := by ring
      _ = B := by
        apply (div_eq_iff hdet).2
        dsimp [D,Y,Z]
        ring
  · calc
      e*(X/D)+f*(Z/D) = (e*X+f*Z)/D := by ring
      _ = C := by
        apply (div_eq_iff hdet).2
        dsimp [D,X,Z]
        ring

theorem cyclic_determinant_pos (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    0 < a*c*f+b*d*e :=
  add_pos (mul_pos (mul_pos ha hc) hf) (mul_pos (mul_pos hb hd) he)

/-- The same argument in dimension d>1 has the coefficient (d-1)/d.
This is only the scalar final step, with all geometric/calculus inputs assumed. -/
theorem strict_negative_margin_scaled (target G slope curvatureFactor velocity curvature : ℝ)
    (ht : 0 < target) (hG : 0 < G)
    (hc : 0 < curvatureFactor)
    (hstationary : G = slope*velocity)
    (hconcave : curvature ≤ curvatureFactor*G)
    (hpositive : curvatureFactor*(slope*velocity)^2/target < curvature) :
    G < target := by
  rw [← hstationary] at hpositive
  have hh : curvatureFactor*G^2 < (curvatureFactor*G)*target := by
    have hlt := lt_of_lt_of_le hpositive hconcave
    exact (div_lt_iff₀ ht).mp hlt
  have hp : 0 < curvatureFactor*G := mul_pos hc hG
  have hh' : (curvatureFactor*G)*G < (curvatureFactor*G)*target := by
    nlinarith only [hh]
  exact (mul_lt_mul_iff_right₀ hp).mp hh'

end Plank.CellValueCurvature
