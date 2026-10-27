/- Symmetric endpoint motion and its strict quadratic curvature obstruction. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralPairBudget
public import Plank.Proofs.Quant.CrossedQuadrilateralAdjacentDifferences

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAdjacentVariation
open Set MeasureTheory CrossedQuadrilateralAttainment
open CrossedQuadrilateralAdjacentProfile CrossedQuadrilateralAdjacentDifferences
open CrossedQuadrilateralPairBudget

theorem budget_plus (S : Shape) (k a b c d lo hi e t : ℝ) :
    budget S k (a-S.c*t) (b+e*t) c (d+S.a*t) lo hi =
      budget S k a b c d lo hi+((S.a+S.c+e)/(S.a+S.c))*t := by
  unfold budget
  ring

theorem budget_minus (S : Shape) (k a b c d lo hi e t : ℝ) :
    budget S k (a+S.c*t) (b-e*t) c (d-S.a*t) lo hi =
      budget S k a b c d lo hi-((S.a+S.c+e)/(S.a+S.c))*t := by
  unfold budget
  ring

theorem gap_difference_upper (S : Shape) {k a b c d lo hi e t : ℝ}
    (hk : Sector S k) (ho : lo < hi) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hp : a-S.c*t ≤ b+e*t ∧ b+e*t ≤ c ∧ c ≤ d+S.a*t)
    (hm : a+S.c*t ≤ b-e*t ∧ b-e*t ≤ c ∧ c ≤ d-S.a*t)
    (hv : valley S k lo ≤ d-S.a*t) :
    gap S k (a-S.c*t) (b+e*t) c (d+S.a*t) lo hi+
      gap S k (a+S.c*t) (b-e*t) c (d-S.a*t) lo hi-
      2*gap S k a b c d lo hi ≤
      ((S.b+S.d)*(S.a+S.c)+lowerConstant S k*e^2)*t^2 := by
  have ha := upper_difference S hk ho.le a (mul_nonneg S.hc.le ht)
  have hb := lower_difference S hk (lo := lo) (hi := hi) b (mul_nonneg he ht)
  have hd := tail_lower_difference S hk (hi := hi) d (mul_nonneg S.ha.le ht) hv
  have hca : (S.b+S.d)/S.c*(S.c*t)^2 = (S.b+S.d)*S.c*t^2 := by
    field_simp
  have hda : -((S.b+S.d)/S.a)*(S.a*t)^2 = -(S.b+S.d)*S.a*t^2 := by
    field_simp
  rw [hca] at ha
  rw [hda] at hd
  unfold gap
  rw [ParallelPairGapIntegral.residual_area S k ho hp.1 hp.2.1 hp.2.2,
    ParallelPairGapIntegral.residual_area S k ho hm.1 hm.2.1 hm.2.2,
    ParallelPairGapIntegral.residual_area S k ho hab hbc hcd]
  unfold areaPrimitive at ha hb hd
  nlinarith only [ha,hb,hd]

theorem coefficient_strict {H W L e : ℝ} (hH : 0 < H) (hW : 0 < W)
    (he : 0 < e) (hsmall : L*e < H) :
    H*W+L*e^2 < H/W*(W+e)^2 := by
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ hW).mpr
  have hm := mul_lt_mul_of_pos_right hsmall (mul_pos he hW)
  have hp := mul_pos (mul_pos hH he) hW
  have hq := mul_nonneg hH.le (sq_nonneg e)
  nlinarith only [hm,hp,hq]

end Quant.CrossedQuadrilateralAdjacentVariation

/-- info: 'Quant.CrossedQuadrilateralAdjacentVariation.gap_difference_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAdjacentVariation.gap_difference_upper
