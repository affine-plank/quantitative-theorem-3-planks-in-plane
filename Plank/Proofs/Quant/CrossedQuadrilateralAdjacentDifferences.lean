/- Finite-difference estimates for the adjacent-support residual area primitive. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAdjacentProfile
public import Plank.Proofs.Quant.IntervalIntegralSecondDifference

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAdjacentDifferences
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralAdjacentProfile IntervalIntegralSecondDifference

theorem tent_lower (S : Shape) {x y : ℝ} (hxy : x ≤ y) :
    tent S x ≤ tent S y+(y-x)/S.a := by
  apply min_increment
  · have h₁ := div_le_div_of_nonneg_right hxy S.hc.le
    have h₂ := div_nonneg (sub_nonneg.mpr hxy) S.ha.le
    linarith only [h₁,h₂]
  · simp only [div_eq_mul_inv]
    nlinarith only []

theorem cap_lower (S : Shape) {k v s x y : ℝ} (hk : 0 ≤ k)
    (hv : 0 ≤ v) (hvH : v ≤ S.b+S.d) (hs : -k ≤ s) (hxy : x ≤ y) (t : ℝ) :
    capProfile S v s t x ≤ capProfile S v s t y+((S.b+S.d)/S.a+k)*(y-x) := by
  have hδ : 0 ≤ ((S.b+S.d)/S.a+k)*(y-x) :=
    mul_nonneg (add_nonneg (div_pos (add_pos S.hb S.hd) S.ha).le hk) (sub_nonneg.mpr hxy)
  have hq := tent_lower S hxy
  have hH := mul_le_mul_of_nonneg_left hq (add_pos S.hb S.hd).le
  have hvq := mul_le_mul_of_nonneg_left hq hv
  have hpos := mul_nonneg hk (sub_nonneg.mpr hxy)
  have hvs := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hxy)
  have hvr := mul_le_mul_of_nonneg_right hvH
    (div_nonneg (sub_nonneg.mpr hxy) S.ha.le)
  unfold capProfile
  apply max_increment hδ
  apply min_increment
  · simp only [div_eq_mul_inv] at hH ⊢
    nlinarith only [hH,hpos]
  · simp only [div_eq_mul_inv] at hvq hvr ⊢
    nlinarith only [hvq,hvr,hvs]

def lowerConstant (S : Shape) (k : ℝ) : ℝ := 2*((S.b+S.d)/S.a+k)

theorem lowerConstant_pos (S : Shape) {k : ℝ} (hk : Sector S k) :
    0 < lowerConstant S k := by
  exact mul_pos (by norm_num) (add_pos (div_pos (add_pos S.hb S.hd) S.ha) (sector_pos S hk))

theorem lower_slope (S : Shape) {k : ℝ} (hk : Sector S k) (lo hi : ℝ)
    {x y : ℝ} (hxy : x ≤ y) :
    residual S k lo hi x ≤ residual S k lo hi y+lowerConstant S k*(y-x) := by
  have h₁ := cap_lower S (sector_pos S hk).le S.hb.le
    (by linarith only [S.hd] : S.b ≤ S.b+S.d)
    (by linarith only [sector_pos S hk] : -k ≤ k) hxy (-hi)
  have h₂ := cap_lower S (sector_pos S hk).le S.hd.le
    (by linarith only [S.hb] : S.d ≤ S.b+S.d) (le_rfl : -k ≤ -k) hxy lo
  unfold CrossedQuadrilateralSectionProfile.residual lowerConstant
  linarith only [h₁,h₂]

def areaPrimitive (S : Shape) (k lo hi : ℝ) : ℝ → ℝ := primitive (residual S k lo hi)

theorem upper_difference (S : Shape) {k lo hi : ℝ} (hk : Sector S k) (ho : lo ≤ hi)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    areaPrimitive S k lo hi (x+h)+areaPrimitive S k lo hi (x-h)-2*areaPrimitive S k lo hi x ≤
      (S.b+S.d)/S.c*h^2 := by
  apply IntervalIntegralSecondDifference.upper (continuous_residual S k lo hi) hh
  intro t ht
  have hb := upper_slope S hk ho (x := x-t) (y := x+t) (by linarith only [ht.1])
  nlinarith only [hb]

theorem lower_difference (S : Shape) {k lo hi : ℝ} (hk : Sector S k)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    -lowerConstant S k*h^2 ≤
      areaPrimitive S k lo hi (x+h)+areaPrimitive S k lo hi (x-h)-2*areaPrimitive S k lo hi x := by
  apply IntervalIntegralSecondDifference.lower (continuous_residual S k lo hi) hh
  intro t ht
  have hb := lower_slope S hk lo hi (x := x-t) (y := x+t) (by linarith only [ht.1])
  nlinarith only [hb]

theorem tail_lower_difference (S : Shape) {k lo hi : ℝ} (hk : Sector S k)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) (hx : valley S k lo ≤ x-h) :
    -((S.b+S.d)/S.a)*h^2 ≤
      areaPrimitive S k lo hi (x+h)+areaPrimitive S k lo hi (x-h)-2*areaPrimitive S k lo hi x := by
  apply IntervalIntegralSecondDifference.lower (continuous_residual S k lo hi) hh
  intro t ht
  have hb := right_lower_after S hk (hi := hi) (x := x-t) (y := x+t)
    (by linarith only [hx,ht.2]) (by linarith only [ht.1])
  nlinarith only [hb]

end Quant.CrossedQuadrilateralAdjacentDifferences

/-- info: 'Quant.CrossedQuadrilateralAdjacentDifferences.tail_lower_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAdjacentDifferences.tail_lower_difference
