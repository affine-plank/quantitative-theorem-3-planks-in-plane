/- Vertical sections after an oblique band supported at the Y vertices. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAttainment
public import Plank.Proofs.Quant.PlanarConvexSectionIntegral
public import Plank.Proofs.Quant.UnimodalIntervalMerge

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSectionProfile
open Set MeasureTheory CrossedQuadrilateralAttainment

/-- The untruncated tent; it is negative outside the body's X projection. -/
def tent (S : Shape) (x : ℝ) : ℝ := min (1+x/S.c) (1-x/S.a)

theorem tent_left (S : Shape) {x : ℝ} (hx : x ≤ 0) :
    tent S x = 1+x/S.c := by
  apply min_eq_left
  have hc := div_nonpos_of_nonpos_of_nonneg hx S.hc.le
  have ha := div_nonpos_of_nonpos_of_nonneg hx S.ha.le
  linarith only [hc,ha]

theorem tent_right (S : Shape) {x : ℝ} (hx : 0 ≤ x) :
    tent S x = 1-x/S.a := by
  apply min_eq_right
  have hc := div_nonneg hx S.hc.le
  have ha := div_nonneg hx S.ha.le
  linarith only [hc,ha]

/-- A clipped upper or lower cap section, including zero outside the body. -/
def capProfile (S : Shape) (v k t x : ℝ) : ℝ :=
  max 0 (min ((S.b+S.d)*tent S x) (v*tent S x+k*x+t))

theorem continuous_capProfile (S : Shape) (v k t : ℝ) :
    Continuous (capProfile S v k t) := by
  unfold capProfile tent
  fun_prop

theorem capProfile_nonneg (S : Shape) (v k t x : ℝ) :
    0 ≤ capProfile S v k t x := le_max_left _ _

theorem capProfile_monotone (S : Shape) (v k t : ℝ) (hk : -v/S.c ≤ k) :
    MonotoneOn (capProfile S v k t) (Iic 0) := by
  intro x hx y hy hxy
  unfold capProfile
  rw [tent_left S hx,tent_left S hy]
  apply max_le_max le_rfl
  apply min_le_min
  · apply mul_le_mul_of_nonneg_left _ (add_pos S.hb S.hd).le
    linarith only [div_le_div_of_nonneg_right hxy S.hc.le]
  · simp only [neg_div] at hk
    have hc : 0 ≤ v/S.c+k := by linarith only [hk]
    have hm := mul_nonneg hc (sub_nonneg.mpr hxy)
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]

theorem capProfile_antitone (S : Shape) (v k t : ℝ) (hk : k ≤ v/S.a) :
    AntitoneOn (capProfile S v k t) (Ici 0) := by
  intro x hx y hy hxy
  unfold capProfile
  rw [tent_right S hx,tent_right S hy]
  apply max_le_max le_rfl
  apply min_le_min
  · apply mul_le_mul_of_nonneg_left _ (add_pos S.hb S.hd).le
    exact sub_le_sub_left (div_le_div_of_nonneg_right hxy S.ha.le) 1
  · have hc : 0 ≤ v/S.a-k := by linarith only [hk]
    have hm := mul_nonneg hc (sub_nonneg.mpr hxy)
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]

/-- The two disjoint cap lengths left by the band lo ≤ k*x+y ≤ hi. -/
def residual (S : Shape) (k lo hi x : ℝ) : ℝ :=
  capProfile S S.b k (-hi) x+capProfile S S.d (-k) lo x

theorem continuous_residual (S : Shape) (k lo hi : ℝ) :
    Continuous (residual S k lo hi) :=
  (continuous_capProfile S _ _ _).add (continuous_capProfile S _ _ _)

/-- Exactly the four vertex inequalities that put the minimum at Y- and
the maximum at Y+, expressed for the oriented form k*x+y. -/
def YSupports (S : Shape) (k : ℝ) : Prop :=
  -S.b/S.c ≤ k ∧ k ≤ S.b/S.a ∧ -S.d/S.a ≤ k ∧ k ≤ S.d/S.c

theorem residual_monotone (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi : ℝ) :
    MonotoneOn (residual S k lo hi) (Iic 0) := by
  exact (capProfile_monotone S _ _ _ hk.1).add
    (capProfile_monotone S _ _ _ (by simpa only [neg_div] using neg_le_neg hk.2.2.2))

theorem residual_antitone (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi : ℝ) :
    AntitoneOn (residual S k lo hi) (Ici 0) := by
  exact (capProfile_antitone S _ _ _ hk.2.1).add
    (capProfile_antitone S _ _ _ (by simpa only [neg_div,neg_neg] using neg_le_neg hk.2.2.1))

theorem merge_residual (S : Shape) {k : ℝ} (hk : YSupports S k) (lo hi : ℝ)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ∃ l u : ℝ, a ≤ l ∧ u ≤ d ∧ l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (∫ x in a..b, residual S k lo hi x)+(∫ x in c..d, residual S k lo hi x) ≤
        ∫ x in l..u, residual S k lo hi x :=
  UnimodalIntervalMerge.exists_interval (continuous_residual S k lo hi)
    (residual_monotone S hk lo hi) (residual_antitone S hk lo hi) hab hbc hcd

end Quant.CrossedQuadrilateralSectionProfile

/-- info: 'Quant.CrossedQuadrilateralSectionProfile.merge_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSectionProfile.merge_residual
