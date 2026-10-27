/- Section inequalities in the adjacent-support sector; not yet its equality catalogue. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSectionGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAdjacentProfile
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile

def Sector (S : Shape) (k : ℝ) : Prop := S.b/S.a ≤ k ∧ k ≤ S.d/S.c

theorem sector_pos (S : Shape) {k : ℝ} (hk : Sector S k) : 0 < k :=
  (div_pos S.hb S.ha).trans_le hk.1

theorem clip_nonneg (H t : ℝ) :
    max 0 (min H (max 0 t)) = max 0 (min H t) := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right ht]
  · have ht' := le_of_not_ge ht
    rw [max_eq_left ht',max_eq_left (min_le_right H t |>.trans ht'),
      max_eq_left (min_le_right H 0)]

/-- The two cap pieces are disjoint. Their combined clipped length is
the minimum of the body height and the sum of their positive lengths. -/
theorem clip_sum {H t b : ℝ} (h : t+b ≤ H) :
    max 0 (min H t)+max 0 (min H b) = max 0 (min H (max 0 t+max 0 b)) := by
  by_cases ht : t ≤ 0
  · rw [max_eq_left (min_le_right H t |>.trans ht),max_eq_left ht,zero_add,zero_add,
      clip_nonneg]
  by_cases hb : b ≤ 0
  · rw [max_eq_left (min_le_right H b |>.trans hb),max_eq_left hb,add_zero,add_zero,
      clip_nonneg]
  have ht' : 0 ≤ t := (lt_of_not_ge ht).le
  have hb' : 0 ≤ b := (lt_of_not_ge hb).le
  rw [min_eq_right (by linarith only [h,hb']),min_eq_right (by linarith only [h,ht']),
    max_eq_right ht',max_eq_right hb',min_eq_right h,max_eq_right (add_nonneg ht' hb')]

theorem residual_formula (S : Shape) {k lo hi : ℝ} (ho : lo ≤ hi) (x : ℝ) :
    residual S k lo hi x = max 0 (min ((S.b+S.d)*tent S x)
      (max 0 (S.b*tent S x+k*x-hi)+max 0 (S.d*tent S x-k*x+lo))) := by
  unfold CrossedQuadrilateralSectionProfile.residual capProfile
  have he : S.d*tent S x+ -k*x+lo = S.d*tent S x-k*x+lo := by ring
  rw [he]
  change max 0 (min ((S.b+S.d)*tent S x) (S.b*tent S x+k*x-hi))+
    max 0 (min ((S.b+S.d)*tent S x) (S.d*tent S x-k*x+lo)) = _
  apply clip_sum
  nlinarith only [ho]

theorem max_increment {u v δ : ℝ} (hδ : 0 ≤ δ) (h : v ≤ u+δ) :
    max 0 v ≤ max 0 u+δ := by
  apply max_le
  · exact add_nonneg (le_max_left _ _) hδ
  · exact h.trans (by linarith only [le_max_right (0 : ℝ) u])

theorem min_increment {u v u' v' δ : ℝ} (hu : u' ≤ u+δ) (hv : v' ≤ v+δ) :
    min u' v' ≤ min u v+δ := by
  calc
    min u' v' ≤ min (u+δ) (v+δ) := min_le_min hu hv
    _ = _ := min_add_add_right u v δ

theorem left_upper (S : Shape) {k lo hi : ℝ} (hk : Sector S k) (ho : lo ≤ hi)
    {x y : ℝ} (hy : y ≤ 0) (hxy : x ≤ y) :
    residual S k lo hi y ≤ residual S k lo hi x+(S.b+S.d)/S.c*(y-x) := by
  have hx := hxy.trans hy
  have hp : 0 ≤ (S.b/S.c+k)*(y-x) :=
    mul_nonneg (add_nonneg (div_pos S.hb S.hc).le (sector_pos S hk).le) (sub_nonneg.mpr hxy)
  have hq : 0 ≤ (S.d/S.c-k)*(y-x) :=
    mul_nonneg (sub_nonneg.mpr hk.2) (sub_nonneg.mpr hxy)
  rw [residual_formula S ho,residual_formula S ho,tent_left S hy,tent_left S hx]
  apply max_increment (mul_nonneg (div_pos (add_pos S.hb S.hd) S.hc).le (sub_nonneg.mpr hxy))
  apply min_increment
  · simp only [div_eq_mul_inv]
    nlinarith only []
  · have htop := max_increment hp (u := S.b*(1+x/S.c)+k*x-hi)
      (v := S.b*(1+y/S.c)+k*y-hi) (by simp only [div_eq_mul_inv]; nlinarith only [])
    have hbot := max_increment hq (u := S.d*(1+x/S.c)-k*x+lo)
      (v := S.d*(1+y/S.c)-k*y+lo) (by simp only [div_eq_mul_inv]; nlinarith only [])
    simp only [div_eq_mul_inv] at htop hbot ⊢
    nlinarith only [htop,hbot]

theorem right_upper (S : Shape) {k : ℝ} (hk : Sector S k) (lo hi : ℝ)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    residual S k lo hi y ≤ residual S k lo hi x+(k-S.b/S.a)*(y-x) := by
  have hy := hx.trans hxy
  have hp : 0 ≤ (k-S.b/S.a)*(y-x) :=
    mul_nonneg (sub_nonneg.mpr hk.1) (sub_nonneg.mpr hxy)
  have htop : capProfile S S.b k (-hi) y ≤
      capProfile S S.b k (-hi) x+(k-S.b/S.a)*(y-x) := by
    unfold capProfile
    rw [tent_right S hx,tent_right S hy]
    apply max_increment hp
    apply min_increment
    · have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxy S.ha.le)
        (add_pos S.hb S.hd).le
      nlinarith only [hh,hp]
    · simp only [div_eq_mul_inv]
      nlinarith only []
  have hbot := capProfile_antitone S S.d (-k) lo
    (by linarith only [sector_pos S hk,div_pos S.hd S.ha]) hx hy hxy
  unfold CrossedQuadrilateralSectionProfile.residual
  linarith only [htop,hbot]

/-- A global upper slope bound, even though the profile can have two peaks. -/
theorem upper_slope (S : Shape) {k lo hi : ℝ} (hk : Sector S k) (ho : lo ≤ hi)
    {x y : ℝ} (hxy : x ≤ y) :
    residual S k lo hi y ≤ residual S k lo hi x+(S.b+S.d)/S.c*(y-x) := by
  have hs : k-S.b/S.a ≤ (S.b+S.d)/S.c := by
    have hp := div_pos S.hb S.ha
    have hb := div_pos S.hb S.hc
    rw [add_div]
    linarith only [hk.2,hp,hb]
  by_cases hy : y ≤ 0
  · exact left_upper S hk ho hy hxy
  by_cases hx : 0 ≤ x
  · have hh := right_upper S hk lo hi hx hxy
    have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hxy)
    linarith only [hh,hm]
  have hl := left_upper S hk ho (x := x) (y := 0) le_rfl (le_of_not_ge hx)
  have hr := right_upper S hk lo hi (x := 0) (y := y) le_rfl (le_of_not_ge hy)
  have hm := mul_le_mul_of_nonneg_right hs (le_of_not_ge hy)
  nlinarith only [hl,hr,hm]

def valley (S : Shape) (k lo : ℝ) : ℝ := max 0 ((S.d+lo)/(S.d/S.a+k))

theorem left_monotone (S : Shape) {k : ℝ} (hk : Sector S k) (lo hi : ℝ) :
    MonotoneOn (residual S k lo hi) (Iic 0) := by
  apply (capProfile_monotone S S.b k (-hi) ?_).add
    (capProfile_monotone S S.d (-k) lo ?_)
  · have hb := div_pos S.hb S.hc
    simp only [neg_div]
    linarith only [sector_pos S hk,hb]
  · simpa only [neg_div] using neg_le_neg hk.2

theorem right_antitone_before (S : Shape) {k lo hi : ℝ} (hk : Sector S k) (ho : lo ≤ hi)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ (S.d+lo)/(S.d/S.a+k)) :
    residual S k lo hi y ≤ residual S k lo hi x := by
  have hq : 0 < S.d/S.a+k := add_pos (div_pos S.hd S.ha) (sector_pos S hk)
  have hby := (le_div_iff₀ hq).mp hy
  have hbx := mul_le_mul_of_nonneg_right hxy hq.le
  have bypos : 0 ≤ S.d*(1-y/S.a)-k*y+lo := by
    simp only [div_eq_mul_inv] at hby ⊢
    nlinarith only [hby]
  have bxpos : 0 ≤ S.d*(1-x/S.a)-k*x+lo := by
    simp only [div_eq_mul_inv] at hbx hby ⊢
    nlinarith only [hbx,hby]
  have he (t : ℝ) : max 0 (S.b*(1-t/S.a)+k*t-hi)+(S.d*(1-t/S.a)-k*t+lo) =
      max (S.d*(1-t/S.a)-k*t+lo) ((S.b+S.d)*(1-t/S.a)-(hi-lo)) := by
    rw [← max_add_add_right]
    congr 1 <;> ring
  rw [residual_formula S ho,residual_formula S ho,tent_right S (hx.trans hxy),tent_right S hx,
    max_eq_right bypos,max_eq_right bxpos,he,he]
  apply max_le_max le_rfl
  have hH : (S.b+S.d)*(1-y/S.a) ≤ (S.b+S.d)*(1-x/S.a) := by
    apply mul_le_mul_of_nonneg_left _ (add_pos S.hb S.hd).le
    exact sub_le_sub_left (div_le_div_of_nonneg_right hxy S.ha.le) 1
  apply min_le_min hH
  apply max_le_max
  · simp only [div_eq_mul_inv] at hbx ⊢
    nlinarith only [hbx]
  · exact sub_le_sub_right hH _

theorem antitone_before_valley (S : Shape) {k lo hi : ℝ} (hk : Sector S k) (ho : lo ≤ hi) :
    AntitoneOn (residual S k lo hi) (Icc 0 (valley S k lo)) := by
  intro x hx y hy hxy
  by_cases hv : 0 ≤ (S.d+lo)/(S.d/S.a+k)
  · apply right_antitone_before S hk ho hx.1 hxy
    simpa only [valley,max_eq_right hv] using hy.2
  · have hv' : valley S k lo = 0 := max_eq_left (le_of_not_ge hv)
    have hxe : x = 0 := le_antisymm (hx.2.trans_eq hv') hx.1
    have hye : y = 0 := le_antisymm (hy.2.trans_eq hv') hy.1
    rw [hxe,hye]

theorem right_lower_after (S : Shape) {k lo hi : ℝ} (hk : Sector S k)
    {x y : ℝ} (hx : valley S k lo ≤ x) (hxy : x ≤ y) :
    residual S k lo hi x ≤ residual S k lo hi y+(S.b+S.d)/S.a*(y-x) := by
  have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
  have hy0 := hx0.trans hxy
  have hq : 0 < S.d/S.a+k := add_pos (div_pos S.hd S.ha) (sector_pos S hk)
  have rawx := (le_max_right _ _).trans hx
  have hbx := (div_le_iff₀ hq).mp rawx
  have hz (t : ℝ) (ht0 : 0 ≤ t) (hxt : x ≤ t) : capProfile S S.d (-k) lo t = 0 := by
    unfold capProfile
    rw [tent_right S ht0]
    apply max_eq_left
    apply (min_le_right _ _).trans
    have hmul := mul_le_mul_of_nonneg_right hxt hq.le
    simp only [div_eq_mul_inv] at hbx hmul ⊢
    nlinarith only [hbx,hmul]
  unfold CrossedQuadrilateralSectionProfile.residual
  rw [hz x hx0 le_rfl,hz y hy0 hxy,add_zero,add_zero]
  unfold capProfile
  rw [tent_right S hx0,tent_right S hy0]
  have hδ : 0 ≤ (S.b+S.d)/S.a*(y-x) :=
    mul_nonneg (div_pos (add_pos S.hb S.hd) S.ha).le (sub_nonneg.mpr hxy)
  apply max_increment hδ
  apply min_increment
  · simp only [div_eq_mul_inv]
    nlinarith only []
  · have hp := mul_nonneg (sub_nonneg.mpr hk.1) (sub_nonneg.mpr hxy)
    simp only [div_eq_mul_inv] at hp hδ ⊢
    nlinarith only [hp,hδ]

/-- Flattening the profile after its valley gives a globally continuous
unimodal extension of the entire region before that valley. -/
theorem truncated_unimodal (S : Shape) {k lo hi : ℝ} (hk : Sector S k) (ho : lo ≤ hi) :
    Continuous (fun x => residual S k lo hi (min x (valley S k lo))) ∧
    MonotoneOn (fun x => residual S k lo hi (min x (valley S k lo))) (Iic 0) ∧
    AntitoneOn (fun x => residual S k lo hi (min x (valley S k lo))) (Ici 0) := by
  have hv : 0 ≤ valley S k lo := le_max_left _ _
  refine ⟨(continuous_residual S k lo hi).comp (by fun_prop),?_,?_⟩
  · intro x hx y hy hxy
    dsimp only
    rw [min_eq_left (hx.trans hv),min_eq_left (hy.trans hv)]
    exact left_monotone S hk lo hi hx hy hxy
  · intro x hx y hy hxy
    exact antitone_before_valley S hk ho ⟨le_min hx hv,min_le_right _ _⟩
      ⟨le_min hy hv,min_le_right _ _⟩ (min_le_min_right _ hxy)

end Quant.CrossedQuadrilateralAdjacentProfile

/-- info: 'Quant.CrossedQuadrilateralAdjacentProfile.upper_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAdjacentProfile.upper_slope
