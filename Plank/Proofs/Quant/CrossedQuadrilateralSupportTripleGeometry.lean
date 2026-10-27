/- Boundary obstruction after two calibrated crossed bands are contracted. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTwoPlankFamilies

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupportTripleGeometry
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralSupportGeometry
open Plank.Convex.DeficientHeightTilt

/-- The support-contraction obstruction can avoid a positive transverse band
as well. The point lies on one of the two edges through the transverse vertex. -/
theorem apex_obstruction {K : Set Point} (hK : Convex ℝ K)
    (F G B L : Point →ᵃ[ℝ] ℝ) (a b z : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hz : z ∈ K)
    (hFa : F a = 1) (hFb : 0 ≤ F b)
    (hGa : G a = 1) (hGb : G b = 0)
    (hBa : B a = 0) (hBb : B b = 0) (hBz : B z = 1)
    (α r s t : ℝ) (hα : 0 < α) (hα1 : α < 1) (hGz : G z = α)
    (hFz : α+(1-α)*F b ≤ F z)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hR : r+s+t < 1)
    (hLa : L a < 1) (hLb : L b = 1) (hLz : L z = 1)
    (hL : ∀ x ∈ K, L x ≤ 1) :
    ∃ x ∈ K, r < F x ∧ G x < r+(1-r-s)*α ∧ t < B x ∧
      x ∉ AffineMap.homothety a (1-r) '' K := by
  let lo := r+(1-r-s)*α
  let lower := max r (t*α)
  let upper := min lo (1-t*(1-α))
  have hq : 0 < 1-r-s := by linarith only [hR,ht]
  have hlo : r < lo := by dsimp [lo]; linarith only [mul_pos hq hα]
  have htlo : t*α < lo := by
    have hh := mul_pos (by linarith only [hR] : 0 < 1-r-s-t) hα
    dsimp [lo]; nlinarith only [hh,hr]
  have hrcap : r < 1-t*(1-α) := by
    have hh := mul_pos ht hα
    nlinarith only [hR,hs,hh]
  have htcap : t*α < 1-t*(1-α) := by nlinarith only [hR,hr,hs]
  have hlu : lower < upper := max_lt (lt_min hlo hrcap) (lt_min htlo htcap)
  let v := (lower+upper)/2
  have hlv : lower < v := by dsimp [v]; linarith only [hlu]
  have hvu : v < upper := by dsimp [v]; linarith only [hlu]
  have hv : r < v := (le_max_left r (t*α)).trans_lt hlv
  have htv : t*α < v := (le_max_right r (t*α)).trans_lt hlv
  have hvlo : v < lo := hvu.trans_le (min_le_left _ _)
  have hvcap : v < 1-t*(1-α) := hvu.trans_le (min_le_right _ _)
  have hr1 : r < 1 := by linarith only [hR,hs,ht]
  have hlo1 : lo < 1 := by
    have hh := mul_lt_mul_of_pos_left hα1 hq
    dsimp [lo]; nlinarith only [hh,hs]
  have hvr : v < r+(1-r)*α := by
    have hh := mul_pos hs hα
    dsimp [lo] at hvlo
    nlinarith only [hvlo,hh]
  have hzt : α ≤ F z := by
    have hh := mul_nonneg (sub_pos.mpr hα1).le hFb
    linarith only [hFz,hh]
  by_cases hva : v ≤ α
  · let u := v/α
    have hu0 : 0 ≤ u := div_nonneg (hr.le.trans hv.le) hα.le
    have hu1 : u ≤ 1 := (div_le_one hα).mpr hva
    let x := b+u • (z-b)
    have hx : x ∈ K := hK.add_smul_sub_mem hb hz ⟨hu0,hu1⟩
    have hGx : G x = v := by
      dsimp [x]; rw [ray_eval,hGb,hGz]; dsimp [u]
      field_simp
      ring
    have hFx : v ≤ F x := by
      have hh := mul_le_mul_of_nonneg_left hzt hu0
      have hh' := mul_nonneg (sub_nonneg.mpr hu1) hFb
      have hue : u*α = v := div_mul_cancel₀ _ hα.ne'
      dsimp [x]; rw [ray_eval]
      nlinarith only [hh,hh',hue]
    have hBx : t < B x := by
      dsimp [x]; rw [ray_eval,hBb,hBz]
      simpa only [sub_zero,mul_one,zero_add] using (lt_div_iff₀ hα).mpr htv
    have hLx : L x = 1 := by dsimp [x]; rw [ray_eval,hLb,hLz]; ring
    refine ⟨x,hx,hv.trans_le hFx,hGx ▸ hvlo,hBx,?_⟩
    intro hmem
    have hh := homothety_support L a hr1.le hL hmem
    rw [hLx] at hh
    have hh' := mul_pos hr (sub_pos.mpr hLa)
    nlinarith only [hh,hh']
  · let u := (v-α)/(1-α)
    have hav : α < v := lt_of_not_ge hva
    have hu0 : 0 ≤ u := div_nonneg (sub_pos.mpr hav).le (sub_pos.mpr hα1).le
    have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr hα1)).mpr (by linarith only [hvlo,hlo1])
    have hur : u < r := (div_lt_iff₀ (sub_pos.mpr hα1)).mpr (by nlinarith only [hvr])
    let x := z+u • (a-z)
    have hx : x ∈ K := hK.add_smul_sub_mem hz ha ⟨hu0,hu1⟩
    have hue : u*(1-α) = v-α := div_mul_cancel₀ _ (sub_pos.mpr hα1).ne'
    have hGx : G x = v := by dsimp [x]; rw [ray_eval,hGz,hGa]; linarith only [hue]
    have hFx : v ≤ F x := by
      have hh := mul_le_mul_of_nonneg_left hzt (sub_nonneg.mpr hu1)
      dsimp [x]; rw [ray_eval,hFa]
      nlinarith only [hh,hue]
    have hBx : t < B x := by
      have hh : t < 1-u := (_root_.mul_lt_mul_iff_of_pos_right (sub_pos.mpr hα1)).mp
        (by nlinarith only [hvcap,hue])
      dsimp [x]; rw [ray_eval,hBz,hBa]
      linarith only [hh]
    have hLx : L x = 1+u*(L a-1) := by dsimp [x]; rw [ray_eval,hLz]
    refine ⟨x,hx,hv.trans_le hFx,hGx ▸ hvlo,hBx,?_⟩
    intro hmem
    have hh := homothety_support L a hr1.le hL hmem
    rw [hLx] at hh
    have hh' := mul_pos (sub_pos.mpr hur) (sub_pos.mpr hLa)
    nlinarith only [hh,hh']

def yBand (S : Shape) (a : Point) (r t : ℝ) : Set Point :=
  {x | r*a.2-t*S.d ≤ x.2 ∧ x.2 ≤ r*a.2+t*S.b}

theorem yBand_bound (S : Shape) (i j : Bool) (r t : ℝ) {x : Point}
    (hx : x ∈ yBand S (S.X i,0) r t) : x.2/S.Y j ≤ t := by
  change r*0-t*S.d ≤ x.2 ∧ x.2 ≤ r*0+t*S.b at hx
  cases j
  · change x.2/(-S.d) ≤ t
    apply (div_le_iff_of_neg (neg_neg_of_pos S.hd)).mpr
    linarith only [hx.1]
  · change x.2/S.b ≤ t
    apply (div_le_iff₀ S.hb).mpr
    linarith only [hx.2]

theorem x_apex (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (i : Bool)
    (hFa : F (S.X i,0) = 1) (hF : ∀ x ∈ S.body, 0 ≤ F x)
    (r s t : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hR : r+s+t < 1) :
    ¬S.body ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band S (S.X i,0) r s ∪
      yBand S (S.X i,0) r t) ∪ AffineMap.homothety (S.X i,0) (1-r) '' S.body := by
  obtain ⟨j,hj⟩ := some_y_ge S F
  have hm := zero_x_mix S F i
  rw [hFa,mul_one] at hm
  let B := direction (0,(S.Y j)⁻¹)
  have hB (x : Point) : B x = x.2/S.Y j := by simp [B,dot,div_eq_mul_inv,mul_comm]
  obtain ⟨x,hx,hFx,hGx,hBx,hHx⟩ := apex_obstruction (convex_body S) F (xLevel S i) B
    (edge S (!i) j) (S.X i,0) (S.X (!i),0) (0,S.Y j)
    (vertexX_mem S i) (vertexX_mem S (!i)) (vertexY_mem S j) hFa
    (hF _ (vertexX_mem S (!i))) (level_vertex S i) (level_opposite S i)
    (by rw [hB]; simp) (by rw [hB]; simp) (by rw [hB]; simp [S.Y_ne])
    (xLevel S i 0) r s t (level_pos S i) (level_lt_one S i) (level_y S i j)
    (by rwa [← hm]) hr hs ht hR (edge_x_opposite S i j) (edge_x S (!i) j)
    (edge_y S (!i) j) (edge_bound S (!i) j)
  intro hcover
  rcases hcover hx with ((hf | hg) | hb) | hh
  · exact (not_lt_of_ge hf.2) hFx
  · exact (not_lt_of_ge (band_apex_lower S i r s hg)) hGx
  · rw [hB] at hBx
    exact (not_lt_of_ge (yBand_bound S i j r t hb)) hBx
  · exact hHx hh

theorem map_homothety (T : Point ≃ᵃ[ℝ] Point) (a x : Point) (q : ℝ) :
    T (AffineMap.homothety a q x) = AffineMap.homothety (T a) q (T x) := by
  have hv : T.toAffineMap.linear (x-a) = T x-T a := T.toAffineMap.linearMap_vsub x a
  simpa only [AffineEquiv.coe_toAffineMap,AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,map_smul,
    hv] using T.toAffineMap.map_vadd a (q • (x-a))

theorem image_homothety (T : Point ≃ᵃ[ℝ] Point) (a : Point) (q : ℝ) (K : Set Point) :
    T '' (AffineMap.homothety a q '' K) = AffineMap.homothety (T a) q '' (T '' K) := by
  rw [Set.image_image,Set.image_image]
  congr 1
  funext x
  exact map_homothety T a x q

theorem swap_xBand (S : Shape) (a : Point) (r s : ℝ) :
    CrossedQuadrilateralSupport.swap '' band S a r s =
      yBand (CrossedQuadrilateralSupport.transpose S) (CrossedQuadrilateralSupport.swap a) r s := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨(x.2,x.1),hx,rfl⟩

theorem swap_yBand (S : Shape) (a : Point) (r t : ℝ) :
    CrossedQuadrilateralSupport.swap '' yBand S a r t =
      band (CrossedQuadrilateralSupport.transpose S) (CrossedQuadrilateralSupport.swap a) r t := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨(x.2,x.1),hx,rfl⟩

theorem y_apex (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (j : Bool)
    (hFa : F (0,S.Y j) = 1) (hF : ∀ x ∈ S.body, 0 ≤ F x)
    (r s t : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hR : r+s+t < 1) :
    ¬S.body ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band S (0,S.Y j) r s ∪
      yBand S (0,S.Y j) r t) ∪ AffineMap.homothety (0,S.Y j) (1-r) '' S.body := by
  let T := CrossedQuadrilateralSupport.swap
  let F' := CrossedQuadrilateralAffine.pull T F
  have hF' : ∀ x ∈ (CrossedQuadrilateralSupport.transpose S).body, 0 ≤ F' x := by
    intro x hx
    rw [← CrossedQuadrilateralSupport.swap_body] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa [F',T] using hF y hy
  intro hcover
  have hh := Set.image_mono (f := T) hcover
  simp only [Set.image_union,CrossedQuadrilateralSupport.swap_body,
    CrossedQuadrilateralSupport.image_band,swap_xBand,swap_yBand,image_homothety,T] at hh
  apply x_apex (CrossedQuadrilateralSupport.transpose S) F' j
    (by change F (0,S.Y j) = 1; exact hFa)
    hF' r t s hr ht hs (by linarith only [hR])
  convert hh using 1
  ext x
  change ((0 ≤ F' x ∧ F' x ≤ r ∨ x ∈ _ ) ∨ x ∈ _) ∨ x ∈ _ ↔
    ((0 ≤ F' x ∧ F' x ≤ r ∨ x ∈ _) ∨ x ∈ _) ∨ x ∈ _
  tauto

/-- No positive support band can complete the support-induction cover after
two positive calibrated diagonal bands, whichever vertex realizes the maximum. -/
theorem no_cover (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a : Point)
    (ha : a ∈ S.vertices) (hFa : F a = 1) (hF : ∀ x ∈ S.body, 0 ≤ F x)
    (r s t : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hR : r+s+t < 1) :
    ¬S.body ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band S a r s ∪ yBand S a r t) ∪
      AffineMap.homothety a (1-r) '' S.body := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact x_apex S F true hFa hF r s t hr hs ht hR
  · exact y_apex S F true hFa hF r s t hr hs ht hR
  · exact x_apex S F false hFa hF r s t hr hs ht hR
  · exact y_apex S F false hFa hF r s t hr hs ht hR

end Quant.CrossedQuadrilateralSupportTripleGeometry

/-- info: 'Quant.CrossedQuadrilateralSupportTripleGeometry.no_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupportTripleGeometry.no_cover
