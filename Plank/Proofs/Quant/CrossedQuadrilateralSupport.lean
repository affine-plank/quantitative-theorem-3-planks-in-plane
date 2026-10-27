/- Actual support-plank equality is incompatible with a genuine quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportGeometry
public import Plank.Proofs.Quant.PlanarSupportPairReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupport
open Set MeasureTheory
open CrossedQuadrilateralAttainment
open Plank.Convex.DeficientHeightTilt

theorem max_vertex (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a : Point)
    (ha : a ∈ S.body) (hFa : F a = 1) (hF : ∀ x ∈ S.body, F x ≤ 1) :
    ∃ v ∈ S.vertices, F v = 1 := by
  classical
  by_contra hn
  push Not at hn
  have hh : S.body ⊆ F ⁻¹' Iio 1 := by
    apply convexHull_min _ ((convex_Iio (1 : ℝ)).affine_preimage F)
    intro v hv
    exact lt_of_le_of_ne (hF v (subset_convexHull ℝ S.vertices hv)) (hn v hv)
  have hh' : F a < 1 := hh ha
  linarith only [hh',hFa]

/-- The existing actual-area support reduction transported to the product plane. -/
theorem reduced {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ K, 0 ≤ F x ∧ F x ≤ 1)
    (r lo hi : ℝ) (hr : 0 ≤ r) (ho : lo < hi) (hW : 0 < rangeWidth K G)
    (hR : r+(hi-lo)/rangeWidth K G < 1)
    (he : (volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal =
      (1-r-(hi-lo)/rangeWidth K G)^2*(volume K).toReal) :
    (volume (K \ {x | (lo-r*G a)/(1-r) ≤ G x ∧ G x ≤ (hi-r*G a)/(1-r)})).toReal =
      (1-((hi-r*G a)/(1-r)-(lo-r*G a)/(1-r))/rangeWidth K G)^2*(volume K).toReal ∧
    K ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}) ∪
      AffineMap.homothety a (1-r) '' K := by
  let C := ParallelProductPlane.coordinates
  let A := C ⁻¹' K
  let f := ParallelProductPlane.pullForm F
  let g := ParallelProductPlane.pullForm G
  have hwidth : rangeWidth (ParallelProductPlane.coordinates ⁻¹' K) g = rangeWidth K G :=
    CrossedQuadrilateralDirections.width_preimage K G
  have hgap : volume (A \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi})) =
      volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi})) := by
    rw [← ParallelProductPlane.volume_preimage]
    congr 1
  have hGa : g (C.symm a) = G a := by simp [g,C]
  obtain ⟨hp,hcover⟩ := (Plank.PlanarSupportPairReduction.equality_iff_reduced
    (ParallelProductPlane.compact_preimage hK) (hc.linear_preimage C.toLinearMap)
    (by rw [ParallelProductPlane.volume_preimage]; exact hV) f g (C.symm a) (C.symm b)
    (by simpa [A,C] using ha) (by simpa [A,C] using hb) (by simpa [f,C] using hFa)
    (by simpa [f,C] using hFb) (fun x hx => hF (C x) hx) r lo hi hr ho
    (by rw [hwidth]; exact hW) (by rw [hwidth]; exact hR)).mp (by
      rw [hgap,hwidth,ParallelProductPlane.volume_preimage]; exact he)
  simp only [Plank.PlanarSupportPairReduction.pulledEndpoint,hGa,hwidth] at hp
  have hgap' : volume (A \ {x | (lo-r*G a)/(1-r) ≤ g x ∧ g x ≤ (hi-r*G a)/(1-r)}) =
      volume (K \ {x | (lo-r*G a)/(1-r) ≤ G x ∧ G x ≤ (hi-r*G a)/(1-r)}) := by
    rw [← ParallelProductPlane.volume_preimage]
    congr 1
  rw [hgap',ParallelProductPlane.volume_preimage] at hp
  refine ⟨hp,?_⟩
  intro x hx
  have hx' : C.symm x ∈ A := by simpa [A] using hx
  rcases hcover hx' with (hf | hg) | hh
  · exact Or.inl (Or.inl (by simpa [f,C] using hf))
  · exact Or.inl (Or.inr (by simpa [g,C] using hg))
  · obtain ⟨y,hy,he⟩ := hh
    refine Or.inr ⟨C y,hy,?_⟩
    have hh := congrArg C he
    simpa only [AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,map_add,map_sub,map_smul,
      C.apply_symm_apply] using hh

theorem single_vertical_calibrated (S : Shape) (l u : ℝ) (ho : l < u)
    (hR : (u-l)/(S.a+S.c) < 1)
    (he : (volume (S.body \ {x | l ≤ x.1 ∧ x.1 ≤ u})).toReal =
      (1-(u-l)/(S.a+S.c))^2*(volume S.body).toReal) :
    l = -S.c*((u-l)/(S.a+S.c)) ∧ u = S.a*((u-l)/(S.a+S.c)) := by
  have hnull : volume (CrossedQuadrilateralPlacement.band true 0 0) = 0 := by
    have hh : CrossedQuadrilateralPlacement.band true 0 0 = {z : Point | dot (0,1) z = 0} := by
      ext z
      simp only [CrossedQuadrilateralPlacement.band,CrossedQuadrilateralPlacement.coord,
        if_true,mem_ofPred_eq,dot,zero_mul,one_mul,zero_add]
      exact ⟨fun h => le_antisymm h.2 h.1,fun h => by rw [h]; exact ⟨le_rfl,le_rfl⟩⟩
    rw [hh]
    exact volume_line (by norm_num) 0
  have hvol : volume (S.body \ (CrossedQuadrilateralPlacement.band false l u ∪
      CrossedQuadrilateralPlacement.band true 0 0)) = volume (S.body \ {x | l ≤ x.1 ∧ x.1 ≤ u}) := by
    rw [← Set.sdiff_sdiff,measure_sdiff_null hnull]
    rfl
  have hh := (CrossedQuadrilateralPlacement.arbitrary_placement_equality_iff S l u 0 0 ho.le le_rfl
    (by simpa using hR)).mp (by simpa only [hvol,sub_self,zero_div,sub_zero] using he)
  have hbal : u/S.a = -l/S.c := hh.1.resolve_left (ne_of_gt ho)
  have hrel := (div_eq_div_iff S.ha.ne' S.hc.ne').mp hbal
  constructor <;> field_simp [(add_pos S.ha S.hc).ne'] <;> nlinarith only [hrel]

/-- A positive support plank and an arbitrary positive vertical plank
cannot attain equality on this quadrilateral. The second endpoints are
unrestricted, and the ratio uses its full actual directional width. -/
theorem vertical_not_equality (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (r lo hi : ℝ) (hr : 0 < r) (ho : lo < hi)
    (hR : r+(hi-lo)/(S.a+S.c) < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ x.1 ∧ x.1 ≤ hi}))).toReal ≠
      (1-r-(hi-lo)/(S.a+S.c))^2*(volume S.body).toReal := by
  intro he
  obtain ⟨v,hv,hFv⟩ := max_vertex S F a ha hFa (fun x hx => (hF x hx).2)
  have hvm : v ∈ S.body := subset_convexHull ℝ S.vertices hv
  let s := (hi-lo)/(S.a+S.c)
  have hs : 0 < s := div_pos (sub_pos.mpr ho) (add_pos S.ha S.hc)
  have hq : 0 < 1-r := by change r+s < 1 at hR; linarith only [hR,hs]
  obtain ⟨hp,hcover⟩ := reduced (compact_body S) (convex_body S) (area_body_pos S)
    F (direction (1,0)) v b hvm hb hFv hFb hF r lo hi hr.le ho
    (by rw [(coordinate_widths S).1]; exact add_pos S.ha S.hc)
    (by rwa [(coordinate_widths S).1]) (by simpa [dot,(coordinate_widths S).1] using he)
  simp only [direction_apply,dot,one_mul,zero_mul,add_zero,(coordinate_widths S).1] at hp hcover
  have hw : ((hi-r*v.1)/(1-r)-(lo-r*v.1)/(1-r))/(S.a+S.c) = s/(1-r) := by dsimp [s]; ring
  have horder : (lo-r*v.1)/(1-r) < (hi-r*v.1)/(1-r) :=
    (div_lt_div_iff_of_pos_right hq).mpr (by linarith only [ho])
  have hsmall : ((hi-r*v.1)/(1-r)-(lo-r*v.1)/(1-r))/(S.a+S.c) < 1 := by
    rw [hw]
    apply (div_lt_one hq).mpr
    change r+s < 1 at hR
    linarith only [hR]
  obtain ⟨hl,hh⟩ := single_vertical_calibrated S _ _ horder hsmall hp
  rw [hw] at hl hh
  have hlo : lo = r*v.1-s*S.c := by
    have heq := congrArg (fun x : ℝ => x*(1-r)) hl
    field_simp [hq.ne'] at heq
    nlinarith only [heq]
  have hhi : hi = r*v.1+s*S.a := by
    have heq := congrArg (fun x : ℝ => x*(1-r)) hh
    field_simp [hq.ne'] at heq
    nlinarith only [heq]
  apply CrossedQuadrilateralSupportGeometry.no_cover S F v hv hFv
    (fun x hx => (hF x hx).1) r s hr hs hR
  simpa only [hlo,hhi,CrossedQuadrilateralSupportGeometry.band] using hcover

theorem eval_linear (G : Point →ᵃ[ℝ] ℝ) (x : Point) :
    G x = G.linear (1,0)*x.1+G.linear (0,1)*x.2+G 0 := by
  have hx : x = x.1 • ((1,0) : Point)+x.2 • ((0,1) : Point) := by ext <;> simp
  have hl : G.linear x = x.1*G.linear (1,0)+x.2*G.linear (0,1) := by
    conv_lhs => rw [hx]
    simp only [map_add,map_smul,smul_eq_mul]
  have hh := G.map_vadd 0 x
  simpa only [vadd_eq_add,add_zero,hl,mul_comm] using hh

theorem nonzero_coefficient (S : Shape) (G : Point →ᵃ[ℝ] ℝ)
    (hW : 0 < rangeWidth S.body G) : G.linear (1,0) ≠ 0 ∨ G.linear (0,1) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hconst (x : Point) : G x = G 0 := by rw [eval_linear,hn.1,hn.2]; ring
  have hw : rangeWidth S.body G = G 0-G 0 := Plank.Body.width_eq_of_realisers (zero_mem S)
    (zero_mem S) (fun x _ => (hconst x).le) (fun x _ => (hconst x).ge)
  rw [hw,sub_self] at hW
  exact (lt_irrefl 0) hW

theorem vertical_affine_pos (S : Shape) (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (k c : ℝ) (hk : 0 < k) (hG : ∀ x, G x = k*x.1+c)
    (r lo hi : ℝ) (hr : 0 < r) (ho : lo < hi)
    (hR : r+(hi-lo)/rangeWidth S.body G < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal ≠
      (1-r-(hi-lo)/rangeWidth S.body G)^2*(volume S.body).toReal := by
  have hw : rangeWidth S.body G = k*(S.a+S.c) := by
    have hh := Plank.Body.width_eq_of_realisers (f := G) (vertexX_mem S true) (vertexX_mem S false)
      (fun x hx => by
        rw [hG,hG]
        change k*x.1+c ≤ k*S.a+c
        nlinarith only [mul_le_mul_of_nonneg_left (coordinate_box S hx).1.2 hk.le])
      (fun x hx => by
        rw [hG,hG]
        change k*(-S.c)+c ≤ k*x.1+c
        nlinarith only [mul_le_mul_of_nonneg_left (coordinate_box S hx).1.1 hk.le])
    change rangeWidth S.body G = G (S.X true,0)-G (S.X false,0) at hh
    rw [hh,hG,hG]
    simp only [Shape.X,if_true,Bool.false_eq_true,if_false]
    ring
  have hw' : (((hi-c)/k)-((lo-c)/k))/(S.a+S.c) = (hi-lo)/rangeWidth S.body G := by
    rw [hw]
    field_simp
    ring
  have hband : {x | lo ≤ G x ∧ G x ≤ hi} = {x : Point | (lo-c)/k ≤ x.1 ∧ x.1 ≤ (hi-c)/k} := by
    ext x
    rw [mem_ofPred_eq,mem_ofPred_eq,hG,div_le_iff₀ hk,le_div_iff₀ hk]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]
  intro he
  apply vertical_not_equality S F a b ha hb hFa hFb hF r ((lo-c)/k) ((hi-c)/k) hr
    ((div_lt_div_iff_of_pos_right hk).mpr (by linarith only [ho])) (by rwa [hw'])
  rwa [hband,← hw'] at he

theorem vertical_affine (S : Shape) (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (k c : ℝ) (hk : k ≠ 0) (hG : ∀ x, G x = k*x.1+c)
    (r lo hi : ℝ) (hr : 0 < r) (ho : lo < hi)
    (hR : r+(hi-lo)/rangeWidth S.body G < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal ≠
      (1-r-(hi-lo)/rangeWidth S.body G)^2*(volume S.body).toReal := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hw : rangeWidth S.body (-G) = rangeWidth S.body G :=
      Plank.Body.width_neg (compact_body S) ⟨0,zero_mem S⟩ G.continuous_of_finiteDimensional
    have hband : {x | -hi ≤ (-G) x ∧ (-G) x ≤ -lo} = {x | lo ≤ G x ∧ G x ≤ hi} := by
      ext x
      change (-hi ≤ -G x ∧ -G x ≤ -lo) ↔ (lo ≤ G x ∧ G x ≤ hi)
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
    have hh := vertical_affine_pos S F (-G) a b ha hb hFa hFb hF (-k) (-c)
      (neg_pos.mpr hk) (fun x => by change -G x = _; rw [hG]; ring) r (-hi) (-lo) hr
      (neg_lt_neg ho) (by rw [hw]; convert hR using 1; ring)
    simpa only [hband,hw,neg_sub_neg] using hh
  · exact vertical_affine_pos S F G a b ha hb hFa hFb hF k c hk hG r lo hi hr ho hR

theorem direction_of_equality (S : Shape) (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (r lo hi : ℝ) (hr : 0 ≤ r) (ho : lo < hi) (hW : 0 < rangeWidth S.body G)
    (hR : r+(hi-lo)/rangeWidth S.body G < 1)
    (he : (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal =
      (1-r-(hi-lo)/rangeWidth S.body G)^2*(volume S.body).toReal) :
    G.linear (1,0) = 0 ∨ G.linear (0,1) = 0 := by
  obtain ⟨hp,_⟩ := reduced (compact_body S) (convex_body S) (area_body_pos S) F G a b
    ha hb hFa hFb hF r lo hi hr ho hW hR he
  have hs := div_pos (sub_pos.mpr ho) hW
  have hq : 0 < 1-r := by linarith only [hs,hR]
  let l := (lo-r*G a)/(1-r)
  let u := (hi-r*G a)/(1-r)
  have hlu : l < u := (div_lt_div_iff_of_pos_right hq).mpr (by linarith only [ho])
  have hw : (u-l)/rangeWidth S.body G = ((hi-lo)/rangeWidth S.body G)/(1-r) := by dsimp [l,u]; ring
  have hsmall : (u-l)/rangeWidth S.body G < 1 := by
    rw [hw]
    exact (div_lt_one hq).mpr (by linarith only [hR])
  let g := ParallelProductPlane.pullForm G
  have hwidth := CrossedQuadrilateralDirections.width_preimage S.body G
  have hgap : volume (CrossedQuadrilateralFormDirections.body S \ {x | l ≤ g x ∧ g x ≤ u}) =
      volume (S.body \ {x | l ≤ G x ∧ G x ≤ u}) := by
    rw [← ParallelProductPlane.volume_preimage]
    congr 1
  have hh := CrossedQuadrilateralFormDirections.one_window_direction S g l u hlu
    (by rw [hwidth]; exact hW) (by rwa [hwidth]) (by
      rw [hgap,hwidth,ParallelProductPlane.volume_preimage]; exact hp)
  exact hh

def transpose (S : Shape) : Shape := ⟨S.b,S.a,S.d,S.c,S.hb,S.ha,S.hd,S.hc⟩
def swap : Point ≃ᵃ[ℝ] Point := (LinearEquiv.prodComm ℝ ℝ ℝ).toAffineEquiv

theorem swap_apply (x : Point) : swap x = (x.2,x.1) := rfl

theorem swap_body (S : Shape) : swap '' S.body = (transpose S).body := by
  rw [CrossedQuadrilateralAffine.image_body]
  apply congrArg (convexHull ℝ)
  ext x
  simp only [swap_apply,transpose,Shape.vertices,mem_insert_iff,mem_singleton_iff]
  tauto

theorem image_band (T : Point ≃ᵃ[ℝ] Point) (G : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) :
    T '' {x | lo ≤ G x ∧ G x ≤ hi} =
      {x | lo ≤ CrossedQuadrilateralAffine.pull T G x ∧ CrossedQuadrilateralAffine.pull T G x ≤ hi} := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [mem_ofPred_eq,CrossedQuadrilateralAffine.pull_apply] using hy
  · intro hx
    exact ⟨T.symm x,hx,T.apply_symm_apply x⟩

/-- A positive support plank cannot participate in two-positive-plank
equality on a genuine quadrilateral, with no direction or overlap restriction
on the second physical plank. -/
theorem not_equality (S : Shape) (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (r lo hi : ℝ) (hr : 0 < r) (ho : lo < hi) (hW : 0 < rangeWidth S.body G)
    (hR : r+(hi-lo)/rangeWidth S.body G < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal ≠
      (1-r-(hi-lo)/rangeWidth S.body G)^2*(volume S.body).toReal := by
  intro he
  rcases direction_of_equality S F G a b ha hb hFa hFb hF r lo hi hr.le ho hW hR he with hx | hy
  · let F' := CrossedQuadrilateralAffine.pull swap F
    let G' := CrossedQuadrilateralAffine.pull swap G
    have hw : rangeWidth (transpose S).body G' = rangeWidth S.body G := by
      rw [← swap_body]
      exact CrossedQuadrilateralAffine.width_pull swap S.body G
    have hmem {x : Point} (hx : x ∈ S.body) : swap x ∈ (transpose S).body := by
      rw [← swap_body]
      exact mem_image_of_mem swap hx
    have hF' : ∀ x ∈ (transpose S).body, 0 ≤ F' x ∧ F' x ≤ 1 := by
      intro x hx
      rw [← swap_body] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      simpa [F'] using hF y hy
    have hk : G.linear (0,1) ≠ 0 := (nonzero_coefficient S G hW).resolve_left (not_ne_iff.mpr hx)
    have hG' (x : Point) : G' x = G.linear (0,1)*x.1+G 0 := by
      change G (x.2,x.1) = _
      rw [eval_linear,hx]
      ring
    have he' := (CrossedQuadrilateralAffine.image_equality_iff swap S.body
      ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi})
      ((1-r-(hi-lo)/rangeWidth S.body G)^2)).mpr he
    rw [swap_body,Set.image_union,image_band,image_band] at he'
    apply vertical_affine (transpose S) F' G' (swap a) (swap b) (hmem ha) (hmem hb)
      (by simpa [F'] using hFa) (by simpa [F'] using hFb) hF'
      (G.linear (0,1)) (G 0) hk hG' r lo hi hr ho (by rwa [hw])
    rwa [hw]
  · have hk : G.linear (1,0) ≠ 0 := (nonzero_coefficient S G hW).resolve_right (not_ne_iff.mpr hy)
    exact vertical_affine S F G a b ha hb hFa hFb hF (G.linear (1,0)) (G 0) hk
      (fun x => by rw [eval_linear,hy]; ring) r lo hi hr ho hR he

end Quant.CrossedQuadrilateralSupport

/-- info: 'Quant.CrossedQuadrilateralSupport.vertical_not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupport.vertical_not_equality

/-- info: 'Quant.CrossedQuadrilateralSupport.not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupport.not_equality
