/- Support-plank exclusion on every genuine quadrilateral, in original coordinates. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupport
public import Plank.Proofs.Quant.PlanarTwoPlank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupportOriginal
open Plank
open Set MeasureTheory PlanarQuantitative
open Plank.Convex.DeficientHeightTilt

def productForm (f : Point →ᵃ[ℝ] ℝ) : CrossedQuadrilateralAttainment.Point →ᵃ[ℝ] ℝ :=
  f.comp ParallelProductPlane.coordinates.symm.toLinearEquiv.toAffineEquiv.toAffineMap

theorem product_pull (f : Point →ᵃ[ℝ] ℝ) :
    ParallelProductPlane.pullForm (productForm f) = f := by
  ext x
  simp [productForm,ParallelProductPlane.pullForm]

theorem model_not_equality (S : CrossedQuadrilateralAttainment.Shape)
    (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ CrossedQuadrilateralFormDirections.body S)
    (hb : b ∈ CrossedQuadrilateralFormDirections.body S) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ CrossedQuadrilateralFormDirections.body S, 0 ≤ F x ∧ F x ≤ 1)
    (r lo hi : ℝ) (hr : 0 < r) (ho : lo < hi)
    (hW : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) G)
    (hR : r+(hi-lo)/rangeWidth (CrossedQuadrilateralFormDirections.body S) G < 1) :
    (volume (CrossedQuadrilateralFormDirections.body S \
      ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal ≠
      (1-r-(hi-lo)/rangeWidth (CrossedQuadrilateralFormDirections.body S) G)^2*
        (volume (CrossedQuadrilateralFormDirections.body S)).toReal := by
  let C := ParallelProductPlane.coordinates
  have hw : rangeWidth S.body (productForm G) = rangeWidth (CrossedQuadrilateralFormDirections.body S) G := by
    rw [← CrossedQuadrilateralDirections.width_preimage,product_pull]
  have hg : volume (CrossedQuadrilateralFormDirections.body S \
      ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi})) =
      volume (S.body \ ({x | 0 ≤ productForm F x ∧ productForm F x ≤ r} ∪
        {x | lo ≤ productForm G x ∧ productForm G x ≤ hi})) := by
    rw [← ParallelProductPlane.volume_preimage]
    congr 1
    ext x
    change (C x ∈ S.body ∧ ¬(0 ≤ F x ∧ F x ≤ r ∨ lo ≤ G x ∧ G x ≤ hi)) ↔
      (C x ∈ S.body ∧ ¬(0 ≤ F (C.symm (C x)) ∧ F (C.symm (C x)) ≤ r ∨
        lo ≤ G (C.symm (C x)) ∧ G (C.symm (C x)) ≤ hi))
    rw [C.symm_apply_apply]
  intro he
  apply CrossedQuadrilateralSupport.not_equality S (productForm F) (productForm G) (C a) (C b)
    ha hb (by simpa [productForm,C] using hFa) (by simpa [productForm,C] using hFb)
    (fun x hx => by simpa [productForm,C] using hF (C.symm x) (by simpa [C] using hx))
    r lo hi hr ho (by rwa [hw]) (by rwa [hw])
  rwa [← hg,hw,← ParallelProductPlane.volume_preimage]

theorem genuine_compact {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K) : IsCompact K := by
  obtain ⟨v,_,rfl,_⟩ := hG
  exact (Set.finite_range v).isCompact_convexHull (𝕜 := ℝ)

theorem genuine_convex {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K) : Convex ℝ K := by
  obtain ⟨v,_,rfl,_⟩ := hG
  exact convex_convexHull ℝ _

/-- The support exclusion needs no supplied diagonal chart or ordering of vertices. -/
theorem normalized_not_equality {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (F G : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ K, 0 ≤ F x ∧ F x ≤ 1)
    (r lo hi : ℝ) (hr : 0 < r) (ho : lo < hi) (hW : 0 < rangeWidth K G)
    (hR : r+(hi-lo)/rangeWidth K G < 1) :
    (volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}))).toReal ≠
      (1-r-(hi-lo)/rangeWidth K G)^2*(volume K).toReal := by
  obtain ⟨S,T,rfl⟩ := CrossedQuadrilateralGenuine.exists_model hG hV
  let A := CrossedQuadrilateralFormDirections.body S
  let f := CrossedQuadrilateralImageStrata.pre T F
  let g := CrossedQuadrilateralImageStrata.pre T G
  have hw : rangeWidth A g = rangeWidth (T '' A) G := CrossedQuadrilateralImageStrata.width_pre T A G
  have hgap : T '' (A \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi})) =
      (T '' A) \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | lo ≤ G x ∧ G x ≤ hi}) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_image_of_mem T hy.1,hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hnot⟩
      exact ⟨y,⟨hy,hnot⟩,rfl⟩
  have hpre {x : Point} (hx : x ∈ T '' A) : T.symm x ∈ A := by
    obtain ⟨y,hy,rfl⟩ := hx
    simpa using hy
  intro he
  apply model_not_equality S f g (T.symm a) (T.symm b) (hpre ha) (hpre hb)
    (by simpa [f] using hFa) (by simpa [f] using hFb)
    (fun x hx => hF (T x) (mem_image_of_mem T hx)) r lo hi hr ho (by rwa [hw]) (by rwa [hw])
  change (volume (A \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal = _
  rw [hw]
  change (volume ((T '' A) \ _)).toReal = _ at he
  rw [← hgap,CrossedQuadrilateralImageStrata.area_image,CrossedQuadrilateralImageStrata.area_image] at he
  apply (mul_left_cancel₀ (CrossedQuadrilateralImageStrata.factor_pos T).ne')
  nlinarith only [he]

theorem lower_support_not_equality {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f g : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ lo hi : ℝ) (hbase : f b = lo₀) (horder : lo₀ < hi₀) (ho : lo < hi)
    (hWf : 0 < rangeWidth K f) (hWg : 0 < rangeWidth K g)
    (hR : (hi₀-lo₀)/rangeWidth K f+(hi-lo)/rangeWidth K g < 1) :
    (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal ≠
      (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g)^2*(volume K).toReal := by
  let F : Point →ᵃ[ℝ] ℝ := (rangeWidth K f)⁻¹ • (f-AffineMap.const ℝ Point lo₀)
  let r := (hi₀-lo₀)/rangeWidth K f
  have hFeval (x) : F x = (f x-lo₀)/rangeWidth K f := by simp [F,div_eq_mul_inv,mul_comm]
  have hw : rangeWidth K f = f a-lo₀ := by
    have hh : rangeWidth K f = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
    rwa [hbase] at hh
  have hFa : F a = 1 := by rw [hFeval,← hw,div_self hWf.ne']
  have hFb : F b = 0 := by rw [hFeval,hbase,sub_self,zero_div]
  have hF (x) (hx : x ∈ K) : 0 ≤ F x ∧ F x ≤ 1 := by
    rw [hFeval]
    refine ⟨div_nonneg (sub_nonneg.mpr (by rw [← hbase]; exact hmin x hx)) hWf.le,?_⟩
    rw [div_le_one hWf,hw]
    exact sub_le_sub_right (hmax x hx) _
  have hband : {x | 0 ≤ F x ∧ F x ≤ r} = {x | lo₀ ≤ f x ∧ f x ≤ hi₀} := by
    ext x
    change (0 ≤ F x ∧ F x ≤ r) ↔ _
    rw [hFeval]
    dsimp only [r]
    rw [div_le_div_iff_of_pos_right hWf]
    simp only [le_div_iff₀ hWf,zero_mul,sub_nonneg,sub_le_sub_iff_right,mem_ofPred_eq]
  have hh := normalized_not_equality hG hV F g a b ha hb hFa hFb hF r lo hi
    (div_pos (sub_pos.mpr horder) hWf) ho hWg hR
  rwa [hband] at hh

/-- For two positive physical planks, reaching either support is strictly
above the square bound on every genuine quadrilateral. No overlap or
direction hypothesis is present. -/
theorem support_strict {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f g : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ lo hi : ℝ) (hface : f b = lo₀ ∨ f a = hi₀) (horder : lo₀ < hi₀) (ho : lo < hi)
    (hWf : 0 < rangeWidth K f) (hWg : 0 < rangeWidth K g)
    (hR : (hi₀-lo₀)/rangeWidth K f+(hi-lo)/rangeWidth K g < 1) :
    (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g)^2*(volume K).toReal <
      (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal := by
  have hneq : (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal ≠
      (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g)^2*(volume K).toReal := by
    rcases hface with hface | hface
    · exact lower_support_not_equality hG hV f g a b ha hb hmax hmin lo₀ hi₀ lo hi hface horder ho hWf hWg hR
    · have hw : rangeWidth K (-f) = rangeWidth K f :=
        Body.width_neg (genuine_compact hG) ⟨a,ha⟩ (PlanarGapCells.continuous_form f)
      have hband : {x | -hi₀ ≤ (-f) x ∧ (-f) x ≤ -lo₀} = {x | lo₀ ≤ f x ∧ f x ≤ hi₀} := by
        ext x
        change (-hi₀ ≤ -f x ∧ -f x ≤ -lo₀) ↔ (lo₀ ≤ f x ∧ f x ≤ hi₀)
        constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
      have hh := lower_support_not_equality hG hV (-f) g b a hb ha
        (fun x hx => by simpa using neg_le_neg (hmin x hx))
        (fun x hx => by simpa using neg_le_neg (hmax x hx)) (-hi₀) (-lo₀) lo hi
        (by simpa using congrArg Neg.neg hface) (neg_lt_neg horder) ho (by rwa [hw]) hWg
        (by simpa only [hw,neg_sub_neg] using hR)
      simpa only [hband,hw,neg_sub_neg] using hh
  have hbound := PlanarTwoPlank.sharpPlanarBound_two K (genuine_compact hG) (genuine_convex hG)
    ⟨a,ha⟩ ![f,g] ![lo₀,lo] ![hi₀,hi]
    (by intro i; fin_cases i; exact horder.le; exact ho.le)
    (by intro i; fin_cases i; exact hWf; exact hWg)
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    sub_add_eq_sub_sub] at hbound
  rw [max_eq_right (by linarith only [hR] : 0 ≤ 1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g)] at hbound
  have hu : (⋃ i : Fin 2, {x | ![lo₀,lo] i ≤ (![f,g] i) x ∧ (![f,g] i) x ≤ ![hi₀,hi] i}) =
      ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}) := by
    ext x
    simp only [mem_iUnion,mem_union,mem_ofPred_eq,Fin.exists_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hu] at hbound
  exact lt_of_le_of_ne hbound hneq.symm

end Quant.CrossedQuadrilateralSupportOriginal

/-- info: 'Quant.CrossedQuadrilateralSupportOriginal.support_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupportOriginal.support_strict
