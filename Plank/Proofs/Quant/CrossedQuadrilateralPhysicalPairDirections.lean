/- Two-plank rigidity in the supplied physical quadrilateral coordinates. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSurvivingDirections
public import Plank.Proofs.Quant.CrossedQuadrilateralPairBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralPhysicalPairDirections
open Set MeasureTheory CrossedQuadrilateralAttainment
open CrossedQuadrilateralFormDirections CrossedQuadrilateralDirections
open Plank.Convex.DeficientHeightTilt
open Plank.PlanarParameterDomain Plank.PlanarQuantitative Plank.PlanarEqualityReductions
open scoped BigOperators

theorem genuine (S : Shape) : CrossedQuadrilateralGenuine.Genuine (body S) := by
  let C := ParallelProductPlane.coordinates
  let v : Fin 4 → ℝ × ℝ := ![(S.a,0),(0,S.b),(-S.c,0),(0,-S.d)]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v,Prod.mk.injEq,S.ha.ne',S.hb.ne',S.hc.ne',S.hd.ne']
    all_goals nlinarith [S.ha,S.hb,S.hc,S.hd]
  have hr : range v = S.vertices := by
    ext z
    simp [v,Shape.vertices]
    tauto
  have he : body S = C.symm '' S.body := by
    ext x
    constructor
    · intro hx
      exact ⟨C x,hx,by simp⟩
    · rintro ⟨y,hy,rfl⟩
      change C (C.symm y) ∈ S.body
      simpa using hy
  refine ⟨fun i => C.symm (v i),C.symm.injective.comp hv,?_,?_⟩
  · rw [he]
    change C.symm.toLinearMap '' convexHull ℝ S.vertices = _
    rw [C.symm.toLinearMap.image_convexHull,← hr]
    congr 1
    exact (Set.range_comp C.symm v).symm
  · intro i
    rw [he,← image_extremePoints C.symm]
    exact mem_image_of_mem C.symm (vertices_extreme S (hr ▸ mem_range_self i))

theorem original_in_model (S : Shape) (f : Fin 2 → Plane →ᵃ[ℝ] ℝ)
    (p : Endpoints 2) (hW : ∀ i, 0 < rangeWidth (body S) (f i))
    (ho : ∀ i, p.1 i < p.2 i) (hR : Plank.PlanarParameterDomain.budget (body S) f p < 1)
    (he : Equality (body S) f p) :
    ∀ i, (f i).linear ![1,0] = 0 ∨ (f i).linear ![0,1] = 0 := by
  have hK := CrossedQuadrilateralContainedOriginal.compact_body S
  have hne := CrossedQuadrilateralContainedOriginal.body_nonempty S
  have hV := CrossedQuadrilateralContainedOriginal.area_body_pos S
  choose g a hg hnorm hunit using fun i => Plank.PlanarNormalization.exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 2 := (fun i => (p.1 i-a i)/rangeWidth (body S) (f i),
    fun i => (p.2 i-a i)/rangeWidth (body S) (f i))
  have hqo (i) : q.1 i < q.2 i :=
    (div_lt_div_iff_of_pos_right (hW i)).mpr (sub_lt_sub_right (ho i) _)
  have hband (i) : {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i} =
      {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_ofPred_eq,hg]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hb : Plank.PlanarParameterDomain.budget (body S) g q =
      Plank.PlanarParameterDomain.budget (body S) f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hgap : gapArea (body S) g q = gapArea (body S) f p := by simp only [gapArea,hband]
  have hEq : Equality (body S) g q := by
    change gapArea (body S) g q = (max 0 (1-Plank.PlanarParameterDomain.budget (body S) g q))^2*
      (volume (body S)).toReal
    rwa [hgap,hb]
  have hd := CrossedQuadrilateralSurvivingDirections.two_in_chart (genuine S) hV S
    (AffineEquiv.refl ℝ Plane) (by simp) g q hnorm hunit hqo (by rwa [hb]) hEq
  intro i
  have hlin := Plank.PlanarTransverseNormalization.linear_eq_of_formula (f i) (g i) (a i) _ (hg i)
  have hz (v : Plane) (h : (g i).linear v = 0) : (f i).linear v = 0 := by
    rw [hlin,LinearMap.smul_apply,smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (hW i).ne')
  exact (hd i).imp (hz _) (hz _)

/-- No normalization, supplied direction, overlap or cell-count hypothesis
is imposed on the two original physical planks. -/
theorem physical (S : Shape) (p : Fin 2 → Plank) (ho : ∀ i, (p i).lo < (p i).hi)
    (hR : (∑ i, relativeWidth S (p i)) < 1)
    (he : (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal) :
    ∀ i, (p i).u.1 = 0 ∨ (p i).u.2 = 0 := by
  let f (i : Fin 2) := ParallelProductPlane.pullForm (direction (p i).u)
  let q : Endpoints 2 := (fun i => (p i).lo,fun i => (p i).hi)
  have hW (i) : 0 < rangeWidth (body S) (f i) := by
    rw [width_preimage]
    exact direction_width_pos S (p i).u_ne_zero
  have hb : Plank.PlanarParameterDomain.budget (body S) f q = ∑ i, relativeWidth S (p i) := by
    apply Finset.sum_congr rfl
    intro i _
    change ((p i).hi-(p i).lo)/rangeWidth (body S) (f i) = _
    rw [width_preimage]
    rfl
  have hg : gapArea (body S) f q = (volume (S.body \ ⋃ i, (p i).set)).toReal := by
    rw [← ParallelProductPlane.volume_preimage]
    rw [Set.preimage_sdiff,Set.preimage_iUnion]
    rfl
  have hEq : Equality (body S) f q := by
    change gapArea (body S) f q =
      (max 0 (1-Plank.PlanarParameterDomain.budget (body S) f q))^2*(volume (body S)).toReal
    rw [hb,hg,max_eq_right (sub_pos.mpr hR).le,ParallelProductPlane.volume_preimage]
    exact he
  have hd := original_in_model S f q hW ho (by rwa [hb]) hEq
  intro i
  have h := hd i
  change (p i).u.1*1+(p i).u.2*0 = 0 ∨ (p i).u.1*0+(p i).u.2*1 = 0 at h
  simpa only [mul_one,mul_zero,add_zero,zero_add] using h

theorem lower_bound (S : Shape) (p : Fin 2 → Plank) :
    (max 0 (1-∑ i, relativeWidth S (p i)))^2*(volume S.body).toReal ≤
      (volume (S.body \ ⋃ i, (p i).set)).toReal := by
  let f (i : Fin 2) := ParallelProductPlane.pullForm (direction (p i).u)
  have hW (i) : rangeWidth (body S) (f i) = rangeWidth S.body (direction (p i).u) :=
    width_preimage S.body _
  have hg : volume ((body S) \ ⋃ i, {x | (p i).lo ≤ f i x ∧ f i x ≤ (p i).hi}) =
      volume (S.body \ ⋃ i, (p i).set) := by
    rw [← ParallelProductPlane.volume_preimage]
    rw [Set.preimage_sdiff,Set.preimage_iUnion]
    rfl
  have hh := Plank.PlanarTwoPlank.sharpPlanarBound_two (body S)
    (CrossedQuadrilateralContainedOriginal.compact_body S)
    (CrossedQuadrilateralContainedOriginal.convex_body S)
    (CrossedQuadrilateralContainedOriginal.body_nonempty S) f
    (fun i => (p i).lo) (fun i => (p i).hi) (fun i => (p i).lo_le_hi)
    (fun i => by rw [hW]; exact direction_width_pos S (p i).u_ne_zero)
  simpa only [hW,hg,ParallelProductPlane.volume_preimage,relativeWidth] using hh

end Quant.CrossedQuadrilateralPhysicalPairDirections

/-- info: 'Quant.CrossedQuadrilateralPhysicalPairDirections.original_in_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralPhysicalPairDirections.original_in_model

/-- info: 'Quant.CrossedQuadrilateralPhysicalPairDirections.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralPhysicalPairDirections.physical
