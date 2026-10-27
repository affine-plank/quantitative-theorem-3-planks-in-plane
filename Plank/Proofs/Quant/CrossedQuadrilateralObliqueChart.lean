/- A normalized shear chart for actual oblique sections and area. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCalibratedPacking
public import Plank.Proofs.Quant.CrossedQuadrilateralSectionGap

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliqueChart
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralAffine CrossedQuadrilateralReflections
open Plank.Convex.DeficientHeightTilt

def shear (k w : ℝ) (hw : w ≠ 0) : Point ≃ₗ[ℝ] Point where
  toFun z := ((z.1+k*z.2)/w,z.2)
  invFun z := (w*z.1-k*z.2,z.2)
  left_inv z := by
    ext
    · change w*((z.1+k*z.2)/w)-k*z.2=z.1
      rw [mul_div_cancel₀ _ hw]
      ring
    · rfl
  right_inv z := by ext <;> simp [hw]
  map_add' z v := by ext <;> dsimp <;> ring
  map_smul' c z := by ext <;> dsimp <;> ring

def chart (k c w : ℝ) (hw : w ≠ 0) : Point ≃ᵃ[ℝ] Point :=
  (shear k w hw).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ Point (-c/w,0))

theorem chart_apply (k c w : ℝ) (hw : w ≠ 0) (z : Point) :
    chart k c w hw z = ((z.1+k*z.2-c)/w,z.2) := by
  ext
  · change -c/w+(z.1+k*z.2)/w = (z.1+k*z.2-c)/w
    ring
  · change 0+z.2=z.2
    ring

theorem chart_symm_apply (k c w : ℝ) (hw : w ≠ 0) (z : Point) :
    (chart k c w hw).symm z = (w*z.1+c-k*z.2,z.2) := by
  apply (chart k c w hw).injective
  rw [AffineEquiv.apply_symm_apply,chart_apply]
  ext
  · dsimp
    field_simp [hw]
    ring
  · rfl

theorem chart_det (k c w : ℝ) (hw : w ≠ 0) :
    LinearMap.det (chart k c w hw).linear.toLinearMap = w⁻¹ := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Module.Basis.finTwoProd]
  change ((1+k*0)/w)*1-((0+k*1)/w)*0=w⁻¹
  simp

theorem area_chart (k c w : ℝ) (hw : 0 < w) (A : Set Point) :
    (volume A).toReal = w*(volume (chart k c w hw.ne' '' A)).toReal := by
  rw [area_image,jacobian,chart_det,abs_of_pos (inv_pos.mpr hw)]
  field_simp

theorem fiber_chart (k c w : ℝ) (hw : w ≠ 0) (A : Set Point) (q : ℝ) :
    Plank.ConvexSections.fiber (chart k c w hw '' A) q = fiber A k (w*q+c) := by
  ext y
  change (q,y) ∈ chart k c w hw '' A ↔ (w*q+c-k*y,y) ∈ A
  rw [image_mem,chart_symm_apply]

theorem length_chart (k c w : ℝ) (hw : w ≠ 0) (A : Set Point) (q : ℝ) :
    Plank.PlanarConvexSectionLength.length (chart k c w hw '' A) q =
      sectionLength A k (w*q+c) := by
  rw [Plank.PlanarConvexSectionLength.length,fiber_chart]
  rfl

theorem projected_body (S : Shape) (k c w : ℝ) (hw : 0 < w)
    (g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ)
    (hg : ∀ z, g z = (z 0+k*z 1-c)/w)
    (hnorm : ∀ z ∈ CrossedQuadrilateralFormDirections.body S, 0 ≤ g z ∧ g z ≤ 1)
    (hunit : rangeWidth (CrossedQuadrilateralFormDirections.body S) g = 1) :
    Prod.fst '' (chart k c w hw.ne' '' S.body) = Icc (0 : ℝ) 1 := by
  have he : Prod.fst '' (chart k c w hw.ne' '' S.body) =
      g '' CrossedQuadrilateralFormDirections.body S := by
    ext t
    constructor
    · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
      refine ⟨ParallelProductPlane.coordinates.symm y,by simpa using hy,?_⟩
      rw [hg,chart_apply]
      rfl
    · rintro ⟨z,hz,rfl⟩
      refine ⟨chart k c w hw.ne' (ParallelProductPlane.coordinates z),
        ⟨ParallelProductPlane.coordinates z,hz,rfl⟩,?_⟩
      rw [chart_apply,hg]
      rfl
  rw [he]
  exact Plank.PlanarBodySectionDensity.image_eq_unitInterval
    (ParallelProductPlane.compact_preimage (compact_body S))
    ((convex_body S).linear_preimage ParallelProductPlane.coordinates.toLinearMap)
    ⟨0,zero_mem S⟩ g hnorm hunit

theorem interior_body (S : Shape) : (interior S.body).Nonempty := by
  have hh := Plank.PlanarGapAnalysis.interior_nonempty_of_area_pos
    (ParallelProductPlane.compact_preimage (compact_body S))
    ((convex_body S).linear_preimage ParallelProductPlane.coordinates.toLinearMap)
    (show 0 < (volume (CrossedQuadrilateralFormDirections.body S)).toReal by
      rw [ParallelProductPlane.volume_preimage]; exact area_body_pos S)
  have he : S.body = ParallelProductPlane.coordinates '' CrossedQuadrilateralFormDirections.body S :=
    (image_preimage_eq _ ParallelProductPlane.coordinates.surjective).symm
  rw [he]
  change (interior (ParallelProductPlane.coordinates.toHomeomorph ''
    CrossedQuadrilateralFormDirections.body S)).Nonempty
  rw [← ParallelProductPlane.coordinates.toHomeomorph.image_interior]
  exact hh.image _

/-- The density is explicitly the actual sheared fiber length, multiplied by
its actual directional range. It is not an abstract optimizer certificate. -/
theorem exists_density (S : Shape) (k c w : ℝ) (hw : 0 < w)
    (g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ)
    (hg : ∀ z, g z = (z 0+k*z 1-c)/w)
    (hnorm : ∀ z ∈ CrossedQuadrilateralFormDirections.body S, 0 ≤ g z ∧ g z ≤ 1)
    (hunit : rangeWidth (CrossedQuadrilateralFormDirections.body S) g = 1) :
    ∃ D : Plank.PlanarUnitSectionDensity.UnitSectionDensity
      (CrossedQuadrilateralFormDirections.body S) g,
      ∀ q ∈ Icc (0 : ℝ) 1, D.density q = w*sectionLength S.body k (w*q+c) := by
  let T := chart k c w hw.ne'
  let B := T '' S.body
  have hB : IsCompact B := (compact_body S).image T.toContinuousAffineEquiv.continuous
  have hcB : Convex ℝ B := (convex_body S).affine_image T.toAffineMap
  have hiB : (interior B).Nonempty := by
    change (interior (T.toContinuousAffineEquiv.toHomeomorph '' S.body)).Nonempty
    rw [← T.toContinuousAffineEquiv.toHomeomorph.image_interior]
    exact (interior_body S).image T
  have hp : Prod.fst '' B = Icc (0 : ℝ) 1 := projected_body S k c w hw g hg hnorm hunit
  have hrep (lo hi : ℝ) : T '' (S.body ∩ {z | lo ≤ (z.1+k*z.2-c)/w ∧
      (z.1+k*z.2-c)/w ≤ hi}) = Plank.PlanarConvexSectionIntegral.slab B lo hi := by
    ext z
    constructor
    · rintro ⟨y,⟨hy,hl,hu⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,by simpa only [T,chart_apply,mem_ofPred_eq] using And.intro hl hu⟩
    · rintro ⟨⟨y,hy,rfl⟩,hz⟩
      exact ⟨y,⟨hy,by simpa only [T,chart_apply,mem_ofPred_eq] using hz⟩,rfl⟩
  have harea (lo hi : ℝ) :
      Plank.PlanarBodySectionDensity.coveredArea (CrossedQuadrilateralFormDirections.body S) g lo hi =
        w*(volume (Plank.PlanarConvexSectionIntegral.slab B lo hi)).toReal := by
    have he : CrossedQuadrilateralFormDirections.body S ∩ Plank.PlanarSevenCellArea.plank g lo hi =
        ParallelProductPlane.coordinates ⁻¹' (S.body ∩ {z | lo ≤ (z.1+k*z.2-c)/w ∧
          (z.1+k*z.2-c)/w ≤ hi}) := by
      ext z
      simp only [mem_inter_iff,mem_preimage,Plank.PlanarSevenCellArea.plank,mem_ofPred_eq,hg]
      rfl
    rw [Plank.PlanarBodySectionDensity.coveredArea,he,ParallelProductPlane.volume_preimage,
      area_chart k c w hw,hrep]
  refine ⟨{
    density := fun q => w*Plank.PlanarConvexSectionDensity.density B q
    continuous := continuous_const.mul (Plank.PlanarConvexSectionDensity.continuous_density hB hcB hiB hp)
    nonnegative := fun q => mul_nonneg hw.le (Plank.PlanarConvexSectionDensity.nonnegative_density B q)
    concave := (Plank.PlanarConvexSectionDensity.concaveOn_density hB hcB hp).smul hw.le
    area_integral := ?_
    mass_eq := ?_ },?_⟩
  · intro lo hi hlo ho hhi
    rw [harea,Plank.PlanarConvexSectionDensity.area_slab_eq_integral_density hB hlo ho hhi,
      intervalIntegral.integral_const_mul]
  · change (∫ q in (0 : ℝ)..1, w*Plank.PlanarConvexSectionDensity.density B q) = _
    rw [intervalIntegral.integral_const_mul]
    change w*Plank.ConcaveDensity.mass (Plank.PlanarConvexSectionDensity.density B) = _
    rw [Plank.PlanarConvexSectionDensity.mass_density hB hp,
      ParallelProductPlane.volume_preimage]
    exact (area_chart k c w hw S.body).symm
  · intro q hq
    change w*Plank.PlanarConvexSectionDensity.density B q = _
    rw [Plank.PlanarConvexSectionDensity.density_eq B hq]
    exact congrArg (w*·) (length_chart k c w hw.ne' S.body q)

end Quant.CrossedQuadrilateralObliqueChart

/-- info: 'Quant.CrossedQuadrilateralObliqueChart.exists_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliqueChart.exists_density
