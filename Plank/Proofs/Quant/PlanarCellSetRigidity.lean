/- Upgrade tight cell-area interpolation to exact geometric set identities. -/
module

public import Plank.Proofs.Quant.PlanarInactiveCellMotion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellSetRigidity

open Set MeasureTheory PlanarQuantitative PlanarCellArea PlanarInductionBoundary
open scoped Pointwise

/-- A compact subset of a positive-area compact convex body with the same
area is the entire body, including its boundary. -/
theorem eq_of_subset_of_area_eq {A B : Set Point} (hA : IsCompact A) (hB : IsCompact B)
    (hconv : Convex ℝ B) (hpos : 0 < (volume B).toReal) (hsub : A ⊆ B)
    (heq : (volume A).toReal = (volume B).toReal) : A = B := by
  apply Subset.antisymm hsub
  apply (PlanarGapAnalysis.area_sdiff_eq_zero_iff_subset hB hconv hpos hA.isClosed).mp
  have hh := measureReal_sdiff (μ := volume) hsub hA.measurableSet hB.measure_ne_top
  change (volume (B \ A)).toReal = (volume B).toReal-(volume A).toReal at hh
  rw [heq,sub_self] at hh
  exact hh

/-- A proper homothety of a nonempty compact set determines its center.
Only equality of the actual image sets is assumed. -/
theorem homothety_center_unique {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (a b : Point)
    (heq : AffineMap.homothety a q '' S = AffineMap.homothety b q '' S) : a = b := by
  have hle (a b : Point)
      (hsub : AffineMap.homothety a q '' S ⊆ AffineMap.homothety b q '' S) (i : Fin 2) :
      a i ≤ b i := by
    obtain ⟨x,hx,hmax⟩ := hS.exists_isMaxOn hne (continuous_apply i).continuousOn
    obtain ⟨y,hy,he⟩ := hsub ⟨x,hx,rfl⟩
    have hh := congrFun he i
    simp only [AffineMap.homothety_apply, vadd_eq_add, vsub_eq_sub,
      Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] at hh
    have hm := mul_le_mul_of_nonneg_left (hmax hy) hq
    nlinarith only [hh,hm,hq1]
  ext i
  exact le_antisymm (hle a b heq.subset i) (hle b a heq.symm.subset i)

variable {ι : Type*}

/-- Equality in square-root cell concavity identifies the interpolated
cell with the actual Minkowski interpolation of its two endpoint cells. -/
theorem cell_interpolation_eq {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) (u v : ι → ℝ)
    (hu : (cell K f u).Nonempty) (hv : (cell K f v).Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hpos : 0 < (volume (cell K f (a • u+b • v))).toReal)
    (heq : Real.sqrt (volume (cell K f (a • u+b • v))).toReal =
      a*Real.sqrt (volume (cell K f u)).toReal+b*Real.sqrt (volume (cell K f v)).toReal) :
    cell K f (a • u+b • v) = a • cell K f u+b • cell K f v := by
  let C := a • cell K f u+b • cell K f v
  have hC : IsCompact C :=
    ((isCompact_cell hK f u).image (f := fun x : Point => a • x) (by fun_prop)).add
      ((isCompact_cell hK f v).image (f := fun x : Point => b • x) (by fun_prop))
  have hsub : C ⊆ cell K f (a • u+b • v) := smul_cell_add_subset hconv f u v a b ha hb hab
  have hlo := sqrt_area_smul_add (isCompact_cell hK f u) (isCompact_cell hK f v) hu hv a b ha hb
  have hfinite : volume (cell K f (a • u+b • v)) ≠ ⊤ :=
    (isCompact_cell hK f _).measure_ne_top
  have hhi := Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite (measure_mono hsub))
  have hroot : Real.sqrt (volume C).toReal = Real.sqrt (volume (cell K f (a • u+b • v))).toReal :=
    le_antisymm hhi (heq ▸ hlo)
  have harea : (volume C).toReal = (volume (cell K f (a • u+b • v))).toReal := by
    have hh := congrArg (fun x : ℝ => x^2) hroot
    simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using hh
  exact (eq_of_subset_of_area_eq hC (isCompact_cell hK f _) (convex_cell hconv f _)
    hpos hsub harea).symm

/-- If a cell has exactly the area of a copy contracted toward a point
of the other endpoint cell, it is that actual homothetic image. -/
theorem cell_eq_homothety {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) (u v : ι → ℝ)
    (hpos : 0 < (volume (cell K f u)).toReal) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (y : Point) (hy : y ∈ cell K f v)
    (heq : (volume (cell K f (q • u+(1-q) • v))).toReal =
      q^2*(volume (cell K f u)).toReal) :
    cell K f (q • u+(1-q) • v) = AffineMap.homothety y q '' cell K f u := by
  have hcopy : IsCompact (AffineMap.homothety y q '' cell K f u) :=
    (isCompact_cell hK f u).image (by
      change Continuous (fun x : Point => q • (x-y)+y)
      fun_prop)
  have hsub : AffineMap.homothety y q '' cell K f u ⊆ cell K f (q • u+(1-q) • v) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := smul_cell_add_subset hconv f u v q (1-q) hq.le (sub_nonneg.mpr hq1)
      (by ring) (add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy))
    convert hh using 1
    simp only [AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub]
    module
  exact (eq_of_subset_of_area_eq hcopy (isCompact_cell hK f _) (convex_cell hconv f _)
    (by rw [heq]; exact mul_pos (sq_pos_of_pos hq) hpos) hsub
    ((area_homothety _ y q).trans heq.symm)).symm

/-- Tight interpolation with a nonempty zero-area endpoint collapses that
endpoint to one point. Every positive interpolated cell is an exact copy
of the first cell centered at that point. -/
theorem endpoint_singleton_of_tight_interpolation {K : Set Point}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : ι → Point →L[ℝ] ℝ) (u v : ι → ℝ)
    (hu : (cell K f u).Nonempty) (hv : (cell K f v).Nonempty)
    (hpos : 0 < (volume (cell K f u)).toReal) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (heq : (volume (cell K f (q • u+(1-q) • v))).toReal =
      q^2*(volume (cell K f u)).toReal) :
    ∃ y : Point, cell K f v = {y} ∧
      cell K f (q • u+(1-q) • v) = AffineMap.homothety y q '' cell K f u := by
  obtain ⟨y,hy⟩ := hv
  have hcopy := cell_eq_homothety hK hconv f u v hpos hq hq1.le y hy heq
  refine ⟨y,?_,hcopy⟩
  apply Subset.antisymm
  · intro z hz
    have hzcopy := cell_eq_homothety hK hconv f u v hpos hq hq1.le z hz heq
    exact homothety_center_unique (isCompact_cell hK f u) hu hq.le hq1 z y
      (hzcopy.symm.trans hcopy)
  · rintro z rfl
    exact hy

end Plank.PlanarCellSetRigidity

/-- info: 'Plank.PlanarCellSetRigidity.cell_interpolation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCellSetRigidity.cell_interpolation_eq
/-- info: 'Plank.PlanarCellSetRigidity.endpoint_singleton_of_tight_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCellSetRigidity.endpoint_singleton_of_tight_interpolation
