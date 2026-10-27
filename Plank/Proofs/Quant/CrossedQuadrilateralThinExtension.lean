/- A quantitative exclusion of thin non-diagonal extensions of a sharp band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralResidualArea

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralThinExtension
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralCalibratedPacking
open CrossedQuadrilateralResidualArea
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def total (S : Shape) (k lo hi : Fin 2 → ℝ) : ℝ :=
  ∑ i, (hi i-lo i)/rangeWidth S.body (direction (1,k i))

theorem area_gap (S : Shape) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (volume (gap S r)).toReal = (1-r)^2*(volume S.body).toReal := by
  have he := volume_gap_two S (r := 0) (s := r) (by norm_num) hr (by simpa using hr1)
  simp only [mul_zero,sub_zero] at he
  have hs : S.body \ ({z : Point | 0 ≤ z.1 ∧ z.1 ≤ 0} ∪
      {z : Point | -S.d*r ≤ z.2 ∧ z.2 ≤ S.b*r}) =
      gap S r \ CrossedQuadrilateralPlacement.band false 0 0 := by
    ext z
    simp only [gap,CrossedQuadrilateralPlacement.band,mem_sdiff,mem_union,mem_ofPred_eq]
    tauto
  rw [hs,measure_sdiff_null (CrossedQuadrilateralPlacement.volume_band_null false 0)] at he
  rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)]

theorem covered_pair_le (S : Shape) (r : ℝ) (k lo hi : Fin 2 → ℝ) :
    (volume (gap S r)).toReal-(volume (gap S r \ ⋃ i, band (k i) (lo i) (hi i))).toReal ≤
      ∑ i, (volume (gap S r ∩ band (k i) (lo i) (hi i))).toReal := by
  have hm : MeasurableSet (⋃ i, band (k i) (lo i) (hi i)) :=
    MeasurableSet.iUnion (fun i => measurable_band _ _ _)
  have hf : volume (gap S r) ≠ ⊤ :=
    measure_ne_top_of_subset sdiff_subset (compact_body S).measure_ne_top
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := gap S r) hm hf
  have hu := measureReal_iUnion_fintype_le (μ := volume)
    (fun i => gap S r ∩ band (k i) (lo i) (hi i))
  rw [← inter_iUnion] at hu
  change (volume (gap S r \ ⋃ i, band (k i) (lo i) (hi i))).toReal+
    (volume (gap S r ∩ ⋃ i, band (k i) (lo i) (hi i))).toReal = (volume (gap S r)).toReal at hd
  change (volume (gap S r ∩ ⋃ i, band (k i) (lo i) (hi i))).toReal ≤
    ∑ i, (volume (gap S r ∩ band (k i) (lo i) (hi i))).toReal at hu
  linarith only [hd,hu]

/-- For any two fixed non-diagonal directions there is a positive threshold,
uniform in all placements and in the calibrated starting width. A positive
additional budget below epsilon times the remaining width gives STRICTLY more
uncovered area than the quantitative equality target. Null added bands are allowed. -/
theorem exists_threshold (S : Shape) (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 ≤ r → r < 1 →
      ∀ lo hi : Fin 2 → ℝ, (∀ i, lo i ≤ hi i) →
      0 < total S k lo hi → total S k lo hi < ε*(1-r) →
      (1-r-total S k lo hi)^2*(volume S.body).toReal <
        (volume (gap S r \ ⋃ i, band (k i) (lo i) (hi i))).toReal := by
  choose M hM hstrict hbound using fun i => strict_covered_bound S (hk i)
  let B := max (M 0) (M 1)
  have hB : B < 2*(volume S.body).toReal := max_lt (hstrict 0) (hstrict 1)
  have hMB (i : Fin 2) : M i ≤ B := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  let ε := (2*(volume S.body).toReal-B)/(volume S.body).toReal
  have hε : 0 < ε := div_pos (sub_pos.mpr hB) (area_body_pos S)
  refine ⟨ε,hε,?_⟩
  intro r hr hr1 lo hi ho ht hsmall
  have hw (i : Fin 2) : 0 < rangeWidth S.body (direction (1,k i)) :=
    direction_width_pos S (by intro he; have hh := congrArg Prod.fst he; norm_num at hh)
  have hwidth (i : Fin 2) : 0 ≤ (hi i-lo i)/rangeWidth S.body (direction (1,k i)) :=
    div_nonneg (sub_nonneg.mpr (ho i)) (hw i).le
  have hu := (covered_pair_le S r k lo hi).trans
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (hbound i r hr hr1 (lo i) (hi i) (ho i)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hMB i) (sub_pos.mpr hr1).le) (hwidth i))))
  rw [← Finset.mul_sum,area_gap S hr hr1] at hu
  change (1-r)^2*(volume S.body).toReal-
    (volume (gap S r \ ⋃ i, band (k i) (lo i) (hi i))).toReal ≤
      (1-r)*B*total S k lo hi at hu
  have he : ε*(volume S.body).toReal=2*(volume S.body).toReal-B :=
    div_mul_cancel₀ _ (area_body_pos S).ne'
  have hs := mul_lt_mul_of_pos_right hsmall (area_body_pos S)
  have hh : 0 < (1-r)*(2*(volume S.body).toReal-B)-total S k lo hi*(volume S.body).toReal := by
    apply sub_pos.mpr
    calc
      total S k lo hi*(volume S.body).toReal < ε*(1-r)*(volume S.body).toReal := hs
      _ = (1-r)*(ε*(volume S.body).toReal) := by ring
      _ = (1-r)*(2*(volume S.body).toReal-B) := by rw [he]
  have hp := mul_pos ht hh
  nlinarith only [hu,hp]

end Quant.CrossedQuadrilateralThinExtension

/-- info: 'Quant.CrossedQuadrilateralThinExtension.exists_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralThinExtension.exists_threshold
