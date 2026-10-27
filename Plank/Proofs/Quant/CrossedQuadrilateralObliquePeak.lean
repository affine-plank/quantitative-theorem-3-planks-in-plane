/- Uniform strict bounds for actual non-diagonal fiber lengths. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliqueChart

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliquePeak
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralObliqueChart
open Plank.Convex.DeficientHeightTilt

/-- Strict efficiency in every non-diagonal direction, for the actual fibers
on the entire real line, including supporting and empty sections. -/
theorem strict_original_bound (S : Shape) {k : ℝ} (hk : k ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ M*rangeWidth S.body (direction (1,k)) < 2*(volume S.body).toReal ∧
      ∀ q : ℝ, sectionLength S.body k q ≤ M := by
  let F := ParallelProductPlane.pullForm (direction (1,k))
  let w := rangeWidth S.body (direction (1,k))
  have hw : 0 < w := direction_width_pos S (by
    intro he; have hh := congrArg Prod.fst he; norm_num at hh)
  have hwidth : rangeWidth (CrossedQuadrilateralFormDirections.body S) F = w :=
    CrossedQuadrilateralDirections.width_preimage S.body _
  have hK := ParallelProductPlane.compact_preimage (compact_body S)
  have hne : (CrossedQuadrilateralFormDirections.body S).Nonempty := ⟨0,zero_mem S⟩
  obtain ⟨g,c,hg,hnorm,hunit⟩ := Plank.PlanarNormalization.exists_unit_form hK hne F
    (by rwa [hwidth])
  rw [hwidth] at hg
  have heF (z : Fin 2 → ℝ) : F z = z 0+k*z 1 := by
    change 1*z 0+k*z 1=z 0+k*z 1
    ring
  have hformula (z : Fin 2 → ℝ) : g z = (z 0+k*z 1-c)/w := by
    rw [hg,heF]
  obtain ⟨D,hD⟩ := exists_density S k c w hw g hformula hnorm hunit
  obtain ⟨q,hq,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) D.continuous.continuousOn
  have hlin := Plank.PlanarTransverseNormalization.linear_eq_of_formula F g c w hg
  have hbad : ¬(g.linear ![1,0] = 0 ∨ g.linear ![0,1] = 0) := by
    rintro (hx | hy)
    · rw [hlin] at hx
      change w⁻¹*(1*1+k*0)=0 at hx
      exact hw.ne' (by simpa only [mul_one,mul_zero,add_zero,inv_eq_zero] using hx)
    · rw [hlin] at hy
      change w⁻¹*(1*0+k*1)=0 at hy
      have hprod : w⁻¹*k=0 := by simpa only [mul_zero,mul_one,zero_add] using hy
      exact (mul_ne_zero (inv_ne_zero hw.ne') hk) hprod
  have hstrict : D.density q < 2*(volume (CrossedQuadrilateralFormDirections.body S)).toReal := by
    apply lt_of_le_of_ne (Plank.PlanarSectionPeakRigidity.density_le_twice_area D hq)
    intro he
    have hd := CrossedQuadrilateralSectionGap.diagonal_of_peak hK S
      (AffineEquiv.refl ℝ (Fin 2 → ℝ)) (by simp) g D hunit hq he
    exact hbad hd
  rw [ParallelProductPlane.volume_preimage] at hstrict
  refine ⟨D.density q/w,div_nonneg (D.nonnegative q) hw.le,?_,?_⟩
  · change (D.density q/w)*w < _
    rwa [div_mul_cancel₀ _ hw.ne']
  · intro z
    by_cases ht : (z-c)/w ∈ Icc (0 : ℝ) 1
    · have hh : D.density ((z-c)/w) ≤ D.density q := hmax ht
      rw [hD _ ht] at hh
      have he : w*((z-c)/w)+c=z := by rw [mul_div_cancel₀ _ hw.ne']; ring
      rw [he] at hh
      exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hh)
    · have hzero : fiber S.body k z = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hz : ![z-k*y,y] ∈ CrossedQuadrilateralFormDirections.body S := hy
        have hg' : g ![z-k*y,y] = (z-c)/w := by
          rw [hformula]
          congr 1
          change z-k*y+k*y-c=z-c
          ring
        exact ht (by simpa only [hg',mem_Icc] using hnorm _ hz)
      rw [sectionLength,hzero,measure_empty,ENNReal.toReal_zero]
      exact div_nonneg (D.nonnegative q) hw.le

/-- A calibrated diagonal cut preserves the uniform strict inefficiency of
every fixed non-diagonal direction. No bound on residual fibers is assumed. -/
theorem strict_residual_bound (S : Shape) {k : ℝ} (hk : k ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ M*rangeWidth S.body (direction (1,k)) < 2*(volume S.body).toReal ∧
      ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ q : ℝ,
        sectionLength (CrossedQuadrilateralCalibratedPacking.gap S r) k q ≤ (1-r)*M := by
  obtain ⟨M,hM,hstrict,hbound⟩ := strict_original_bound S hk
  refine ⟨M,hM,hstrict,?_⟩
  intro r hr hr1 q
  obtain ⟨s,hs⟩ := CrossedQuadrilateralCalibratedPacking.actual_section_packing S hr hr1 k q
  exact hs.trans (mul_le_mul_of_nonneg_left (hbound s) (sub_pos.mpr hr1).le)

end Quant.CrossedQuadrilateralObliquePeak

/-- info: 'Quant.CrossedQuadrilateralObliquePeak.strict_residual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliquePeak.strict_residual_bound
