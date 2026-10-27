/- Actual area removed from the calibrated residual by an oblique plank. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliquePeak

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralResidualArea
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralCalibratedSections CrossedQuadrilateralCalibratedPacking
open CrossedQuadrilateralObliqueChart CrossedQuadrilateralObliquePeak
open Plank.Convex.DeficientHeightTilt

def band (k lo hi : ℝ) : Set Point := {z | lo ≤ z.1+k*z.2 ∧ z.1+k*z.2 ≤ hi}

theorem measurable_band (k lo hi : ℝ) : MeasurableSet (band k lo hi) := by
  unfold band
  apply IsClosed.measurableSet
  have hf : Continuous (fun z : Point => z.1+k*z.2) := by fun_prop
  exact (isClosed_le continuous_const hf).inter (isClosed_le hf continuous_const)

theorem closed_section_eq (S : Shape) (r k q : ℝ) :
    sectionLength (closedResidual S r) k q = sectionLength (gap S r) k q := by
  have hsub : fiber (gap S r) k q ⊆ fiber (closedResidual S r) k q :=
    fun _ hy => gap_subset S r hy
  have hsub' : fiber (closedResidual S r) k q ⊆
      fiber (gap S r) k q ∪ ({-S.d*r,S.b*r} : Set ℝ) := by
    intro y hy
    by_cases hlo : y = -S.d*r
    · exact Or.inr (by simp [hlo])
    by_cases hhi : y = S.b*r
    · exact Or.inr (by simp [hhi])
    left
    refine ⟨residual_subset S r hy,?_⟩
    intro hb
    change -S.d*r ≤ y ∧ y ≤ S.b*r at hb
    rcases hy with hy | hy
    · have hh : r ≤ y/(-S.d) := hy.2
      have hl := (le_div_iff_of_neg (neg_lt_zero.mpr S.hd)).mp hh
      apply hlo
      linarith only [hl,hb.1]
    · have hh : r ≤ y/S.b := hy.2
      have hu := (le_div_iff₀ S.hb).mp hh
      apply hhi
      linarith only [hu,hb.2]
  have hz : volume ({-S.d*r,S.b*r} : Set ℝ) = 0 :=
    (Set.Finite.insert _ (Set.finite_singleton _)).measure_zero volume
  have he : volume (fiber (closedResidual S r) k q) = volume (fiber (gap S r) k q) := by
    apply le_antisymm
    · have hu := measure_union_le (μ := volume) (fiber (gap S r) k q)
        ({-S.d*r,S.b*r} : Set ℝ)
      rw [hz,add_zero] at hu
      exact (measure_mono hsub').trans hu
    · exact measure_mono hsub
  exact congrArg ENNReal.toReal he

theorem area_band_integral {A : Set Point} (hA : IsCompact A) (k : ℝ)
    {lo hi : ℝ} (ho : lo ≤ hi) :
    (volume (A ∩ band k lo hi)).toReal = ∫ q in lo..hi, sectionLength A k q := by
  let T := chart k 0 1 (by norm_num)
  have hB : IsCompact (T '' A) := hA.image T.toContinuousAffineEquiv.continuous
  have he : T '' (A ∩ band k lo hi) = Plank.PlanarConvexSectionIntegral.slab (T '' A) lo hi := by
    ext z
    constructor
    · rintro ⟨y,⟨hy,hb⟩,rfl⟩
      refine ⟨⟨y,hy,rfl⟩,?_⟩
      simpa only [T,chart_apply,sub_zero,div_one,band,mem_ofPred_eq] using hb
    · rintro ⟨⟨y,hy,rfl⟩,hb⟩
      refine ⟨y,⟨hy,?_⟩,rfl⟩
      simpa only [T,chart_apply,sub_zero,div_one,band,mem_ofPred_eq] using hb
  have hl (q : ℝ) : Plank.PlanarConvexSectionLength.length (T '' A) q = sectionLength A k q := by
    simpa only [one_mul,add_zero] using length_chart k 0 1 (by norm_num) A q
  rw [area_chart k 0 1 (by norm_num),one_mul,he,
    Plank.PlanarConvexSectionIntegral.area_slab_eq_integral hB ho]
  exact intervalIntegral.integral_congr (fun q _ => hl q)

theorem area_band_le {A : Set Point} (hA : IsCompact A) (k M : ℝ)
    (hM : ∀ q : ℝ, sectionLength A k q ≤ M) {lo hi : ℝ} (ho : lo ≤ hi) :
    (volume (A ∩ band k lo hi)).toReal ≤ (hi-lo)*M := by
  rw [area_band_integral hA k ho]
  let T := chart k 0 1 (by norm_num)
  have hl : Plank.PlanarConvexSectionLength.length (T '' A) = sectionLength A k := by
    funext q
    simpa only [one_mul,add_zero] using length_chart k 0 1 (by norm_num) A q
  have hInt : Integrable (Plank.PlanarConvexSectionLength.length (T '' A)) :=
    Plank.PlanarConvexSectionIntegral.integrable_length
    (hA.image T.toContinuousAffineEquiv.continuous)
  rw [hl] at hInt
  have hh := intervalIntegral.integral_mono_on (μ := volume) ho hInt.intervalIntegrable
    (intervalIntegrable_const (c := M)) (fun q _ => hM q)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh

/-- One uniform constant, strictly below twice the original area, bounds the
actual area removed by every additional band in a fixed non-diagonal direction.
Its width is divided by the full actual range on the original quadrilateral. -/
theorem strict_covered_bound (S : Shape) {k : ℝ} (hk : k ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ M < 2*(volume S.body).toReal ∧
      ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ lo hi : ℝ, lo ≤ hi →
        (volume (gap S r ∩ band k lo hi)).toReal ≤
          (1-r)*M*((hi-lo)/rangeWidth S.body (direction (1,k))) := by
  obtain ⟨M,hM,hm,hbound⟩ := strict_residual_bound S hk
  let w := rangeWidth S.body (direction (1,k))
  have hw : 0 < w := direction_width_pos S (by
    intro he; have hh := congrArg Prod.fst he; norm_num at hh)
  refine ⟨M*w,mul_nonneg hM hw.le,hm,?_⟩
  intro r hr hr1 lo hi ho
  have hclosed (q) : sectionLength (closedResidual S r) k q ≤ (1-r)*M := by
    rw [closed_section_eq]
    exact hbound r hr hr1 q
  have ha := area_band_le (compact_residual S r) k ((1-r)*M) hclosed ho
  have hmono : (volume (gap S r ∩ band k lo hi)).toReal ≤
      (volume (closedResidual S r ∩ band k lo hi)).toReal := by
    exact ENNReal.toReal_mono
      (measure_ne_top_of_subset inter_subset_left (compact_residual S r).measure_ne_top)
      (measure_mono (fun _ hz => ⟨gap_subset S r hz.1,hz.2⟩))
  refine (hmono.trans ha).trans_eq ?_
  change (hi-lo)*((1-r)*M) = (1-r)*(M*w)*((hi-lo)/w)
  field_simp [hw.ne']

end Quant.CrossedQuadrilateralResidualArea

/-- info: 'Quant.CrossedQuadrilateralResidualArea.strict_covered_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralResidualArea.strict_covered_bound
