/- Actual uncovered area for two ordered parallel intervals. -/
module
public import Plank.Proofs.Quant.UnimodalPlanarMerge
public import Plank.Proofs.Quant.CrossedQuadrilateralSectionGeometry
public import Plank.Proofs.Quant.IntervalIntegralSecondDifference

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.ParallelPairGapIntegral
open Set MeasureTheory UnimodalPlanarMerge
open Plank.PlanarConvexSectionLength Plank.PlanarConvexSectionIntegral
open CrossedQuadrilateralAttainment CrossedQuadrilateralSectionGeometry
open CrossedQuadrilateralSectionProfile IntervalIntegralSecondDifference

theorem area {K : Set Point} (hK : IsCompact K) {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (volume (K \ (band a b ∪ band c d))).toReal =
      (volume K).toReal-(∫ x in a..b, length K x)-(∫ x in c..d, length K x) := by
  have hd : AEDisjoint volume (K ∩ band a b) (K ∩ band c d) := by
    apply measure_mono_null (t := {z : Point | z.1 = b})
    · intro z hz
      have hb : z.1 ≤ b := hz.1.2.2
      have hc : c ≤ z.1 := hz.2.2.1
      change z.1 = b
      linarith only [hb,hc,hbc]
    · simpa [dot] using volume_line (by norm_num : ((1,0) : Point) ≠ 0) b
  have hu : volume.real (K ∩ (band a b ∪ band c d)) =
      (∫ x in a..b, length K x)+(∫ x in c..d, length K x) := by
    rw [inter_union_distrib_left]
    change (volume ((K ∩ band a b) ∪ (K ∩ band c d))).toReal = _
    rw [measure_union₀ (hK.measurableSet.inter (measurable_band c d)).nullMeasurableSet hd,
      ENNReal.toReal_add (measure_ne_top_of_subset inter_subset_left hK.measure_ne_top)
        (measure_ne_top_of_subset inter_subset_left hK.measure_ne_top)]
    change (volume (slab K a b)).toReal+(volume (slab K c d)).toReal = _
    rw [area_slab_eq_integral hK hab,area_slab_eq_integral hK hcd]
  have hs := measureReal_sdiff_add_inter (μ := volume) (s := K)
    ((measurable_band a b).union (measurable_band c d)) hK.measure_ne_top
  change volume.real (K \ (band a b ∪ band c d)) =
    volume.real K-(∫ x in a..b, length K x)-(∫ x in c..d, length K x)
  linarith only [hu,hs]

theorem primitive_sub {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, f x) = primitive f b-primitive f a := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
  unfold primitive
  linarith only [h]

/-- This formula uses the actual residual body and is valid for every slope. -/
theorem residual_area (S : Shape) (k : ℝ) {lo hi a b c d : ℝ}
    (ho : lo < hi) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal =
      (volume (closedResidual S k lo hi)).toReal+
        primitive (residual S k lo hi) a-primitive (residual S k lo hi) b+
        primitive (residual S k lo hi) c-primitive (residual S k lo hi) d := by
  rw [gap_eq_closedResidual S k lo hi]
  rw [area (compact_closedResidual S k lo hi) hab hbc hcd]
  simp only [length_closedResidual S k ho]
  rw [primitive_sub (continuous_residual S k lo hi),primitive_sub (continuous_residual S k lo hi)]
  ring

end Quant.ParallelPairGapIntegral

/-- info: 'Quant.ParallelPairGapIntegral.residual_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.ParallelPairGapIntegral.residual_area
