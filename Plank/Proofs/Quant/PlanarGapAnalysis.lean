/- Continuity and positivity of the actual planar uncovered area. -/
module

public import Plank.Proofs.Quant.PlanarGapCells
public import Plank.Measure.FiniteBandContinuity
public import Plank.Measure.ConvexBody

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarGapAnalysis

open Set MeasureTheory PlanarQuantitative PlanarGapCells
open Plank.Convex.DeficientHeightTilt

/-- Positive planar area supplies interior points of a convex body. -/
theorem interior_nonempty_of_area_pos {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (volume K).toReal) : (interior K).Nonempty := by
  exact ConvexBodyMeasure.interior_nonempty_of_measure_pos volume hK hconv harea

/-- A closed set missing any point of a positive-area convex body misses a
positive-area part. This includes a missed boundary point of the body. -/
theorem area_sdiff_pos_of_not_subset {K C : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (volume K).toReal)
    (hC : IsClosed C) (hnot : ¬ K ⊆ C) : 0 < (volume (K \ C)).toReal := by
  exact ConvexBodyMeasure.measure_sdiff_pos_of_not_subset volume hK hconv harea hC hnot

/-- On a positive-area compact convex body, zero uncovered area is equivalent
to an actual closed cover; it is not merely an almost-everywhere cover. -/
theorem area_sdiff_eq_zero_iff_subset {K C : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (volume K).toReal) (hC : IsClosed C) :
    (volume (K \ C)).toReal = 0 ↔ K ⊆ C := by
  exact ConvexBodyMeasure.measure_sdiff_eq_zero_iff_subset volume hK hconv harea hC

section Finite

variable {ι : Type*} [Fintype ι]

/-- The actual closed-plank gap area is continuous on the entire endpoint
space. No endpoint-order or pairwise-direction assumption is needed. -/
theorem continuous_gap_area {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : ι → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < rangeWidth K (f i)) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) =>
      (volume (K \ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i})).toReal) := by
  exact FiniteBandContinuity.continuous_area_uncovered volume hK.measurableSet
    hK.measure_ne_top (fun i => (continuous_form (f i)).measurable)
    (fun i c => measure_level_zero (f i)
      (linear_ne_zero_of_rangeWidth_pos hne (f i) (hf i)) c)

/-- A finite union of closed affine planks is closed, even with zero-width or
reversed endpoint intervals. -/
theorem isClosed_plank_union (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    IsClosed (⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) :=
  isClosed_iUnion_of_finite fun i =>
    (isClosed_le continuous_const (continuous_form (f i))).inter
      (isClosed_le (continuous_form (f i)) continuous_const)

/-- The measure-theoretic bridge needed to apply a qualitative plank-cover
theorem inside the quantitative minimum argument. -/
theorem gap_area_eq_zero_iff_cover {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (harea : 0 < (volume K).toReal)
    (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal = 0 ↔
      K ⊆ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i} :=
  area_sdiff_eq_zero_iff_subset hK hconv harea (isClosed_plank_union f lo hi)

end Finite

/-- The induction starts with the exact, actual-area zero-plank statement. -/
theorem sharpPlanarBound_zero : SharpPlanarBound 0 := by
  intro K _ _ _ f lo hi _ _
  simp

end Plank.PlanarGapAnalysis
