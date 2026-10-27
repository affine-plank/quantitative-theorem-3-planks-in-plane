/- Measurability and Haar volume of the convex chord seed, in any finite-dimensional
real normed space. The existing BangVolume names remain available to callers. -/
module

public import Plank.Convex.ChordSeed
public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped BigOperators Pointwise
open Set MeasureTheory

namespace Plank.BangVolume

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Fintype ι]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem chordSeed_eq_image (K : Set E) (ρ : ι → ℝ) (y : ι → E) :
    Plank.Convex.chordSeed K ρ y =
      (fun z => z + ∑ i, ρ i • y i) '' ((1 - ∑ i, ρ i) • K) := by
  unfold Plank.Convex.chordSeed
  rw [← Set.image_smul, Set.image_image]
  congr 1
  funext z
  exact add_comm _ _

theorem measurableSet_chordSeed {K : Set E} (hK : MeasurableSet K)
    (ρ : ι → ℝ) (y : ι → E) :
    MeasurableSet (Plank.Convex.chordSeed K ρ y) := by
  rw [chordSeed_eq_image]
  exact (measurableEmbedding_addRight _).measurableSet_image'
    (hK.const_smul₀ (1 - ∑ i, ρ i))

/-- The convex seed has the expected homothetic volume, including zero deficit. -/
theorem measure_chordSeed (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (ρ : ι → ℝ) (y : ι → E) (hsum : ∑ i, ρ i ≤ 1) :
    μ (Plank.Convex.chordSeed K ρ y) =
      (ENNReal.ofReal (1 - ∑ i, ρ i)) ^ Module.finrank ℝ E * μ K := by
  rw [chordSeed_eq_image]
  change μ ((MeasurableEquiv.addRight (∑ i, ρ i • y i)) ''
    ((1 - ∑ i, ρ i) • K)) = _
  rw [MeasurableEquiv.image_eq_preimage_symm]
  change μ ((fun z => z + -(∑ i, ρ i • y i)) ⁻¹'
    ((1 - ∑ i, ρ i) • K)) = _
  rw [measure_preimage_add_right, μ.addHaar_smul_of_nonneg (sub_nonneg.mpr hsum),
    ENNReal.ofReal_pow (sub_nonneg.mpr hsum)]

end Plank.BangVolume
