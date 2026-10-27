/- A common minimizing point gives the sharp volume bound for any finite
family. This is the monotone compatible-chord argument in arbitrary dimension. -/
module

public import Plank.Convex.MonotoneVolume

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.CommonMinimumVolume

open Set MeasureTheory
open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- Normalized affine coordinates with a common zero and attained value one
give a translated homothetic seed. Plank positions are unrestricted. -/
theorem bound (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (z : E) (hz : z∈K)
    (hzero : ∀ i, f i z=0) (hpos : ∀ i x, x∈K → 0≤f i x)
    (htop : ∀ i, ∃ x∈K, f i x=1)
    (lo hi : ι → ℝ) (horder : ∀ i, lo i≤hi i)
    (hR : ∑ i, (hi i-lo i)≤1) :
    (ENNReal.ofReal (1-∑ i, (hi i-lo i)))^Module.finrank ℝ E*μ K ≤
      μ (K \ ⋃ i, {x | lo i≤f i x ∧ f i x≤hi i}) := by
  classical
  choose q hq hqone using htop
  have hb := MonotoneVolume.measure_gap_ge_of_compatible_affine_chords μ K hconv
    hK.measurableSet f q (fun _ => z) hq (fun _ => hz)
    (by intro i; simp only [hqone, hzero, sub_zero, zero_lt_one])
    (fun i j => by simpa only [hzero, sub_zero] using hpos j (q i) (hq i))
    lo hi horder (by simpa only [hqone, hzero, sub_zero, div_one] using hR)
  simpa only [hqone, hzero, sub_zero, div_one, LinearBands.closedBand] using hb

end Plank.CommonMinimumVolume
