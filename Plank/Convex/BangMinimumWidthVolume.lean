/- The Euclidean quantitative plank bound from minimum-width chords. -/
module

public import Plank.Convex.BangVolume
public import Plank.Convex.MinimumWidthChords

@[expose] public section
set_option autoImplicit false

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set MeasureTheory

namespace Plank.BangVolume

/-- In every finite dimension, a finite family of closed planks leaves at least
the minimum-width deficit power of the body's volume uncovered. The total width
here is the ordinary Euclidean sum of plank widths. -/
theorem measure_gap_ge_of_minWidth
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    [Fintype ι] (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) (hW : 0 < minWidth (K : Set E))
    (u : ι → E) (hu : ∀ i, ‖u i‖ = 1)
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    (ENNReal.ofReal (max 0
      (1 - (∑ i, (hi i - lo i)) / minWidth (K : Set E)))) ^
      Module.finrank ℝ E * μ (K : Set E) ≤
      μ ((K : Set E) \ ⋃ i,
        LinearBands.closedBand (fun z => ⟪u i, z⟫) (lo i) (hi i)) := by
  classical
  choose x hx y hy hxy using fun i => Plank.Convex.exists_minWidth_chord K (u i) (hu i)
  have h := measure_gap_ge_of_realized_chords μ (K : Set E) K.convex'
    K.isCompact.measurableSet u x y (fun _ => minWidth (K : Set E)) lo hi
    hu (fun _ => hW) hx hy hxy hwidth
  simpa only [← Finset.sum_div] using h

end Plank.BangVolume
