/- Quantitative uncovered volume from compatible, possibly oblique chords. -/
module

public import Plank.Convex.SelectableChordVolume

@[expose] public section
set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise
open Set MeasureTheory

namespace Plank.MonotoneVolume

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Fintype ι]

/-- Nonnegative interactions give the translation bound without symmetrization
weights. The diagonal step may exceed the band width. -/
theorem measure_core_le_closed_gap (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : ι → E →L[ℝ] ℝ) (hfne : ∀ i, f i ≠ 0)
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i)
    (v : ι → E) (hq : ∀ i j, 0 ≤ f j (v i))
    (hdiag : ∀ i, hi i - lo i ≤ f i (v i))
    (K core : Set E) (hcore : MeasurableSet core)
    (hinside : ∀ s : Finset ι, ∀ t ∈ core, t + s.sum v ∈ K) :
    μ core ≤ μ (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i)) := by
  exact SelectableChordVolume.measure_core_le_closed_gap μ f hfne lo hi hwidth v
    (SideAssignments.of_nonnegative _ (fun i j => hq j i)) hdiag K core hcore hinside

/-- Compatible chord displacements give the sharp chord-relative gap bound.
For support chords their positive functional spans are the body's support widths.
No common endpoint, parallelism, or interaction symmetry is required. -/
theorem measure_gap_ge_of_compatible_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀ i, x i ∈ K) (hy : ∀ i, y i ∈ K)
    (hspan : ∀ i, 0 < f i (x i - y i))
    (hcompat : ∀ i j, 0 ≤ f j (x i - y i))
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) / f i (x i - y i) ≤ 1) :
    (ENNReal.ofReal (1 - ∑ i, (hi i - lo i) / f i (x i - y i))) ^
      Module.finrank ℝ E * μ K ≤
      μ (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i)) := by
  exact SelectableChordVolume.measure_gap_ge_of_chords_le_one μ K hK hKm f x y hx hy hspan
    (SideAssignments.stable_of_nonnegative _ (fun i j => hcompat j i)) lo hi hwidth hsum

/-- The compatible-chord bound for affine coordinates. Shifting each window by
its coordinate's constant term reuses the linear theorem without extra geometry. -/
theorem measure_gap_ge_of_compatible_affine_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀ i, x i ∈ K) (hy : ∀ i, y i ∈ K)
    (hspan : ∀ i, 0 < f i (x i)-f i (y i))
    (hcompat : ∀ i j, 0 ≤ f j (x i)-f j (y i))
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i)
    (hsum : ∑ i, (hi i-lo i)/(f i (x i)-f i (y i)) ≤ 1) :
    (ENNReal.ofReal (1-∑ i, (hi i-lo i)/(f i (x i)-f i (y i)))) ^
      Module.finrank ℝ E * μ K ≤
      μ (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i)) := by
  have h := SelectableChordVolume.measure_gap_ge_of_affine_chords μ K hK hKm f x y hx hy hspan
    (SideAssignments.stable_of_nonnegative _ (fun i j => hcompat j i)) lo hi hwidth
  simpa only [max_eq_right (sub_nonneg.mpr hsum)] using h

theorem area_gap_ge_of_compatible_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hK : Convex ℝ K) (hKm : MeasurableSet K) (hKfin : μ K ≠ ⊤)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀ i, x i ∈ K) (hy : ∀ i, y i ∈ K)
    (hspan : ∀ i, 0 < f i (x i - y i))
    (hcompat : ∀ i j, 0 ≤ f j (x i - y i))
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) / f i (x i - y i) ≤ 1) :
    (1 - ∑ i, (hi i - lo i) / f i (x i - y i)) ^ Module.finrank ℝ E *
      (μ K).toReal ≤
      (μ (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i))).toReal := by
  have hbound := measure_gap_ge_of_compatible_chords μ K hK hKm
    f x y hx hy hspan hcompat lo hi hwidth hsum
  have hgap : μ (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i)) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin (measure_mono Set.sdiff_subset)
  have hreal := ENNReal.toReal_mono hgap hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hsum)] using hreal

end Plank.MonotoneVolume
