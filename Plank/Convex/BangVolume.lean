/- Quantitative uncovered volume from realized parallel chords. -/
module

public import Plank.Convex.SymmetricChordVolume
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section
set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise RealInnerProductSpace
open Set MeasureTheory

namespace Plank.BangVolume

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Fintype ι]

/-- A finite family of positive-width planks leaves at least the chord-deficit
power of the body's volume uncovered. The denominators are lengths of realized
parallel chords, not directional support widths. -/
theorem measure_gap_ge_of_realized_chords_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (u x y : ι → E) (L lo hi : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hL : ∀ i, 0 < L i)
    (hx : ∀ i, x i ∈ K) (hy : ∀ i, y i ∈ K)
    (hchord : ∀ i, x i - y i = L i • u i)
    (hwidth : ∀ i, lo i < hi i)
    (hsum : ∑ i, (hi i - lo i) / L i ≤ 1) :
    (ENNReal.ofReal (1 - ∑ i, (hi i - lo i) / L i)) ^ Module.finrank ℝ E * μ K ≤
      μ (K \ ⋃ i, LinearBands.closedBand (fun z => ⟪u i, z⟫) (lo i) (hi i)) := by
  let f (i : ι) := innerSL ℝ (u i)
  have hspan (i : ι) : f i (x i-y i)=L i := by
    simp only [f,hchord i,innerSL_apply_apply,inner_smul_right,
      real_inner_self_eq_norm_sq,hu i,one_pow,mul_one]
  have hsym (i j : ι) : L i*f i (x j-y j)=L j*f j (x i-y i) := by
    simp only [f,hchord,innerSL_apply_apply,inner_smul_right]
    rw [real_inner_comm (u j) (u i)]
    ring
  have h := SymmetricChordVolume.measure_gap_ge_of_symmetric_chords_pos μ K hK hKm
    f x y hx hy (by simpa only [hspan] using hL) L hL hsym lo hi hwidth
    (by simpa only [hspan] using hsum)
  simpa only [hspan,f,coe_innerSL_apply] using h

/-- The chord-relative quantitative plank bound, for any finite family of
closed planks, with zero widths and exhausted budgets included. -/
theorem measure_gap_ge_of_realized_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (u x y : ι → E) (L lo hi : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hL : ∀ i, 0 < L i)
    (hx : ∀ i, x i ∈ K) (hy : ∀ i, y i ∈ K)
    (hchord : ∀ i, x i - y i = L i • u i)
    (hwidth : ∀ i, lo i ≤ hi i) :
    (ENNReal.ofReal (max 0 (1 - ∑ i, (hi i - lo i) / L i))) ^
      Module.finrank ℝ E * μ K ≤
      μ (K \ ⋃ i, LinearBands.closedBand (fun z => ⟪u i, z⟫) (lo i) (hi i)) := by
  let f (i : ι) := innerSL ℝ (u i)
  have hspan (i : ι) : f i (x i-y i)=L i := by
    simp only [f,hchord i,innerSL_apply_apply,inner_smul_right,
      real_inner_self_eq_norm_sq,hu i,one_pow,mul_one]
  have hsym (i j : ι) : L i*f i (x j-y j)=L j*f j (x i-y i) := by
    simp only [f,hchord,innerSL_apply_apply,inner_smul_right]
    rw [real_inner_comm (u j) (u i)]
    ring
  have h := SymmetricChordVolume.measure_gap_ge_of_symmetric_chords μ K hK hKm
    f x y hx hy (by simpa only [hspan] using hL) L hL hsym lo hi hwidth
  simpa only [hspan,f,coe_innerSL_apply] using h

end Plank.BangVolume
