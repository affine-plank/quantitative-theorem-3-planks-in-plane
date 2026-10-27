/- Quantitative volume from chords with positively symmetrizable interactions.
The ambient space is normed; the chord directions need not be cut normals. -/
module

public import Plank.Convex.BangMap
public import Plank.Convex.SelectableChordVolume

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SymmetricChordVolume

open Set MeasureTheory
open scoped BigOperators Pointwise

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Fintype ι]

/-- Positive window widths scale a chord symmetrizer into a step symmetrizer. -/
theorem measure_gap_ge_of_symmetric_chords_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i-y i))
    (a : ι → ℝ) (ha : ∀i,0<a i)
    (hsym : ∀i j,a i*f i (x j-y j)=a j*f j (x i-y i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i<hi i)
    (hsum : ∑i,(hi i-lo i)/f i (x i-y i)≤1) :
    (ENNReal.ofReal (1-∑i,(hi i-lo i)/f i (x i-y i)))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  exact SelectableChordVolume.measure_gap_ge_of_chords_le_one μ K hc hm f x y hx hy hspan
    (SideAssignments.stable_of_weighted_symmetry _ a ha hsym) lo hi (fun i => (ho i).le) hsum

/-- Arbitrary ordered windows, zero widths and exhausted budgets are included.
Positive symmetrizing weights are an explicit hypothesis on the original chords. -/
theorem measure_gap_ge_of_symmetric_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i-y i))
    (a : ι → ℝ) (ha : ∀i,0<a i)
    (hsym : ∀i j,a i*f i (x j-y j)=a j*f j (x i-y i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) :
    (ENNReal.ofReal (max 0 (1-∑i,(hi i-lo i)/f i (x i-y i))))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  exact SelectableChordVolume.measure_gap_ge_of_chords μ K hc hm f x y hx hy hspan
    (SideAssignments.stable_of_weighted_symmetry _ a ha hsym) lo hi ho

/-- Shifting each window by the affine constant preserves every chord interaction. -/
theorem measure_gap_ge_of_symmetric_affine_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i)-f i (y i))
    (a : ι → ℝ) (ha : ∀i,0<a i)
    (hsym : ∀i j,a i*(f i (x j)-f i (y j))=a j*(f j (x i)-f j (y i)))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) :
    (ENNReal.ofReal (max 0 (1-∑i,(hi i-lo i)/(f i (x i)-f i (y i)))))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  exact SelectableChordVolume.measure_gap_ge_of_affine_chords μ K hc hm f x y hx hy hspan
    (SideAssignments.stable_of_weighted_symmetry _ a ha hsym) lo hi ho

end Plank.SymmetricChordVolume
