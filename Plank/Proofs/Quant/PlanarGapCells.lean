/- Actual affine-plank gap cells and their area decomposition.
Closed cells agree in area with a disjoint partition of the uncovered set,
including zero-width planks and repeated directions. -/
module

public import Plank.Proofs.Quant.PlanarCellArea
public import Plank.Measure.LinearBands
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarGapCells

open Set MeasureTheory PlanarQuantitative PlanarCellArea
open Plank.Convex.DeficientHeightTilt

variable {ι : Type*}

/-- The closed exterior cell with upper sides selected by `s`. -/
def signCell (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (s : Finset ι) : Set Point :=
  K ∩ LinearBands.weakCell (fun i x => f i x) lo hi s

/-- Fixed outward linear forms for one sign pattern. -/
def cutForms (f : ι → Point →ᵃ[ℝ] ℝ) (s : Finset ι) : ι → Point →L[ℝ] ℝ := by
  classical
  exact fun i => if i ∈ s then -(f i).linear.toContinuousLinearMap
    else (f i).linear.toContinuousLinearMap

/-- Affine offsets identifying the exterior cell with the half-plane model. -/
def cutOffsets (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (s : Finset ι) : ι → ℝ := by
  classical
  exact fun i => if i ∈ s then f i 0 - hi i else lo i - f i 0

theorem affine_eval (f : Point →ᵃ[ℝ] ℝ) (x : Point) :
    f x = f.linear x + f 0 := congrFun f.decomp x

theorem continuous_form (f : Point →ᵃ[ℝ] ℝ) : Continuous f :=
  FiniteDimensionalCapWindowScaling.continuous_form f

theorem signCell_eq_cell (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (s : Finset ι) :
    signCell K f lo hi s = cell K (cutForms f s) (cutOffsets f lo hi s) :=
  FiniteDimensionalEndpointMajorants.signCell_eq_cell K f (lo, hi) s

theorem isCompact_signCell {K : Set Point} (hK : IsCompact K)
    (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (s : Finset ι) :
    IsCompact (signCell K f lo hi s) :=
  FiniteDimensionalFewCellScaling.isCompact_signCell hK f (lo, hi) s

theorem convex_signCell {K : Set Point} (hK : Convex ℝ K)
    (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (s : Finset ι) :
    Convex ℝ (signCell K f lo hi s) := by
  rw [signCell_eq_cell]
  exact convex_cell hK _ _

/-- The nondegeneracy required by the actual-area target makes every affine
level a null set. No pairwise independence of directions is required. -/
theorem linear_ne_zero_of_rangeWidth_pos {K : Set Point} (hK : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (hwidth : 0 < rangeWidth K f) : f.linear ≠ 0 :=
  Body.linear_ne_zero_of_width_pos hK f hwidth

theorem measure_level_zero (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) :
    volume {x | f x = c} = 0 :=
  FiniteDimensionalCapWindowScaling.measure_level_zero f hf c

section Finite

variable [Fintype ι]

/-- The actual closed-plank gap is the union of its strict sign cells. -/
theorem gap_eq_iUnion_strictCells (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) :
    K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i) =
      ⋃ s : Finset ι, K ∩ LinearBands.strictCell (fun i x => f i x) lo hi s :=
  FiniteDimensionalFewCellScaling.gap_eq_iUnion_strictCells K f lo hi

/-- Closing the sides of one cell does not change its area. This remains true
when some plank widths vanish and when two normals coincide. -/
theorem measure_strict_eq_signCell (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (lo hi : ι → ℝ) (s : Finset ι) :
    volume (K ∩ LinearBands.strictCell (fun i x => f i x) lo hi s) =
      volume (signCell K f lo hi s) :=
  FiniteDimensionalFewCellScaling.measure_strict_eq_signCell K f hf lo hi s

/-- The sum of actual closed-cell areas is exactly the uncovered area.
Disjointness is proved for the strict cells; null affine levels justify closing
them even for zero-width planks. -/
theorem measure_gap_eq_sum_signCells {K : Set Point} (hK : MeasurableSet K)
    (f : ι → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    volume (K \ ⋃ i, LinearBands.closedBand (f i) (lo i) (hi i)) =
      ∑ s : Finset ι, volume (signCell K f lo hi s) :=
  FiniteDimensionalFewCellScaling.measure_gap_eq_sum_signCells hK f hf lo hi hwidth

/-- Real-valued area version of the exact cell decomposition. The hypotheses
use the actual directional widths from the final planar statement. -/
theorem area_gap_eq_sum_signCells {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : ι → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < rangeWidth K (f i))
    (lo hi : ι → ℝ) (hwidth : ∀ i, lo i ≤ hi i) :
    (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal =
      ∑ s : Finset ι, (volume (signCell K f lo hi s)).toReal := by
  have heq := measure_gap_eq_sum_signCells hK.measurableSet f
    (fun i => linear_ne_zero_of_rangeWidth_pos hne (f i) (hf i)) lo hi hwidth
  exact (congrArg ENNReal.toReal heq).trans (ENNReal.toReal_sum
    (fun s _ => (isCompact_signCell hK f lo hi s).measure_ne_top))

end Finite

/-- The linear change in the offsets caused by moving both plank endpoints. -/
def cutDirection (dlo dhi : ι → ℝ) (s : Finset ι) : ι → ℝ := by
  classical
  exact fun i => if i ∈ s then -dhi i else dlo i

theorem cutOffsets_motion (f : ι → Point →ᵃ[ℝ] ℝ)
    (lo hi dlo dhi : ι → ℝ) (s : Finset ι) (t : ℝ) :
    cutOffsets f (lo + t • dlo) (hi + t • dhi) s =
      cutOffsets f lo hi s + t • cutDirection dlo dhi s :=
  FiniteDimensionalEndpointMajorants.cutOffsets_motion f s (lo, hi) (dlo, dhi) t

end Plank.PlanarGapCells
