/- Square-root concavity of actual planar convex-cell areas.
Brunn--Minkowski is proved by the imported development, not an assumption.
Quadratic area charts and the final uncovered-area theorem remain separate. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Proofs.Quant.PlanarStatement
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellArea

open Set MeasureTheory PlanarQuantitative
open scoped Pointwise

/-- Brunn--Minkowski in dimension two, expressed using ordinary real areas. -/
theorem sqrt_area_add {A B : Set Point}
    (hA : IsCompact A) (hB : IsCompact B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    Real.sqrt (volume A).toReal + Real.sqrt (volume B).toReal ≤
      Real.sqrt (volume (A + B)).toReal := by
  simpa [FiniteDimensionalCapWindowScaling.volumeRoot, Real.sqrt_eq_rpow] using
    (FiniteDimensionalCapWindowScaling.volumeRoot_add (d := 1) hA hB hneA hneB)

/-- Nonnegative homotheties scale square-root area by their ratio, including
the zero ratio and sets of zero area. -/
theorem sqrt_area_smul (A : Set Point) (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (volume (a • A)).toReal = a * Real.sqrt (volume A).toReal := by
  simpa [FiniteDimensionalCapWindowScaling.volumeRoot, Real.sqrt_eq_rpow] using
    (FiniteDimensionalCapWindowScaling.volumeRoot_smul (d := 1) A a ha)

/-- The weighted planar Brunn--Minkowski inequality for actual compact sets.
Convexity is not needed for this theorem. -/
theorem sqrt_area_smul_add {A B : Set Point}
    (hA : IsCompact A) (hB : IsCompact B)
    (hneA : A.Nonempty) (hneB : B.Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * Real.sqrt (volume A).toReal + b * Real.sqrt (volume B).toReal ≤
      Real.sqrt (volume (a • A + b • B)).toReal := by
  simpa [FiniteDimensionalCapWindowScaling.volumeRoot, Real.sqrt_eq_rpow] using
    (FiniteDimensionalCapWindowScaling.volumeRoot_smul_add (d := 1) hA hB hneA hneB a b ha hb)

/-- A body cut by fixed linear half-planes whose offsets vary. Fixing a sign
pattern for the plank gaps gives precisely a family of this form. -/
def cell {ι : Type*} (K : Set Point) (f : ι → Point →L[ℝ] ℝ)
    (u : ι → ℝ) : Set Point :=
  K ∩ ⋂ i, {x | f i x ≤ u i}

theorem isCompact_cell {ι : Type*} {K : Set Point} (hK : IsCompact K)
    (f : ι → Point →L[ℝ] ℝ) (u : ι → ℝ) : IsCompact (cell K f u) :=
  FiniteDimensionalCellSupportingAffine.isCompact_cell hK f u

theorem convex_cell {ι : Type*} {K : Set Point} (hK : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) (u : ι → ℝ) : Convex ℝ (cell K f u) :=
  FiniteDimensionalCellSupportingAffine.convex_cell hK f u

/-- Interpolated points from two cells lie in the cell at the interpolated
offsets. This is an inclusion between the actual subsets of the plane. -/
theorem smul_cell_add_subset {ι : Type*} {K : Set Point} (hK : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) (u v : ι → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • cell K f u + b • cell K f v ⊆ cell K f (a • u + b • v) :=
  FiniteDimensionalCellSupportingAffine.smul_cell_add_subset hK f u v a b ha hb hab

/-- The parameters for which the actual cut-out cell is nonempty form a
convex set. No positivity of an individual cell area is assumed. -/
theorem convex_feasible {ι : Type*} {K : Set Point} (hK : Convex ℝ K)
    (f : ι → Point →L[ℝ] ℝ) :
    Convex ℝ {u | (cell K f u).Nonempty} :=
  FiniteDimensionalCellSupportingAffine.convex_feasible hK f

/-- Square-root area of actual convex cells is concave on the feasible
offset domain. Brunn--Minkowski and the geometric inclusion are discharged
inside the proof. Degenerate nonempty cells are allowed. -/
theorem concaveOn_sqrt_area_cell {ι : Type*} {K : Set Point}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : ι → Point →L[ℝ] ℝ) :
    ConcaveOn ℝ {u | (cell K f u).Nonempty}
      (fun u => Real.sqrt (volume (cell K f u)).toReal) := by
  simpa [FiniteDimensionalCapWindowScaling.volumeRoot, Real.sqrt_eq_rpow,
    cell,FiniteDimensionalCellSupportingAffine.cell] using
    FiniteDimensionalCellSupportingAffine.concaveOn_volumeRoot_cell hK hconv f

end Plank.PlanarCellArea
