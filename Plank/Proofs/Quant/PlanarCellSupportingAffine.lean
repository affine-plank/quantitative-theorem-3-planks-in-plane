/- Supporting affine bounds for actual cells without polynomial charts. -/
module

public import Plank.Proofs.Quant.ConcaveSupportingAffine
public import Plank.Proofs.Quant.PlanarInactiveCellMotion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellSupportingAffine

open Set MeasureTheory PlanarQuantitative PlanarCellArea PlanarInactiveCellMotion
open scoped Topology

variable {κ : Type*} [Fintype κ]

/-- One point satisfying all cuts strictly puts the offsets in the interior
of the feasible offset set. -/
theorem interior_of_strict_feasible {K : Set Point} (f : κ → Point →L[ℝ] ℝ)
    (u : κ → ℝ) (x : Point) (hx : x ∈ K) (hstrict : ∀ i, f i x < u i) :
    u ∈ interior {v | (cell K f v).Nonempty} :=
  FiniteDimensionalCellSupportingAffine.interior_of_strict_feasible f u x hx hstrict

/-- A positive-area cell contains a point outside every cut boundary,
so its offsets are interior feasible parameters. -/
theorem interior_of_area_pos {K : Set Point} (f : κ → Point →L[ℝ] ℝ)
    (hf : ∀ i, f i ≠ 0) (u : κ → ℝ) (hpos : 0 < (volume (cell K f u)).toReal) :
    u ∈ interior {v | (cell K f v).Nonempty} :=
  FiniteDimensionalCellSupportingAffine.interior_of_volume_pos f hf u hpos

/-- Interior feasible offsets give positive area, by first tightening all
cuts slightly and then applying the actual relaxation-area theorem. -/
theorem area_pos_of_interior {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : κ → Point →L[ℝ] ℝ) (u : κ → ℝ)
    (hu : u ∈ interior {v | (cell K f v).Nonempty}) :
    0 < (volume (cell K f u)).toReal :=
  FiniteDimensionalCellSupportingAffine.volume_pos_of_interior hK hconv hV f u hu

/-- At a positive cell, square-root area admits a global affine majorant
on all nonempty cells. No chart or differentiability premise is used. -/
theorem exists_sqrt_majorant {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →L[ℝ] ℝ) (hf : ∀ i, f i ≠ 0) (u : κ → ℝ)
    (hpos : 0 < (volume (cell K f u)).toReal) :
    ∃ L : (κ → ℝ) →L[ℝ] ℝ, ∀ v, (cell K f v).Nonempty →
      Real.sqrt (volume (cell K f v)).toReal ≤
        Real.sqrt (volume (cell K f u)).toReal+L (v-u) := by
  simpa [FiniteDimensionalCapWindowScaling.volumeRoot, Real.sqrt_eq_rpow,
    cell,FiniteDimensionalCellSupportingAffine.cell] using
    FiniteDimensionalCellSupportingAffine.exists_root_majorant hK hconv f hf u hpos

/-- A zero-area cell, including a nonempty degenerate cell on an initial
chart wall, has a linear constraint preserving zero area on the whole line.
This removes the need to assume that the base cell is empty. -/
theorem exists_zero_area_constraint {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal) (f : κ → Point →L[ℝ] ℝ)
    (hf : ∀ i, f i ≠ 0) (u : κ → ℝ) (hzero : (volume (cell K f u)).toReal = 0) :
    ∃ L : (κ → ℝ) →L[ℝ] ℝ, L ≠ 0 ∧ ∀ z, L z = 0 → ∀ t : ℝ,
      (volume (cell K f (u+t • z))).toReal = 0 :=
  FiniteDimensionalCellSupportingAffine.exists_zero_volume_constraint hK hconv hne hV f hf u hzero

end Plank.PlanarCellSupportingAffine

/-- info: 'Plank.PlanarCellSupportingAffine.exists_sqrt_majorant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCellSupportingAffine.exists_sqrt_majorant
/-- info: 'Plank.PlanarCellSupportingAffine.exists_zero_area_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCellSupportingAffine.exists_zero_area_constraint
