/- The directional range used by the affine plank statements. -/
module
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Body
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The range of an affine functional on a set. -/
def width (K : Set E) (f : E →ᵃ[ℝ] ℝ) : ℝ := sSup (f '' K) - sInf (f '' K)

/-- Positive actual width excludes a constant affine form, without topology. -/
theorem linear_ne_zero_of_width_pos {K : Set E} (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (hwidth : 0 < width K f) : f.linear ≠ 0 := by
  intro h
  obtain ⟨c,rfl⟩ := f.linear_eq_zero_iff_exists_const.mp h
  have himage : (AffineMap.const ℝ E c) '' K = {c} := hne.image_const c
  rw [width, himage] at hwidth
  simp at hwidth

end Plank.Body

namespace Plank.Convex.DeficientHeightTilt

/-- Compatibility name for the common affine width. -/
abbrev rangeWidth {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (f : E →ᵃ[ℝ] ℝ) : ℝ := Body.width K f

end Plank.Convex.DeficientHeightTilt
