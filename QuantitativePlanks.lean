/- Affine plank inequalities for three planks in the plane and two planks
in every dimension. No compactness or boundedness assumption is needed. -/
module
public import QuantitativePlanks.Extensions.Interface
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace QuantitativePlanks
open MeasureTheory
open scoped BigOperators ENNReal

/-- Real coordinate space of dimension `d`; `Point 2` is the plane. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- A plank represented by a nonconstant affine function. -/
abbrev Plank (d : ℕ) :=
  {f : Point d →ᵃ[ℝ] ℝ // ∃ x y, f x ≠ f y}

/-- Its points lie between the parallel levels where the function is 0 and 1. -/
instance {d : ℕ} : Coe (Plank d) (Set (Point d)) :=
  ⟨fun P => {x | 0 ≤ P.val x ∧ P.val x ≤ 1}⟩

/-- Plank width divided by body width in the same direction.
`ediam` permits infinite widths; division and subtraction use nonnegative
extended reals, so `1 - R` is zero when `R ≥ 1`. -/
def relativeWidth {d : ℕ} (K : Set (Point d)) (P : Plank d) : ℝ≥0∞ :=
  1 / Metric.ediam (P.val '' K)

/-- APC: three planks covering a convex planar set have total relative width ≥ 1. -/
theorem planar_cover (K : Set (Point 2)) (convex : Convex ℝ K)
    (P : Fin 3 → Plank 2) (covers : K ⊆ ⋃ i, (P i : Set (Point 2))) :
    1 ≤ ∑ i, relativeWidth K (P i) := by
  exact _root_.Plank.AffinePlankBounds.planar_cover K convex (fun i => (P i).val) covers

/-- QAPC for three planar planks: uncovered area ≥ (1 − total relative width)²
 times the body's area, with the deficit truncated at zero. -/
theorem planar_quantitative (K : Set (Point 2)) (convex : Convex ℝ K)
    (P : Fin 3 → Plank 2) :
    (1 - ∑ i, relativeWidth K (P i))^2 * volume K ≤
      volume (K \ ⋃ i, (P i : Set (Point 2))) := by
  exact _root_.Plank.AffinePlankBounds.planar_quantitative K convex
    (fun i => (P i).val) (fun i => (P i).property)

/-- QAPC for two planks in dimension `d`, with exponent `d`. -/
theorem two_planks (d : ℕ) (K : Set (Point d)) (convex : Convex ℝ K)
    (P : Fin 2 → Plank d) :
    (1 - ∑ i, relativeWidth K (P i))^d * volume K ≤
      volume (K \ ⋃ i, (P i : Set (Point d))) := by
  exact _root_.Plank.AffinePlankBounds.two_planks d K convex
    (fun i => (P i).val) (fun i => (P i).property)

end QuantitativePlanks
