/- A genuine planar three-coordinate chart has no constant affine
combination of just two coordinates when the third plane coefficient is nonzero. -/
module
public import Plank.Convex.SameSignCapAlgebra
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.PlanarCoordinateIndependence

open SameSignCapAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- No two-coordinate support cut is identically zero in a two-dimensional
injective chart with all three plane coefficients nonzero. -/
theorem nonzero_pair_cut (hdim : Module.finrank ℝ E = 2)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (A : Point) (D : ℝ)
    (hA : ∀ i, A i ≠ 0) (hplane : ∀ x, ∑ i, A i * f i x = D)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (i : Fin 3) (t c : ℝ) (ht : t ≠ 0) :
    ∃ x, c - (f i x + t * f (next i) x) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hpair (x : E) : f i x + t * f (next i) x = c := by
    have h := hn x
    linarith only [h]
  have hfi : Function.Injective (f i) := by
    intro x y hxy
    have hxpair := hpair x
    have hypair := hpair y
    have hnext : f (next i) x = f (next i) y := by
      have he : t * (f (next i) x - f (next i) y) = 0 := by
        nlinarith only [hxpair, hypair, hxy]
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ht)
    have hx : A i * f i x + A (next i) * f (next i) x + A (prev i) * f (prev i) x = D := by
      calc
        _ = ∑ j, A j * f j x := (sum_cycle (fun j => A j * f j x) i).symm
        _ = D := hplane x
    have hy : A i * f i y + A (next i) * f (next i) y + A (prev i) * f (prev i) y = D := by
      calc
        _ = ∑ j, A j * f j y := (sum_cycle (fun j => A j * f j y) i).symm
        _ = D := hplane y
    have hprev : f (prev i) x = f (prev i) y := by
      rw [hxy, hnext] at hx
      have he : A (prev i) * (f (prev i) x - f (prev i) y) = 0 := by
        nlinarith only [hx, hy]
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hA _))
    apply hinj
    funext j
    rcases index_cases i j with rfl | rfl | rfl
    · exact hxy
    · exact hnext
    · exact hprev
  have hdimle := LinearMap.finrank_le_finrank_of_injective ((f i).linear_injective_iff.mpr hfi)
  norm_num [hdim] at hdimle

end Plank.Convex.PlanarTight.PlanarCoordinateIndependence

/-- info: 'Plank.Convex.PlanarTight.PlanarCoordinateIndependence.nonzero_pair_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.PlanarCoordinateIndependence.nonzero_pair_cut
