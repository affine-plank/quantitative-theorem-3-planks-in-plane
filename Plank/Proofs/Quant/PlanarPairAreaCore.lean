/- Exact full pair-plank areas from elementary affine coordinates. -/
module

public import Plank.Proofs.Quant.PlanarAffineCoordinates
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairArea

open Set MeasureTheory PlanarQuantitative PlanarDirectionDerivatives PlanarPolygonHalfplanes

/-- The planar cross product is the determinant of the affine coordinate map. -/
theorem cross_eq_det (f g : Point →ᵃ[ℝ] ℝ) :
    cross f g = (AffineMap.pi ![f, g]).linear.det := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 2)), Matrix.det_fin_two]
  simp [cross, AffineMap.pi]

/-- A common affine change of variables multiplies the cross product by its determinant. -/
theorem cross_comp (f g : Point →ᵃ[ℝ] ℝ) (T : Point →ᵃ[ℝ] Point) :
    cross (f.comp T) (g.comp T) = cross f g * T.linear.det := by
  rw [cross_eq_det, cross_eq_det]
  have he : (AffineMap.pi ![f.comp T, g.comp T]).linear =
      (AffineMap.pi ![f, g]).linear.comp T.linear := by
    ext x i
    fin_cases i <;> rfl
  rw [he, LinearMap.det_comp]

/-- The standard matrix equivalence for two independent coordinates. -/
def matrixCoordinates (a b c d : ℝ) (h : a*d-b*c ≠ 0) : Point ≃ₗ[ℝ] Point :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) !![a,b;c,d]
    (by simpa [Matrix.det_fin_two] using isUnit_iff_ne_zero.mpr h)

@[simp] theorem matrixCoordinates_apply (a b c d : ℝ) (h : a*d-b*c ≠ 0) (x : Point) :
    matrixCoordinates a b c d h x = ![a*x 0+b*x 1, c*x 0+d*x 1] := by
  simp [matrixCoordinates, Matrix.toLin_eq_toLin', Matrix.toLin'_apply,
    dotProduct, Fin.sum_univ_two]

def pairCoordinates (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0) : Point ≃ₗ[ℝ] Point :=
  matrixCoordinates (f.linear (Pi.single 0 1)) (f.linear (Pi.single 1 1))
    (g.linear (Pi.single 0 1)) (g.linear (Pi.single 1 1)) h

theorem pairCoordinates_first (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0) (x : Point) :
    pairCoordinates f g h x 0 = f x-f 0 := by
  have he := congrFun (matrixCoordinates_apply (f.linear (Pi.single 0 1))
    (f.linear (Pi.single 1 1)) (g.linear (Pi.single 0 1)) (g.linear (Pi.single 1 1)) h x) 0
  change pairCoordinates f g h x 0 = f.linear (Pi.single 0 1)*x 0+
    f.linear (Pi.single 1 1)*x 1 at he
  rw [he, affine_eval_coordinates f x]
  ring

theorem pairCoordinates_second (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0) (x : Point) :
    pairCoordinates f g h x 1 = g x-g 0 := by
  have he := congrFun (matrixCoordinates_apply (f.linear (Pi.single 0 1))
    (f.linear (Pi.single 1 1)) (g.linear (Pi.single 0 1)) (g.linear (Pi.single 1 1)) h x) 1
  change pairCoordinates f g h x 1 = g.linear (Pi.single 0 1)*x 0+
    g.linear (Pi.single 1 1)*x 1 at he
  rw [he, affine_eval_coordinates g x]
  ring

/-- The positive, endpoint-independent coefficient of pair-plank area. -/
def pairCoefficient (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0) : ℝ :=
  areaFactor (pairCoordinates f g h)

theorem pairCoefficient_pos (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0) :
    0 < pairCoefficient f g h := areaFactor_pos _

/-- Two transverse planks are the preimage of their coordinate rectangle. -/
theorem pair_eq_preimage (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0)
    (lo hi lo' hi' : ℝ) :
    {x | lo ≤ f x ∧ f x ≤ hi} ∩ {x | lo' ≤ g x ∧ g x ≤ hi'} =
      pairCoordinates f g h ⁻¹' Icc ![lo-f 0,lo'-g 0] ![hi-f 0,hi'-g 0] := by
  ext x
  simp [mem_Icc, Pi.le_def, Fin.forall_fin_two, pairCoordinates_first,
    pairCoordinates_second, and_and_and_comm]

theorem area_pair (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0)
    (lo hi lo' hi' : ℝ) (horder : lo ≤ hi) (horder' : lo' ≤ hi') :
    (volume ({x | lo ≤ f x ∧ f x ≤ hi} ∩ {x | lo' ≤ g x ∧ g x ≤ hi'})).toReal =
      pairCoefficient f g h*(hi-lo)*(hi'-lo') := by
  let a : Point := ![lo-f 0, lo'-g 0]
  let b : Point := ![hi-f 0, hi'-g 0]
  have hab : a ≤ b := by
    intro i
    fin_cases i <;> dsimp [a, b] <;> linarith
  rw [pair_eq_preimage f g h, area_preimage, Real.volume_Icc_pi_toReal hab]
  simp only [Fin.prod_univ_two, a, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  dsimp [pairCoefficient]
  ring

/-- Two transverse planar windows have a compact full intersection. -/
theorem compact_pair (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0)
    (lo hi lo' hi' : ℝ) :
    IsCompact ({x | lo ≤ f x ∧ f x ≤ hi} ∩ {x | lo' ≤ g x ∧ g x ≤ hi'}) := by
  rw [pair_eq_preimage f g h]
  exact (pairCoordinates f g h).toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr
    isCompact_Icc

end Plank.PlanarPairArea
