/- Elementary affine coordinates and planar area transport. -/
module

public import Plank.Proofs.Quant.PlanarStatement
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Plank.PlanarQuantitative

namespace Plank.PlanarPolygonHalfplanes

/-- The coefficients used above are the actual coefficients of an affine
functional on the plane, in the coordinate convention of the final target. -/
theorem affine_eval_coordinates (f : Point →ᵃ[ℝ] ℝ) (x : Point) :
    f x = f.linear (Pi.single 0 1)*x 0 + f.linear (Pi.single 1 1)*x 1 + f 0 := by
  rw [congrFun f.decomp x]
  have h := congrArg f.linear ((Pi.basisFun ℝ (Fin 2)).sum_repr x)
  simpa [map_sum, Pi.basisFun_apply, Pi.basisFun_repr, Fin.sum_univ_two, mul_comm] using
    congrArg (fun y => y + f 0) h.symm

end Plank.PlanarPolygonHalfplanes

namespace Plank.PlanarDirectionDerivatives

/-- The signed determinant of the two affine forms' linear parts. -/
def cross (f g : Point →ᵃ[ℝ] ℝ) : ℝ :=
  f.linear (Pi.single 0 1)*g.linear (Pi.single 1 1) -
    f.linear (Pi.single 1 1)*g.linear (Pi.single 0 1)

/-- The fixed area factor for changing linear coordinates. -/
def areaFactor (T : Point ≃ₗ[ℝ] Point) : ℝ :=
  |LinearMap.det (T.symm : Point →ₗ[ℝ] Point)|

theorem areaFactor_pos (T : Point ≃ₗ[ℝ] Point) : 0 < areaFactor T :=
  abs_pos.mpr T.symm.isUnit_det'.ne_zero

theorem area_preimage (T : Point ≃ₗ[ℝ] Point) (S : Set Point) :
    (volume (T ⁻¹' S)).toReal = areaFactor T*(volume S).toReal := by
  rw [Measure.addHaar_preimage_linearEquiv volume T S, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

end Plank.PlanarDirectionDerivatives
