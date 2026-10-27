/- Apply the normalized three-plank bound directly in the Euclidean plane. -/
module
public import Plank.Convex.ThreePlankPlaneReduction
public import Plank.Convex.AffineRangeInterior
public import Plank.Core
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarConjectureBridge
open scoped BigOperators RealInnerProductSpace
open Plank.Convex.DeficientHeightTilt (rangeWidth)

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The normalized bound applies directly in the Euclidean plane. -/
theorem conjectureFor_three_of_normalized
    (h : ThreePlankPlaneReduction.NormalizedPlaneClaim) : Bang.ConjectureFor E2 3 := by
  intro K hint u lo hi hu hw hcover
  let f : Fin 3 → E2 →ᵃ[ℝ] ℝ :=
    fun i => (innerSLFlip ℝ (u i)).toLinearMap.toAffineMap
  have hW (i : Fin 3) : 0 < rangeWidth (K : Set _) (f i) := by
    apply AffineRangeInterior.positive_width (K : Set _) hint (f i) ?_
      (K.isCompact.image (f i).continuous_of_finiteDimensional).isBounded
    refine ⟨u i, 0, ?_⟩
    change ⟪u i, u i⟫ ≠ ⟪0, u i⟫
    simpa only [inner_zero_left] using (inner_self_ne_zero.mpr (hu i))
  have hb := ThreePlankPlaneReduction.bound_of_finrank_le_two (by simp) h (K : Set _) K.isCompact
    K.nonempty K.convex f lo hi hW hw (fun x hx => Set.mem_iUnion.mp (hcover hx))
  exact hb

end Plank.Convex.PlanarConjectureBridge

/-- info: 'Plank.Convex.PlanarConjectureBridge.conjectureFor_three_of_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarConjectureBridge.conjectureFor_three_of_normalized
