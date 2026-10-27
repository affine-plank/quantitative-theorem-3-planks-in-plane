/- Four exterior corner witnesses force full pair-plank containment. -/
module

public import Plank.Proofs.Quant.PlanarPairAreaCore
public import Mathlib.Analysis.LocallyConvex.Separation
public import ResearchFormalized.Convex.OrthantWitnesses

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairContainment

open Set MeasureTheory PlanarQuantitative PlanarDirectionDerivatives
open PlanarPolygonHalfplanes PlanarPairArea

/-- Every linear functional is a linear combination of two transverse
affine coordinates after subtracting their constants. -/
theorem exists_coefficients (f g : Point →ᵃ[ℝ] ℝ) (hcross : cross f g ≠ 0)
    (L : Point →L[ℝ] ℝ) : ∃ a b : ℝ, ∀ x, L x = a*(f x-f 0)+b*(g x-g 0) := by
  let T := pairCoordinates f g hcross
  let M := L.toLinearMap.comp T.symm.toLinearMap
  refine ⟨M (Pi.single 0 1), M (Pi.single 1 1), fun x => ?_⟩
  have hL : M (T x) = M (Pi.single 0 1)*(T x) 0+M (Pi.single 1 1)*(T x) 1 := by
    simpa using affine_eval_coordinates M.toAffineMap (T x)
  change L (T.symm (T x)) = _ at hL
  simpa only [T, LinearEquiv.symm_apply_apply, pairCoordinates_first,
    pairCoordinates_second] using hL

/-- A closed convex body with a point beyond each of a pair-plank
parallelogram's four corners contains that entire parallelogram. The
witnesses may be on their corner boundaries. -/
theorem pair_subset_of_corners {K : Set Point} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (f g : Point →ᵃ[ℝ] ℝ) (hcross : cross f g ≠ 0) (lo hi lo' hi' : ℝ)
    (hcorners : ∀ b c : Bool, ∃ x ∈ K,
      (if b then hi ≤ f x else f x ≤ lo) ∧ (if c then hi' ≤ g x else g x ≤ lo')) :
    {x | lo ≤ f x ∧ f x ≤ hi} ∩ {x | lo' ≤ g x ∧ g x ≤ hi'} ⊆ K := by
  rw [pair_eq_preimage f g hcross lo hi lo' hi']
  apply ResearchFormalized.OrthantWitnesses.preimage_box_subset
    (pairCoordinates f g hcross).toLinearMap.toAffineMap
    (pairCoordinates f g hcross).injective hconv
  intro s
  obtain ⟨x, hx, hxf, hxg⟩ := hcorners (decide ((0 : Fin 2) ∈ s))
    (decide ((1 : Fin 2) ∈ s))
  refine ⟨x, hx, ?_⟩
  intro i
  fin_cases i
  · simpa [pairCoordinates_first] using hxf
  · simpa [pairCoordinates_second] using hxg

end Plank.PlanarPairContainment
