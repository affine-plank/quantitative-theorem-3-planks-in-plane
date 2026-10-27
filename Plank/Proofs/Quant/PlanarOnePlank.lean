/- The sharp actual-area bound for one plank on any planar convex body. -/
module

public import Plank.Proofs.Quant.PlanarGapCells
public import Plank.Proofs.Quant.FiniteDimensionalOnePlank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnePlank

open Set MeasureTheory PlanarQuantitative PlanarGapCells
open Plank.Convex.DeficientHeightTilt
open scoped Pointwise

/-- A contracted copy of the body can be translated, piece by piece, outside
one plank. The two translations use actual support points of the body. -/
theorem uncovered_area_lower_bound {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (f : Point →ᵃ[ℝ] ℝ)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hW : 0 < rangeWidth K f) :
    (max 0 (1 - (hi-lo)/rangeWidth K f))^2 * (volume K).toReal ≤
      (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal := by
  simpa only [Module.finrank_pi,Fintype.card_fin,Body.width,rangeWidth] using
    FiniteDimensionalOnePlank.uncovered_volume_lower_bound volume hK hconv hne
      f lo hi hlo hW

/-- The exact final-statement interface for one plank, including lower-dimensional
bodies, zero-width planks, and windows extending outside the support interval. -/
theorem sharpPlanarBound_one : SharpPlanarBound 1 := by
  intro K hK hconv hne f lo hi hwidth hf
  have hset : (⋃ i : Fin 1, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) =
      {x | lo 0 ≤ f 0 x ∧ f 0 x ≤ hi 0} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨i, h⟩
      simpa only [Fin.eq_zero i] using h
    · intro h
      exact ⟨0, h⟩
  simpa only [Fin.sum_univ_one, hset] using
    uncovered_area_lower_bound hK hconv hne (f 0) (lo 0) (hi 0)
    (hwidth 0) (hf 0)

end Plank.PlanarOnePlank
