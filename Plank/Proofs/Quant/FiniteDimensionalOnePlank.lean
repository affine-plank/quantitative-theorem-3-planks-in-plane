/- The sharp actual-volume inequality for one affine plank in every finite
positive dimension, by piecewise translations of a contracted body. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalParallelPlanks

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalOnePlank

open Set MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A contracted copy of the body can be translated, piece by piece, outside
one plank. The two translations use actual support points of the body. -/
theorem uncovered_volume_lower_bound (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (f : E →ᵃ[ℝ] ℝ)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hW : 0 < Body.width K f) :
    (max 0 (1 - (hi-lo)/Body.width K f))^Module.finrank ℝ E * (μ K).toReal ≤
      (μ (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal := by
  simpa only [Fin.sum_univ_one,LinearBands.closedBand,iUnion_const] using
    FiniteDimensionalParallelPlanks.uncovered_volume_lower_bound μ hK hconv hne f
      (fun _ : Fin 1 => lo) (fun _ => hi) (fun _ => hlo) hW

end Plank.FiniteDimensionalOnePlank
