/- The sharp actual-width bound for every finite family of parallel affine
planks, by normalization of the common-minimum volume theorem. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCommonMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalParallelPlanks

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι]

/-- The common affine coordinate may define any finite number of planks.
Zero-width windows and empty indexed families are included. -/
theorem uncovered_volume_lower_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (hW : 0<Body.width K f) :
    (max 0 (1-∑i,(hi i-lo i)/Body.width K f))^Module.finrank ℝ E*(μ K).toReal≤
      (μ (K\⋃i,LinearBands.closedBand f (lo i) (hi i))).toReal := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne f.continuous_of_finiteDimensional
  exact FiniteDimensionalCommonMinimum.uncovered_volume_lower_bound μ hK hc
    (fun _ => f) b hb (fun _ => hmin) lo hi ho (fun _ => hW)

end Plank.FiniteDimensionalParallelPlanks
