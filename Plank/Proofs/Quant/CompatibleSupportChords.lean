/- Actual original-width volume bound from compatible full support chords. -/
module

public import Plank.Convex.MonotoneVolume
public import Plank.Proofs.Quant.SelectableSupportChords

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.CompatibleSupportChords

open Set MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι]

/-- Full support spans identify the budget with the body's actual relative
widths. Arbitrary ordered windows, an empty family and exhausted budgets are allowed. -/
theorem uncovered_volume_lower_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K)
    (hspan : ∀i,f i (x i)-f i (y i)=Body.width K (f i))
    (hcompat : ∀i j,0≤f j (x i)-f j (y i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) (hW : ∀i,0<Body.width K (f i)) :
    (max 0 (1-∑i,(hi i-lo i)/Body.width K (f i)))^Module.finrank ℝ E*μ.real K≤
      μ.real (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  exact SelectableSupportChords.uncovered_volume_lower_bound μ hK hc f x y hx hy hspan
    (SideAssignments.stable_of_nonnegative _ (fun i j => hcompat j i)) lo hi ho hW

end Plank.CompatibleSupportChords
