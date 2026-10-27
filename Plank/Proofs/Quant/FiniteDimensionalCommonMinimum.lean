/- Actual-width bounds for finitely many affine planks sharing a minimizing
body support point, in every finite positive dimension. -/
module

public import Plank.Proofs.AffineWidth
public import Plank.Measure.CommonMinimumVolume
public import Plank.Proofs.Quant.CompatibleSupportChords

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalCommonMinimum

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι]

/-- A common minimizing support point pays the sum of actual relative widths.
The directions need not be parallel; all ordered window positions are allowed. -/
theorem uncovered_volume_lower_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (z : E) (hz : z∈K)
    (hmin : ∀i x,x∈K → f i z≤f i x)
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (hW : ∀i,0<Body.width K (f i)) :
    (max 0 (1-∑i,(hi i-lo i)/Body.width K (f i)))^Module.finrank ℝ E*(μ K).toReal≤
      (μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i))).toReal := by
  classical
  have ht (i) : ∃a∈K,f i a-f i z=Body.width K (f i) := by
    obtain ⟨a,ha,b,hb,hmax,_⟩ := Body.exists_realisers hK ⟨z,hz⟩
      (f i).continuous_of_finiteDimensional
    exact ⟨a,ha,(Body.width_eq_of_realisers ha hz hmax (hmin i)).symm⟩
  choose a ha hspan using ht
  exact CompatibleSupportChords.uncovered_volume_lower_bound μ hK hc f a (fun _ => z)
    ha (fun _ => hz) hspan (fun i j => sub_nonneg.mpr (hmin j (a i) (ha i))) lo hi ho hW

end Plank.FiniteDimensionalCommonMinimum
