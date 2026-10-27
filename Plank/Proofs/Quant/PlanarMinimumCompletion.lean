/- A finite-family reduction: preceding quantitative bound, many-cell bound,
then qualitative covering. The first two inputs alone give cover completion. -/
module

public import Plank.Proofs.Quant.PlanarMinimumCellRank
public import Plank.Proofs.Quant.FiniteDimensionalMinimumCompletion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarMinimumCompletion

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt

/-- The geometric input needed only on configurations with many closed cells.
This is a hypothesis for arbitrary plank counts, not an asserted theorem. -/
def ManyCellBound {n : ℕ} (K : Set Point) (f : Fin n → Point →ᵃ[ℝ] ℝ) : Prop :=
  ∀ p ∈ interior (domain K f), budget K f p < 1 →
    2*n+1 ≤ (PlanarMinimumCellRank.nonemptyCells K f p).card →
    (1-budget K f p)^2*(volume K).toReal ≤ gapArea K f p

/-- Excluding the many-cell alternative produces an actual cover at no
greater root-gap cost. No covering theorem is used in this construction. -/
theorem exists_cover_of_counterexample {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) (hcell : ManyCellBound K f)
    (p₀ : Endpoints (m+1)) (hp₀ : p₀ ∈ domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2*(volume K).toReal) :
    ∃ p ∈ interior (domain K f),
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      budget K f p < 1 ∧
      budget K f p ≤ budget K f p₀+Real.sqrt (gapArea K f p₀/(volume K).toReal) := by
  simpa [FiniteDimensionalMinimumCellRank.gapRoot,Real.sqrt_eq_rpow,one_div,
    FiniteDimensionalParameterDomain.domain,domain,
    FiniteDimensionalFewCellScaling.budget,budget,
    FiniteDimensionalFewCellScaling.gapVolume,gapArea,rangeWidth,Body.width] using
    FiniteDimensionalMinimumCompletion.exists_cover_of_counterexample
      hm hK hc hne hV f hnorm hunit hcell p₀ hp₀ hbad

/-- The preceding quantitative bound and the many-cell bound complete every
normalized nonempty finite plank family in its existing directions. -/
theorem exists_cover_completion {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) (hcell : ManyCellBound K f)
    (p₀ : Endpoints (m+1)) (hp₀ : p₀ ∈ domain K f) :
    ∃ p ∈ domain K f,
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∧
      budget K f p ≤ budget K f p₀+Real.sqrt (gapArea K f p₀/(volume K).toReal) := by
  simpa [FiniteDimensionalMinimumCellRank.gapRoot,Real.sqrt_eq_rpow,one_div,
    FiniteDimensionalParameterDomain.domain,domain,
    FiniteDimensionalFewCellScaling.budget,budget,
    FiniteDimensionalFewCellScaling.gapVolume,gapArea,rangeWidth,Body.width] using
    FiniteDimensionalMinimumCompletion.exists_cover_completion
      hm hK hc hne hV f hnorm hunit hcell p₀ hp₀

/-- A covering bound is used only after quantitative cover completion.
Together with the preceding case and many-cell bound it proves this case. -/
theorem bound_normalized {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) (hcell : ManyCellBound K f)
    (hcover : ∀ p ∈ domain K f,
      K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} → 1 ≤ budget K f p)
    (p₀ : Endpoints (m+1)) (hp₀ : p₀ ∈ domain K f) :
    (max 0 (1-budget K f p₀))^2*(volume K).toReal ≤ gapArea K f p₀ := by
  exact FiniteDimensionalMinimumCompletion.bound_normalized
      hm hK hc hne hV f hnorm hunit hcell hcover p₀ hp₀

end Plank.PlanarMinimumCompletion

#print axioms Plank.PlanarMinimumCompletion.exists_cover_of_counterexample
#print axioms Plank.PlanarMinimumCompletion.exists_cover_completion
#print axioms Plank.PlanarMinimumCompletion.bound_normalized
